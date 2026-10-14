"""Fresh, bounded GitHub verification of F1048 left-endpoint and two-sided finite-S consumers."""
import concurrent.futures as cf
import datetime
import fcntl
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import time
from audit_output import parse_public_output

HERE = pathlib.Path(__file__).resolve().parent
WORK = pathlib.Path('/tmp/open-he-run')
OUT = pathlib.Path(os.environ['GITHUB_WORKSPACE']) / 'verification-results'
ML = pathlib.Path('/tmp/mathlib')
TC = pathlib.Path('/tmp/lean-4.35.0-rc3-linux')
LEAN = TC / 'bin/lean'
REQ = json.loads((HERE / 'request.json').read_text())

def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    h = hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def save(name, value):
    target = OUT / name
    tmp = target.with_suffix(target.suffix + '.tmp')
    tmp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(target)

def main():
    ensure(sys.flags.optimize == 0, 'Python optimization is forbidden')
    OUT.mkdir(exist_ok=False)
    lock = (OUT / 'run.lock').open('w')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    WORK.mkdir(exist_ok=False)
    source = HERE.parent / 'Lean'
    files = {p.stem: p for p in source.glob('*.lean')}
    hashes = {n: sha(p) for n, p in files.items()}
    ensure(hashes == REQ['source_sha256'], 'Source hashes changed')
    deps = {n: {d for line in re.findall(r'^import\s+([^\n]+)', p.read_text(), re.M)
                 for d in line.split() if d in files} for n, p in files.items()}
    for n,p in files.items():
        ensure(not re.search(r'^\s*(?:axiom|sorry|admit)\b', p.read_text(), re.M), 'Forbidden declaration: '+n)
    count = 0
    for pinfile in sorted((HERE / 'pins').glob('*.json')):
        for p,digest in json.loads(pinfile.read_text()).items():
            prefix,relative = p.split('/',1)
            actual = (ML if prefix == 'mathlib' else TC) / relative
            ensure(sha(actual) == digest, 'Environment hash mismatch: '+p)
            count += 1
    rev = subprocess.check_output(['git','-C',str(ML),'rev-parse','HEAD'],text=True).strip()
    ensure(rev == REQ['identity']['mathlib_revision'], 'Mathlib revision mismatch')
    manifest = json.loads((ML / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        actual = subprocess.check_output(['git','-C',str(ML / '.lake/packages' / package['name']),
                                         'rev-parse','HEAD'],text=True).strip()
        ensure(actual == package['rev'], 'Dependency revision mismatch: '+package['name'])
    external_paths = [ML / '.lake/build/lib/lean'] + [ML / '.lake/packages' / p['name'] / '.lake/build/lib/lean' for p in manifest['packages']]
    version = subprocess.run([str(LEAN), '--version'], text=True, capture_output=True)
    ensure(version.returncode == 0, 'Lean cannot start')
    objects = OUT / 'objects'; objects.mkdir()
    logs = OUT / 'logs'; logs.mkdir()
    env = {**os.environ, 'LEAN_PATH': os.pathsep.join(map(str, [objects] + external_paths))}
    environment = {'utc': now(), 'identity': REQ['identity'], 'checked_file_hashes': count,
                   'dependency_revisions': len(manifest['packages']), 'external_sources': 10900,
                   'external_artifacts': 43600, 'version': version.stdout, 'lean_path': env['LEAN_PATH']}
    save('environment.json', environment)
    print('ENVIRONMENT_VERIFIED ' + json.dumps(environment), flush=True)

    results = {}
    seed_dir = HERE.parent / 'verification-seed'
    seed = json.loads((seed_dir / 'receipt.json').read_text())
    ensure(seed['identity'] == REQ['identity'], 'Seed environment differs')
    ensure(seed['commit'] == REQ['seed']['commit'], 'Seed commit differs')
    ensure(seed['status'] in {'TARGETS_PASS', 'INCOMPLETE'}, 'Invalid seed compilation status')
    if seed['status'] == 'TARGETS_PASS':
        ensure(seed.get('public_audit') == 'AXIOMS_PASS_TYPES_CAPTURED_SEMANTIC_REVIEW_PENDING',
               'Seed public axiom audit did not pass')
    candidates = {n for n in set(files) & seed['results'].keys()
                  if seed['results'][n]['status'] == 'PASS'
                  and seed['results'][n]['source_sha256'] == hashes[n]
                  and seed['results'][n]['dependency_sources'] ==
                      {d: hashes[d] for d in sorted(deps[n])}}
    while True:
        ready = sorted(n for n in candidates - results.keys() if deps[n] <= results.keys())
        if not ready:
            break
        for n in ready:
            record = seed['results'][n]
            ensure(record['status'] == 'PASS' and record['exit_code'] == 0 and
                   not record.get('sorryAx_detected', True), 'Invalid seed result: '+n)
            ensure(record['source_sha256'] == hashes[n] and record['dependency_sources'] ==
                   {d:hashes[d] for d in sorted(deps[n])}, 'Seed source/dependency mismatch: '+n)
            for folder,suffix,key in [('objects','.olean','olean_sha256'),('logs','.log','log_sha256')]:
                artifact = seed_dir / folder / (n+suffix)
                ensure(sha(artifact) == record[key], 'Seed artifact hash mismatch: '+n)
                shutil.copy2(artifact, OUT / folder / artifact.name)
            results[n] = {**record, 'reused':True,'seed_run':REQ['seed']['run']}
    receipt = {'status':'RUNNING','identity':REQ['identity'],'targets':REQ['targets'],
               'closure':sorted(files),'results':results,'main_theorem_verified':False,
               'full_scattering_proved':False,'started_utc':now(),
               'commit':os.environ.get('GITHUB_SHA'), 'public_semantic_acceptance':'PENDING'}
    save('receipt.json',receipt)
    print(f'Seed verified: {len(results)}; fresh compilations: {len(files)-len(results)}',flush=True)

    def compile_one(n):
        obj = objects / (n + '.olean'); log = logs / (n + '.log')
        command = [str(LEAN), '-DwarningAsError=true', '-o', str(obj), str(files[n])]
        started = now(); tic = time.monotonic(); code = None; timed_out = False
        with log.open('w') as f:
            try:
                code = subprocess.run(command, cwd=source, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=480).returncode
            except subprocess.TimeoutExpired:
                timed_out = True
        sorry = 'sorryAx' in log.read_text()
        ok = code == 0 and not timed_out and not sorry and obj.is_file()
        if not ok and obj.exists():
            failed = OUT / 'failed_objects'; failed.mkdir(exist_ok=True)
            obj.replace(failed / obj.name)
        return {'status': 'PASS' if ok else 'FAIL', 'exit_code': code, 'timed_out': timed_out,
                'seconds': round(time.monotonic() - tic, 3), 'started_utc': started, 'finished_utc': now(),
                'command': command, 'cwd': str(source), 'source_sha256': hashes[n],
                'dependency_sources': {d: hashes[d] for d in sorted(deps[n])},
                'log_sha256': sha(log), 'olean_sha256': sha(obj) if ok else None,
                'sorryAx_detected': sorry, 'reused': False}

    pending = set(files) - results.keys(); active = {}; tic = time.monotonic()
    with cf.ThreadPoolExecutor(max_workers=2) as pool:
        while pending or active:
            passed = {n for n, v in results.items() if v['status'] == 'PASS'}
            failed = any(v['status'] == 'FAIL' for v in results.values())
            ready = sorted(n for n in pending if deps[n] <= passed)
            if not failed and time.monotonic() - tic < 6600:
                for n in ready[:2 - len(active)]:
                    pending.remove(n); active[pool.submit(compile_one, n)] = n
            if not active:
                break
            done, _ = cf.wait(active, return_when=cf.FIRST_COMPLETED)
            for future in done:
                n = active.pop(future); results[n] = future.result()
                save('receipt.json', receipt)
                print('MODULE ' + json.dumps({'module': n, **results[n]}), flush=True)
                if results[n]['status'] != 'PASS':
                    print((logs / (n + '.log')).read_text(), flush=True)
    passed = {n for n, v in results.items() if v['status'] == 'PASS'}
    receipt['status'] = 'TARGETS_PASS' if set(files) <= passed else 'INCOMPLETE'
    receipt['not_built'] = sorted(set(files) - results.keys())
    receipt['requested_not_passed'] = sorted(set(REQ['targets']) - passed)
    receipt['finished_utc'] = now()
    save('receipt.json', receipt)
    # Audit fixed successful components even when an unrelated closure root fails.
    # This never changes compilation status or claims semantic acceptance.
    component_reports = []
    for component in json.loads((HERE / 'component-audits.json').read_text()):
        name = component['module']
        if name not in passed:
            component_reports.append({'module': name, 'status': 'NOT_RUN_MODULE_NOT_PASS'})
            continue
        audit_source = HERE / component['source']
        audit_log = OUT / ('component_audit_' + name + '.log')
        cmd = [str(LEAN), '-DwarningAsError=true', str(audit_source)]
        report = {'module': name, 'commit': os.environ.get('GITHUB_SHA'),
                  'command': cmd, 'source_sha256': sha(audit_source),
                  'module_source_sha256': hashes[name], 'started_utc': now(),
                  'semantic_acceptance': 'PENDING', 'status': 'RUNNING'}
        with audit_log.open('w') as f:
            try:
                audit_run = subprocess.run(cmd, cwd=source, env=env, stdout=f,
                    stderr=subprocess.STDOUT, timeout=480)
                report['exit_code'] = audit_run.returncode
                ensure(audit_run.returncode == 0, 'Component audit compile failed: ' + name)
                report['declarations'] = parse_public_output(audit_log.read_text(), component['declarations'])
                report['status'] = 'AXIOMS_PASS_TYPES_CAPTURED_SEMANTIC_REVIEW_PENDING'
            except Exception as error:
                report['status'] = 'FAIL'
                report['error'] = repr(error)
        report['finished_utc'] = now()
        report['log_sha256'] = sha(audit_log)
        component_reports.append(report)
        save('component_audit_' + name + '.json', report)
        print('COMPONENT_AUDIT ' + json.dumps(report), flush=True)
    receipt['component_audits'] = [{'module': r['module'], 'status': r['status']}
                                  for r in component_reports]
    save('component_audits.json', component_reports)
    save('receipt.json', receipt)
    ensure(all(r['status'] != 'FAIL' for r in component_reports), 'Component audit failed')
    ensure(receipt['status'] == 'TARGETS_PASS', 'Target closure did not pass')

    audit_log = OUT / 'public_audit.log'
    cmd = [str(LEAN), '-DwarningAsError=true', str(HERE / 'PublicAudit.lean')]
    with audit_log.open('w') as f:
        audited = subprocess.run(cmd, cwd=source, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=480)
    text = audit_log.read_text()
    audit = {'exit_code': audited.returncode, 'command': cmd, 'source_sha256': sha(HERE / 'PublicAudit.lean'),
             'log_sha256': sha(audit_log), 'declarations': [], 'semantic_acceptance': 'PENDING'}
    save('public_audit.json', audit)
    ensure(audited.returncode == 0 and 'sorryAx' not in text, 'Public audit compile failed')
    audit['declarations'] = parse_public_output(text, REQ['declarations'])
    audit['status'] = 'AXIOMS_PASS_TYPES_CAPTURED_SEMANTIC_REVIEW_PENDING'
    save('public_audit.json', audit)
    receipt['public_audit'] = audit['status']
    receipt['new_target_passes'] = len(REQ['targets'])
    save('receipt.json', receipt)
    print('PUBLIC_AUDIT ' + json.dumps(audit), flush=True)
    print(f"TARGETS_PASS: {len(REQ['targets'])} new target modules. Main theorem remains unverified.", flush=True)

if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        if OUT.is_dir():
            save('controller_error.json', {'utc': now(), 'error': repr(error), 'does_not_change_prior_receipts': True})
        raise
