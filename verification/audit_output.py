"""Parse real Lean #print axioms and #check output; never infer a compile pass."""
import hashlib
import re


def parse_public_output(text, declarations):
    if 'sorryAx' in text:
        raise ValueError('sorryAx in Lean output')
    starts = list(re.finditer(r'^@?([A-Za-z_][A-Za-z0-9_.]*)\s*:', text, re.M))
    types = {}
    expected_names = {d['name'] for d in declarations}
    for i, match in enumerate(starts):
        name = match.group(1)
        if name not in expected_names:
            continue
        if name in types:
            raise ValueError('Duplicate type output: ' + name)
        types[name] = text[match.start():starts[i + 1].start() if i + 1 < len(starts) else len(text)].strip()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    result = []
    for declaration in declarations:
        name = declaration['name']
        escaped = re.escape(name)
        matches = re.findall("'" + escaped + r"' depends on axioms: \[([^\]]*)\]", text)
        if matches:
            if len(matches) != 1:
                raise ValueError('Duplicate axiom output: ' + name)
            axioms = {a.strip() for a in matches[0].split(',') if a.strip()}
        else:
            if not re.search("'" + escaped + r"' does not depend on any axioms", text):
                raise ValueError('Missing axiom output: ' + name)
            axioms = set()
        if not axioms <= allowed:
            raise ValueError('Unapproved axiom: ' + name + ': ' + repr(axioms))
        if name not in types:
            raise ValueError('Missing type output: ' + name)
        actual_type = types[name]
        ordinary = sorted(set(re.findall(r'\bOrdinary[A-Za-z0-9_]+', actual_type)))
        if 'ordinary_inputs' in declaration and ordinary != declaration['ordinary_inputs']:
            raise ValueError('Ordinary-premise mismatch: ' + name)
        result.append({**declaration, 'axioms': sorted(axioms), 'actual_type': actual_type,
                       'actual_type_sha256': hashlib.sha256(actual_type.encode()).hexdigest(),
                       'ordinary_inputs_actual': ordinary})
    return result
