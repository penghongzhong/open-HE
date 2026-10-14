import FR2ActualTailForcing

/-! Actual full residual domains, before selection or numerical smallness.
All new declarations are static author source and remain UNCOMPILED.
The candidates are genuine first weak gradients of the canonical scalar residual. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FullResidual
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ForcingDomain
  DerivativeMajorization WeakHartreeProduct CriticalTimeSobolev ProfileApproximation
  GeneralProfileCross FiniteProfileWeakGradient FreeValueGradient R2Global R2TailForcing

variable {ι : Type*} [DecidableEq ι]

/-- Zero is simplified in the explicit candidate, using the CLM's map_zero.
No pointwise statement about the totalized raw derivative is used. -/
@[simp] theorem directionalCandidate_zero (α c : ℝ) :
    directionalCandidate α c (0 : Space → ℂ) 0 = 0 := by
  funext x
  simp only [directionalCandidate, Pi.zero_apply, WeakHartreeChain.localFactor,
    smul_zero, map_zero, add_zero]

@[simp] theorem candidateFullGradient_zero (α c : ℝ) :
    candidateFullGradient α c (0 : Space → ℂ) 0 0 = 0 := by
  have hd (j : Fin 3) : directionalField (0 : Space → Space) 0
      (EuclideanSpace.basisFun (Fin 3) ℝ j) = 0 := by
    funext x
    simp [directionalField]
  funext x
  simp only [candidateFullGradient, hd, directionalCandidate_zero, Pi.zero_apply,
    packGradient, zero_smul, zero_add]

/-- sourceCandidate retains the zero-state subtraction in its definition;
this explicit algebra is the justified simplification. -/
theorem sourceCandidate_eq_full {q : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume q) :
    sourceCandidate α c r = fun t => candidateFullGradient α c (r.u t) (r.U t) (r.V t) := by
  funext t x
  rw [sourceCandidate, candidateGradient_eq_candidates]
  simp only [zero_add, Pi.zero_apply, candidateFullGradient_zero, sub_zero]

/-- Any two chosen joint fields of the same canonical curve have the same
candidate class. It is candidate congruence, not raw derivative congruence. -/
theorem sourceCandidate_congr {q : ℝ → EnergyState} (α c : ℝ)
    (r s : EnergyJointFields volume q) :
    ∀ᵐ t ∂volume, sourceCandidate α c r t =ᵐ[volume] sourceCandidate α c s t := by
  rw [sourceCandidate_eq_full, sourceCandidate_eq_full]
  filter_upwards [r.slice_eq, s.slice_eq] with t hr hs
  exact candidateFullGradient_congr_ae α c (hr.1.trans hs.1.symm)
    (hr.2.1.trans hs.2.1.symm) (hr.2.2.trans hs.2.2.symm)

/-- This also covers normalized fields transported through frameJointFields:
pointwise equality of EnergyState curves is established before transport. -/
theorem sourceCandidate_congr_curve {q v : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume q) (s : EnergyJointFields volume v) (h : q = v) :
    ∀ᵐ t ∂volume, sourceCandidate α c r t =ᵐ[volume] sourceCandidate α c s t := by
  subst v
  exact sourceCandidate_congr α c r s

def literalResidual (s : Finset ι) (α c : ℝ) (q : ℝ → EnergyState)
    (p : ι → ℝ → EnergyState) : ℝ → Space → ℂ :=
  fun t x => forcing α c (energyValue (q t)) x -
    ∑ j ∈ s, forcing α c (energyValue (p j t)) x

def residualCandidate (s : Finset ι) (α c : ℝ) {q : ℝ → EnergyState}
    {p : ι → ℝ → EnergyState} (rq : EnergyJointFields volume q)
    (rp : ∀ j, EnergyJointFields volume (p j)) : ℝ → Space → CGradient :=
  fun t x => sourceCandidate α c rq t x - ∑ j ∈ s, sourceCandidate α c (rp j) t x

def residualActual (s : Finset ι) (α c : ℝ) {q : ℝ → EnergyState}
    {p : ι → ℝ → EnergyState} (rq : EnergyJointFields volume q)
    (rp : ∀ j, EnergyJointFields volume (p j)) : ℝ → Space → CGradient :=
  fun t x => sourceGradient α c rq t x - ∑ j ∈ s, sourceGradient α c (rp j) t x

/-- Canonical scalar coupling follows from the actual producer and scalar AE
transport, with all weak-test integrability inherited from that producer. -/
theorem source_candidate_canonical_weak (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    {q : ℝ → EnergyState} (hq : CurveFinite q) (rq : EnergyJointFields volume q) :
    ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (forcing α c (energyValue (q t)) x).re)
        (fun x => gradientReal (sourceCandidate α c rq t x)) ∧
      HasWeakGradient (fun x => (forcing α c (energyValue (q t)) x).im)
        (fun x => gradientImag (sourceCandidate α c rq t x)) := by
  have hd := source_domains hDensity hSob hH hq rq
  filter_upwards [hd.candidate_weak, source_scalar_canonical_ae α c rq] with t hw he
  exact ⟨weakGradient_congr_fields hw.1 (he.mono fun _ hx => congrArg Complex.re hx)
      Filter.EventuallyEq.rfl,
    weakGradient_congr_fields hw.2 (he.mono fun _ hx => congrArg Complex.im hx)
      Filter.EventuallyEq.rfl⟩

omit [DecidableEq ι] in
private theorem gradientReal_sub_sum (s : Finset ι) (a : CGradient) (b : ι → CGradient) :
    gradientReal (a - ∑ j ∈ s, b j) = gradientReal a - ∑ j ∈ s, gradientReal (b j) := by
  ext k
  simp [gradientReal]

omit [DecidableEq ι] in
private theorem gradientImag_sub_sum (s : Finset ι) (a : CGradient) (b : ι → CGradient) :
    gradientImag (a - ∑ j ∈ s, b j) = gradientImag a - ∑ j ∈ s, gradientImag (b j) := by
  ext k
  simp [gradientImag]

private theorem residual_finite_joint_sum {E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → Space → E)
    (h : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => f i z.1 z.2)
      (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => ∑ i ∈ s, f i z.1 z.2)
      (volume.prod volume) := by
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simpa using (aestronglyMeasurable_const (b := (0 : E)))
  | @insert a s ha ih =>
      intro h
      simpa only [Finset.sum_insert ha, Pi.add_apply] using
        (h a (Finset.mem_insert_self a s)).add
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Triangle is used on jointly measurable candidates only. -/
theorem vectorForcingNorm_sub_le (G H : ℝ → Space → CGradient)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume)) :
    vectorForcingNorm (fun t x => G t x - H t x) ≤ vectorForcingNorm G + vectorForcingNorm H := by
  have hn : vectorForcingNorm (fun t x => -H t x) = vectorForcingNorm H := by
    unfold vectorForcingNorm mixedNorm
    congr 1
    funext t
    change eLpNorm (-(H t)) (ENNReal.ofReal (6/5 : ℝ)) volume =
      eLpNorm (H t) (ENNReal.ofReal (6/5 : ℝ)) volume
    exact eLpNorm_neg (H t) (ENNReal.ofReal (6/5 : ℝ)) volume
  calc
    _ = vectorForcingNorm (fun t x => G t x + -H t x) := by simp only [sub_eq_add_neg]
    _ ≤ vectorForcingNorm G + vectorForcingNorm (fun t x => -H t x) :=
      mixed_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6/5 : ℝ))
        ENNReal.ofReal_ne_top G (fun t x => -H t x) hG hH.neg
    _ = _ := congrArg (fun a => vectorForcingNorm G+a) hn

structure ActualResidualDomains (s : Finset ι) (α c : ℝ) (q : ℝ → EnergyState)
    (p : ι → ℝ → EnergyState) (rq : EnergyJointFields volume q)
    (rp : ∀ j, EnergyJointFields volume (p j)) : Prop where
  candidate_joint : AEStronglyMeasurable
    (fun z : ℝ × Space => residualCandidate s α c rq rp z.1 z.2) (volume.prod volume)
  actual_ae_candidate : ∀ᵐ t ∂volume,
    residualActual s α c rq rp t =ᵐ[volume] residualCandidate s α c rq rp t
  candidate_finite : vectorForcingNorm (residualCandidate s α c rq rp) ≠ ∞
  actual_finite : vectorForcingNorm (residualActual s α c rq rp) ≠ ∞
  candidate_slice : ∀ᵐ t ∂volume,
    MemLp (residualCandidate s α c rq rp t) (ENNReal.ofReal (6/5 : ℝ)) volume
  candidate_weak : ∀ᵐ t ∂volume,
    HasWeakGradient (fun x => (literalResidual s α c q p t x).re)
      (fun x => gradientReal (residualCandidate s α c rq rp t x)) ∧
    HasWeakGradient (fun x => (literalResidual s α c q p t x).im)
      (fun x => gradientImag (residualCandidate s α c rq rp t x))
  candidate_tests : ∀ᵐ t ∂volume,
    CoordinateTests (literalResidual s α c q p t) (residualCandidate s α c rq rp t)

/-- Generic every-index packet. In the application q is the augmented curve
and s is range J (or univ : Finset (Fin J)); no eventual cap is needed. -/
theorem actual_residual_domains (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (q : ℝ → EnergyState) (p : ι → ℝ → EnergyState)
    (hq : CurveFinite q) (hp : ∀ j ∈ s, CurveFinite (p j))
    (rq : EnergyJointFields volume q) (rp : ∀ j, EnergyJointFields volume (p j)) :
    ActualResidualDomains s α c q p rq rp := by
  have hqD := source_domains hDensity hSob hH hq rq
  have hpD (j : ι) (hj : j ∈ s) := source_domains hDensity hSob hH (hp j hj) (rp j)
  have hsumJ := residual_finite_joint_sum s (fun j => sourceCandidate α c (rp j))
    (fun j hj => (hpD j hj).candidate_joint)
  have hJ : AEStronglyMeasurable
      (fun z : ℝ × Space => residualCandidate s α c rq rp z.1 z.2) (volume.prod volume) :=
    hqD.candidate_joint.sub hsumJ
  have hsumF : vectorForcingNorm
      (fun t x => ∑ j ∈ s, sourceCandidate α c (rp j) t x) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.sum_ne_top.mpr (fun j hj => (hpD j hj).candidate_finite))
    exact FiniteProfileMixedDefects.mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) _
      (fun j hj => (hpD j hj).candidate_joint)
  have hF : vectorForcingNorm (residualCandidate s α c rq rp) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hqD.candidate_finite, hsumF⟩)
      (vectorForcingNorm_sub_le _ _ hqD.candidate_joint hsumJ)
  have hAE : ∀ᵐ t ∂volume,
      residualActual s α c rq rp t =ᵐ[volume] residualCandidate s α c rq rp t := by
    filter_upwards [hqD.actual_ae_candidate,
      (eventually_all_finset s).2 (fun j hj => (hpD j hj).actual_ae_candidate)] with t ht hp'
    filter_upwards [ht, (eventually_all_finset s).2 hp'] with x hx hpx
    exact congrArg₂ (· - ·) hx (Finset.sum_congr rfl hpx)
  have hW : ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (literalResidual s α c q p t x).re)
        (fun x => gradientReal (residualCandidate s α c rq rp t x)) ∧
      HasWeakGradient (fun x => (literalResidual s α c q p t x).im)
        (fun x => gradientImag (residualCandidate s α c rq rp t x)) := by
    filter_upwards [source_candidate_canonical_weak hDensity hSob hH hq rq,
      (eventually_all_finset s).2 (fun j hj =>
        source_candidate_canonical_weak hDensity hSob hH (hp j hj) (rp j))] with t hqW hpW
    constructor
    · simpa only [literalResidual, residualCandidate, Complex.sub_re, Complex.re_sum,
        gradientReal_sub_sum] using TimeHolder.weakGradient_sub hqW.1
          (weakGradient_sum s (fun j x => (forcing α c (energyValue (p j t)) x).re)
            (fun j x => gradientReal (sourceCandidate α c (rp j) t x))
            (fun j hj => (hpW j hj).1))
    · simpa only [literalResidual, residualCandidate, Complex.sub_im, Complex.im_sum,
        gradientImag_sub_sum] using TimeHolder.weakGradient_sub hqW.2
          (weakGradient_sum s (fun j x => (forcing α c (energyValue (p j t)) x).im)
            (fun j x => gradientImag (sourceCandidate α c (rp j) t x))
            (fun j hj => (hpW j hj).2))
  refine ⟨hJ, hAE, hF, ?_, ?_, hW, ?_⟩
  · have he := mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) hAE
    exact fun htop => hF (he.symm.trans htop)
  · exact finite_mixedNorm_ae_slice_memLp volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (by norm_num) (by norm_num) _ hF
  · exact hW.mono fun _ ht => weakGradients_coordinate_tests ht.1 ht.2

/-- The retained actual residual has the same canonical weak derivative.
Only the supplied nested actual-to-candidate equality is used. -/
omit [DecidableEq ι] in
theorem ActualResidualDomains.actual_weak
    {s : Finset ι} {α c : ℝ} {q : ℝ → EnergyState} {p : ι → ℝ → EnergyState}
    {rq : EnergyJointFields volume q} {rp : ∀ j, EnergyJointFields volume (p j)}
    (h : ActualResidualDomains s α c q p rq rp) :
    ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (literalResidual s α c q p t x).re)
        (fun x => gradientReal (residualActual s α c rq rp t x)) ∧
      HasWeakGradient (fun x => (literalResidual s α c q p t x).im)
        (fun x => gradientImag (residualActual s α c rq rp t x)) := by
  filter_upwards [h.candidate_weak, h.actual_ae_candidate] with t hw he
  exact ⟨weakGradient_congr_gradient hw.1 (he.symm.mono fun _ hx => congrArg gradientReal hx),
    weakGradient_congr_gradient hw.2 (he.symm.mono fun _ hx => congrArg gradientImag hx)⟩

omit [DecidableEq ι] in
theorem ActualResidualDomains.actual_slice
    {s : Finset ι} {α c : ℝ} {q : ℝ → EnergyState} {p : ι → ℝ → EnergyState}
    {rq : EnergyJointFields volume q} {rp : ∀ j, EnergyJointFields volume (p j)}
    (h : ActualResidualDomains s α c q p rq rp) :
    ∀ᵐ t ∂volume,
      MemLp (residualActual s α c rq rp t) (ENNReal.ofReal (6/5:ℝ)) volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 2 (ENNReal.ofReal (6/5:ℝ))
    (by norm_num) (by norm_num) _ h.actual_finite

omit [DecidableEq ι] in
theorem ActualResidualDomains.actual_tests
    {s : Finset ι} {α c : ℝ} {q : ℝ → EnergyState} {p : ι → ℝ → EnergyState}
    {rq : EnergyJointFields volume q} {rp : ∀ j, EnergyJointFields volume (p j)}
    (h : ActualResidualDomains s α c q p rq rp) :
    ∀ᵐ t ∂volume, CoordinateTests (literalResidual s α c q p t) (residualActual s α c rq rp t) :=
  h.actual_weak.mono fun _ ht => weakGradients_coordinate_tests ht.1 ht.2

/-- Independence of all chosen compatible representatives, including a framed
normalized choice versus the joint fields chosen for the physical curve. -/
omit [DecidableEq ι] in
theorem residualCandidate_congr (s : Finset ι) (α c : ℝ)
    {q : ℝ → EnergyState} {p : ι → ℝ → EnergyState}
    (rq sq : EnergyJointFields volume q)
    (rp sp : ∀ j, EnergyJointFields volume (p j)) :
    ∀ᵐ t ∂volume, residualCandidate s α c rq rp t =ᵐ[volume]
      residualCandidate s α c sq sp t := by
  filter_upwards [sourceCandidate_congr α c rq sq,
    (eventually_all_finset s).2 (fun j _ => sourceCandidate_congr α c (rp j) (sp j))]
    with t hq hp
  filter_upwards [hq, (eventually_all_finset s).2 hp] with x hx hpx
  exact congrArg₂ (· - ·) hx (Finset.sum_congr rfl hpx)

end HartreeF.FullResidual
