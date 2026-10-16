import FSpatialLpAverage
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
F-only static proof candidate. NOT COMPILED.
An L1∩Lp kernel convolved with a real L1 density has its literal Bochner
integral in Lp. Translation continuity gives an Lp-valued Bochner average;
finite-set integration CLMs and Fubini identify the same actual representative.
No unproved Young theorem and no local-domain premise is introduced.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution
namespace HartreeF.RieszL1LocalDomains
open ProfileSpatialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]

/-- Integration over a finite-measure measurable set, as a bounded map on Lp. -/
def finiteSetIntegralCLM (s : Set Space) (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) : Lp E p (volume : Measure Space) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume q p
    (indicatorConstLp q hs hμs (1 : ℝ))

theorem finiteSetIntegralCLM_apply (s : Set Space) (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (f : Lp E p (volume : Measure Space)) :
    finiteSetIntegralCLM (p := p) (q := q) s hs hμs f = ∫ x in s, f x := by
  rw [finiteSetIntegralCLM, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    (∫ x, (ContinuousLinearMap.lsmul ℝ ℝ)
        (indicatorConstLp q hs hμs (1 : ℝ) x) (f x)) =
        ∫ x, s.indicator (fun x => f x) x := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs)
        (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = ∫ x in s, f x := integral_indicator hs

/-- The literal scalar-density/vector-kernel convolution used throughout. -/
def actualConvolution (h : Space → ℝ) (k : Space → E) (x : Space) : E :=
  ∫ y, h y • k (x - y)

/-- Lp-valued Bochner integral, for identification only; not a substitute output. -/
def lpAverage (h : Space → ℝ) (k : Lp E p (volume : Measure Space)) :
    Lp E p (volume : Measure Space) := ∫ y : Space, h y • lpShift (-y) k

omit [CompleteSpace E] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p] in
theorem lpAverage_integrable (hp : p ≠ ∞) {h : Space → ℝ}
    (hh : Integrable h volume) (k : Lp E p (volume : Measure Space)) :
    Integrable (fun y : Space => h y • lpShift (-y) k) volume := by
  apply (hh.norm.mul_const ‖k‖).mono'
    (hh.aestronglyMeasurable.smul
      ((lpShift_continuous hp k).comp continuous_neg).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖h y • lpShift (-y) k‖ ≤ ‖h y‖ * ‖k‖
  rw [norm_smul, lpShift_norm]

include q in
/-- The actual representative of the Lp Bochner average is the literal integral.
The extra L1 kernel hypothesis is used only to justify global Fubini. -/
theorem lpAverage_coe_ae (hp : p ≠ ∞) {h : Space → ℝ} {k : Space → E}
    (hh : Integrable h volume) (hk1 : Integrable k volume) (hkp : MemLp k p volume) :
    (lpAverage h (hkp.toLp k) : Space → E) =ᵐ[volume] actualConvolution h k := by
  let K : Lp E p (volume : Measure Space) := hkp.toLp k
  let V : Lp E p (volume : Measure Space) := lpAverage h K
  have hJ : Integrable (fun z : Space × Space => h z.2 • k (z.1 - z.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      hh.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk1
  have hc1 : Integrable (actualConvolution h k) volume := hJ.integral_prod_left
  have hshift (y : Space) : (lpShift (-y) K : Space → E) =ᵐ[volume]
      (fun x => k (x - y)) := by
    refine (lpShift_coe_ae (-y) K).trans ?_
    filter_upwards [(measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae
      hkp.coeFn_toLp] with x hx
    simpa only [K, sub_eq_add_neg] using hx
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    let : Fact (volume s < ∞) := ⟨hμs⟩
    exact ((Lp.memLp V).restrict s).integrable (Fact.out : 1 ≤ p)
  · intro s hs hμs
    exact hc1.integrableOn
  · intro s hs hμs
    let T : Lp E p (volume : Measure Space) →L[ℝ] E :=
      finiteSetIntegralCLM (p := p) (q := q) s hs hμs.ne
    have hT (f : Lp E p (volume : Measure Space)) : T f = ∫ x in s, f x :=
      finiteSetIntegralCLM_apply (p := p) (q := q) s hs hμs.ne f
    have hJres : Integrable (fun z : Space × Space => h z.2 • k (z.1 - z.2))
        ((volume.restrict s).prod volume) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hJ.integrableOn
    calc
      (∫ x in s, V x) = T V := (hT V).symm
      _ = ∫ y, T (h y • lpShift (-y) K) :=
        (T.integral_comp_comm (lpAverage_integrable hp hh K)).symm
      _ = ∫ y, h y • ∫ x in s, k (x - y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [map_smul, hT]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hshift y))
      _ = ∫ y, ∫ x in s, h y • k (x - y) := by simp_rw [integral_smul]
      _ = ∫ x in s, actualConvolution h k x :=
        (integral_integral_swap hJres).symm

include q in
/-- Genuine L1→Lp Young membership for kernels that also belong to L1.
The output is the actual pointwise Bochner integral, not a freely chosen class. -/
theorem actualConvolution_memLp (hp : p ≠ ∞) {h : Space → ℝ} {k : Space → E}
    (hh : Integrable h volume) (hk1 : Integrable k volume) (hkp : MemLp k p volume) :
    MemLp (actualConvolution h k) p volume :=
  (Lp.memLp (lpAverage h (hkp.toLp k))).ae_eq
    (lpAverage_coe_ae (q := q) hp hh hk1 hkp)

end HartreeF.RieszL1LocalDomains
