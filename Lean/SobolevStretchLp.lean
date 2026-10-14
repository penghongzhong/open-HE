import DirectionalStretchGeometry
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Actual finite-Lp pullback under the C9 directional linear equivalence.
The function amplitude is sqrt(l); the proposed real gradient is
sqrt(l) T_l(V(T_l x)). These are genuine function and Lp producers.
The distributional-gradient identification is proved in the next module.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch

def stretchedFunction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ω : Space) (l : ℝ) (u : Space → F) (x : Space) : F :=
  Real.sqrt l • u (stretch ω l x)

def stretchedGradient (ω : Space) (l : ℝ) (V : Space → Space) (x : Space) : Space :=
  Real.sqrt l • stretch ω l (V (stretch ω l x))

theorem stretch_memLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    {u : Space → F} (hu : MemLp u p volume) :
    MemLp (fun x => u (stretch ω l x)) p volume := by
  have hq := Measure.ContinuousLinearMap.quasiMeasurePreserving volume (stretch ω l) (by rw [stretch_det hω]; exact hl.ne')
  have hm := hu.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  apply (integrable_norm_rpow_iff hm hp0 hpt).1
  exact (stretch_integrable_iff hω hl (fun y => ‖u y‖^p.toReal)).2
    ((integrable_norm_rpow_iff hu.aestronglyMeasurable hp0 hpt).2 hu)

theorem stretchedFunction_memLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    {u : Space → F} (hu : MemLp u p volume) :
    MemLp (stretchedFunction ω l u) p volume :=
  (stretch_memLp hω hl hp0 hpt hu).const_smul _

theorem stretchedGradient_memLp {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) {V : Space → Space} (hV : MemLp V 2 volume) :
    MemLp (stretchedGradient ω l V) 2 volume := by
  exact ((stretch ω l).comp_memLp' (stretch_memLp hω hl (by norm_num) (by norm_num) hV)).const_smul (Real.sqrt l)

/-- Compact test products are actual L1 functions, so the weak identity is
not an equality of default nonintegrable Bochner integrals. -/
theorem weak_test_integrable {u : Space → ℝ} {V : Space → Space}
    (hu : LocallyIntegrable u volume) (hV : LocallyIntegrable V volume)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (v : Space) :
    Integrable (fun x => u x * fderiv ℝ φ x v) volume ∧
    Integrable (fun x => ⟪V x,v⟫ * φ x) volume := by
  have hd : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  constructor
  · simpa only [smul_eq_mul] using
      hu.integrable_smul_right_of_hasCompactSupport hd (hc.fderiv_apply ℝ v)
  · have hi : LocallyIntegrable (fun x => ⟪V x,v⟫) volume := by
      rw [show (fun x => ⟪V x,v⟫) = (innerSL ℝ v) ∘ V by funext x; exact real_inner_comm _ _]
      exact
        locallyIntegrableOn_univ.mp ((innerSL ℝ v).locallyIntegrableOn_comp (hV.locallyIntegrableOn univ))
    simpa only [smul_eq_mul] using
      hi.integrable_smul_right_of_hasCompactSupport hφ.continuous hc

#print axioms stretch_memLp
#print axioms stretchedFunction_memLp
#print axioms stretchedGradient_memLp
#print axioms weak_test_integrable
end HartreeF.SobolevStretch
