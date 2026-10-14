import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

open Set Function MeasureTheory
open scoped Topology ContDiff

namespace BanachWeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar compact test times a function continuous only on the test domain
is integrable on the whole line. The ambient function need not be measurable
or continuous outside that domain. -/
theorem integrable_test_smul {u : ℝ → E} {S : Set ℝ} {η : ℝ → ℝ}
    (hu : ContinuousOn u S) (hη : Continuous η)
    (hηc : HasCompactSupport η) (hηS : tsupport η ⊆ S) :
    Integrable (fun x ↦ η x • u x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((support_smul_subset_left η u).trans (subset_tsupport η))).mp
  exact (hη.continuousOn.smul (hu.mono hηS)).integrableOn_compact hηc

/-- The only new analytic ingredient needed in the primitive/distribution
route: a zero-integral smooth test on an interval has a smooth primitive
with compact support inside that same interval. -/
theorem exists_compact_test_primitive {a b : ℝ} {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hqS : tsupport q ⊆ Ioo a b) (hqint : ∫ x, q x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ∧ ∀ x, HasDerivAt ψ (q x) x := by
  rcases (tsupport q).eq_empty_or_nonempty with hzero | hne
  · have hqzero : q = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (by simp [hzero])
    refine ⟨0, contDiff_const, ?_, ?_, ?_⟩
    · simp [HasCompactSupport]
    · simp
    · intro x
      simp [hqzero]
  obtain ⟨m, hm⟩ := hqc.isCompact.exists_isLeast hne
  obtain ⟨M, hM⟩ := hqc.isCompact.exists_isGreatest hne
  let c : ℝ := (a + m) / 2
  let d : ℝ := (M + b) / 2
  have hac : a < c := by dsimp [c]; linarith [(hqS hm.1).1]
  have hcm : c < m := by dsimp [c]; linarith [(hqS hm.1).1]
  have hMd : M < d := by dsimp [d]; linarith [(hqS hM.1).2]
  have hdb : d < b := by dsimp [d]; linarith [(hqS hM.1).2]
  have hqbox : support q ⊆ Ioc c d := by
    intro x hx
    have hxK := subset_tsupport q hx
    exact ⟨hcm.trans_le (hm.2 hxK), (hM.2 hxK).trans hMd.le⟩
  let ψ : ℝ → ℝ := fun x ↦ ∫ y in c..x, q y
  have hψderiv : ∀ x, HasDerivAt ψ (q x) x := by
    intro x
    exact (hq.continuous.integral_hasStrictDerivAt c x).hasDerivAt
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x ↦ (hψderiv x).differentiableAt, ?_⟩
    have hderiv : deriv ψ = q := funext fun x ↦ (hψderiv x).deriv
    rw [hderiv]
    exact hq
  have hψzero : ∀ x, x ∉ Icc c d → ψ x = 0 := by
    intro x hx
    by_cases hxc : x < c
    · change (∫ y in c..x, q y) = 0
      rw [intervalIntegral.integral_symm]
      have hz : (∫ y in x..c, q y) = 0 := by
        calc
          (∫ y in x..c, q y) = ∫ y in x..c, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hyc : y ≤ c := by
              have hy' : y ∈ Icc x c := by
                simpa only [uIcc_of_le hxc.le] using hy
              exact hy'.2
            by_contra hyzero
            have hmy : m ≤ y := hm.2 (subset_tsupport q hyzero)
            linarith
          _ = 0 := by simp
      rw [hz, neg_zero]
    · have hdx : d < x := by
        by_contra h
        exact hx ⟨le_of_not_gt hxc, le_of_not_gt h⟩
      change (∫ y in c..x, q y) = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset
        (fun y hy ↦ ⟨(hqbox hy).1, (hqbox hy).2.trans hdx.le⟩), hqint]
  have hψsupp : tsupport ψ ⊆ Icc c d :=
    closure_minimal (support_subset_iff'.mpr hψzero) isClosed_Icc
  refine ⟨ψ, hψsmooth, HasCompactSupport.intro isCompact_Icc hψzero, ?_, hψderiv⟩
  exact hψsupp.trans fun x hx ↦ ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩

/-- Local FTC for a primitive based at an interior point.
No continuity outside the interval is needed. -/
theorem primitive_hasDerivAt [CompleteSpace E] {a b c : ℝ} {g : ℝ → E}
    (hg : ContinuousOn g (Ioo a b)) (hc : c ∈ Ioo a b)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun z ↦ ∫ y in c..z, g y) (g x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hg.mono (ordConnected_Ioo.uIcc_subset hc hx)).intervalIntegrable
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hg x hx
  · exact hg.continuousAt (isOpen_Ioo.mem_nhds hx)

/-- Whole-line integration by parts with an actual scalar time test and a
locally defined primitive. Here hH is established by primitive_hasDerivAt;
it is not a hypothesis about the unknown weakly differentiable f.
 -/
theorem integral_deriv_test_smul_primitive {S : Set ℝ} {g H : ℝ → E}
    (hg : ContinuousOn g S) (hH : ∀ x ∈ S, HasDerivAt H (g x) x)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ S) :
    (∫ x, deriv η x • H x) = -(∫ x, η x • g x) := by
  have hHcont : ContinuousOn H S :=
    continuousOn_of_forall_continuousAt fun x hx ↦ (hH x hx).continuousAt
  have hη' : Continuous (deriv η) := hη.continuous_deriv (by simp)
  have hparts := MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := η) (u' := deriv η) (v := H) (v' := g)
    (fun x _ ↦ (hη.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun x hx ↦ hH x (hηS hx))
    (integrable_test_smul hg hη.continuous hηc hηS)
    (integrable_test_smul hHcont hη' hηc.deriv (tsupport_deriv_subset.trans hηS))
    (integrable_test_smul hHcont hη.continuous hηc hηS)
  simpa only [ContinuousLinearMap.lsmul_apply, neg_neg] using
    (congrArg (fun v : E ↦ -v) hparts).symm

end BanachWeakDerivative
