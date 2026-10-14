import FCompactPDEInputDomain
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace

/-- A compact time test and its genuine derivative vanish off its stated test interval. -/
theorem timeTest_zero_outside {c d s : ℝ} (η : TimeTest)
    (hη : tsupport η ⊆ Set.Ioo c d) (hs : s ∉ Set.Icc c d) :
    η s = 0 ∧ deriv η s = 0 := by
  have hn : s ∉ tsupport η := fun h => hs ⟨(hη h).1.le, (hη h).2.le⟩
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn⟩

/-- Compact time support permits exact restriction of every scalar source pairing. -/
theorem timeTest_mul_integral_restrict {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    (η : TimeTest) (hη : tsupport η ⊆ Set.Ioo c d) (g : ℝ → ℂ) :
    (∫ s in Set.Icc a b, η s * g s) = ∫ s in Set.Icc c d, η s * g s := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Set.Icc_subset_Icc hac hdb)
  intro s hs
  rw [(timeTest_zero_outside η hη hs.2).1, zero_mul]

/-- The same support argument includes the derivative term in the actual weak operator. -/
theorem weakOperator_integral_restrict {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    (U : ℝ → TD) (η : TimeTest) (hη : tsupport η ⊆ Set.Ioo c d) (φ : Test) :
    (∫ s in Set.Icc a b, weakOperator U η φ s) =
      ∫ s in Set.Icc c d, weakOperator U η φ s := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Set.Icc_subset_Icc hac hdb)
  intro s hs
  have hz := timeTest_zero_outside η hη hs.2
  simp only [weakOperator, hz.1, hz.2, mul_zero, zero_mul, add_zero]

/-- A genuine compact distributional equation restricts to every smaller open interval. -/
theorem CompactTestIdentity.restrict {a b c d : ℝ} {U F : ℝ → TD}
    (h : CompactTestIdentity a b U F) (hac : a ≤ c) (hdb : d ≤ b) :
    CompactTestIdentity c d U F := by
  intro η hη φ hφ
  have hη' : tsupport η ⊆ Set.Ioo a b := fun s hs =>
    ⟨hac.trans_lt (hη hs).1, (hη hs).2.trans_le hdb⟩
  exact (weakOperator_integral_restrict hac hdb U η hη φ).symm.trans
    ((h η hη' φ hφ).trans (timeTest_mul_integral_restrict hac hdb η hη (fun s => F s φ)))

end HartreeF.LinearWeakEquation
