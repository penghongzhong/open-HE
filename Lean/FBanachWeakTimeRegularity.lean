import FBanachWeakDerivativeConstant

open Set Function MeasureTheory
open scoped Topology ContDiff

namespace BanachWeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous Banach-valued function with continuous weak time derivative
is classically differentiable at every point of its open time domain. The
weak identity is tested against actual scalar smooth compactly supported
functions, with their support contained in precisely that domain. -/
theorem hasDerivAt_of_weak_time_derivative
    {S : Set ℝ} (hS : IsOpen S) {f g : ℝ → E}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hweak : ∀ η : ℝ → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ S →
      (∫ s, deriv η s • f s) = -(∫ s, η s • g s))
    {t : ℝ} (ht : t ∈ S) :
    HasDerivAt f (g t) t := by
  obtain ⟨a, b, htU, hUS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  have hfU : ContinuousOn f (Ioo a b) := hf.mono hUS
  have hgU : ContinuousOn g (Ioo a b) := hg.mono hUS
  let H : ℝ → E := fun x ↦ ∫ y in t..x, g y
  have hH : ∀ x ∈ Ioo a b, HasDerivAt H (g x) x :=
    fun _ hx ↦ primitive_hasDerivAt hgU htU hx
  have hHcont : ContinuousOn H (Ioo a b) :=
    continuousOn_of_forall_continuousAt fun x hx ↦ (hH x hx).continuousAt
  have hzero : ∀ η : ℝ → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo a b →
      (∫ x, deriv η x • (f x - H x)) = 0 := by
    intro η hη hηc hηU
    have hiF : Integrable (fun x ↦ deriv η x • f x) :=
      integrable_test_smul hfU (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηU)
    have hiH : Integrable (fun x ↦ deriv η x • H x) :=
      integrable_test_smul hHcont (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηU)
    simp only [smul_sub]
    rw [integral_sub hiF hiH, hweak η hη hηc (hηU.trans hUS),
      integral_deriv_test_smul_primitive hgU hH hη hηc hηU, sub_self]
  obtain ⟨C, hC⟩ := eq_const_of_zero_weak_derivative (htU.1.trans htU.2)
    (hfU.sub hHcont) hzero
  have hmodel : HasDerivAt (fun x ↦ H x + C) (g t) t := (hH t htU).add_const C
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds htU] with x hx
  exact (sub_eq_iff_eq_add.mp (hC hx)).trans (add_comm C (H x))

end BanachWeakDerivative
