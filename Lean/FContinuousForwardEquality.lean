import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option warningAsError true
open Set Filter
open scoped Topology
namespace HartreeF.CriticalUniqueness

/-- Equality of continuous paths propagates through a closed interval when
agreement at each internal time produces agreement on a right neighborhood. -/
theorem continuous_eqOn_of_forward_local {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (ha : f a = g a)
    (hlocal : ∀ r ∈ Ico a b, f r = g r →
      ∃ d : ℝ, r < d ∧ EqOn f g (Icc r d)) : EqOn f g (Icc a b) := by
  let S : Set ℝ := {t | f t = g t}
  have hclosed : IsClosed (S ∩ Icc a b) := (isClosed_eq hf hg).inter isClosed_Icc
  apply hclosed.Icc_subset_of_forall_mem_nhdsWithin ha
  intro r hr
  obtain ⟨d, hrd, hd⟩ := hlocal r hr.2 hr.1
  exact mem_of_superset (Ioo_mem_nhdsGT hrd) (fun s hs => hd ⟨hs.1.le, hs.2.le⟩)

end HartreeF.CriticalUniqueness
