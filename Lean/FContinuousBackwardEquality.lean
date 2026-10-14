import FContinuousForwardEquality

set_option autoImplicit false
set_option warningAsError true
open Set
namespace HartreeF.CriticalUniqueness

/-- Equality propagates from the terminal value through left neighborhoods. -/
theorem continuous_eqOn_of_backward_local {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hb : f b = g b)
    (hlocal : ∀ r ∈ Ioc a b, f r = g r →
      ∃ d : ℝ, d < r ∧ EqOn f g (Icc d r)) : EqOn f g (Icc a b) := by
  have hrev : EqOn (fun t => f (-t)) (fun t => g (-t)) (Icc (-b) (-a)) := by
    apply continuous_eqOn_of_forward_local (hf.comp continuous_neg) (hg.comp continuous_neg)
    · simpa only [Function.comp_apply, neg_neg] using hb
    · intro r hr heq
      have hr' : -r ∈ Ioc a b := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      obtain ⟨d, hd, he⟩ := hlocal (-r) hr' heq
      refine ⟨-d, by linarith, ?_⟩
      intro s hs
      apply he
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  intro t ht
  have ht' : -t ∈ Icc (-b) (-a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [neg_neg] using hrev ht'

end HartreeF.CriticalUniqueness
