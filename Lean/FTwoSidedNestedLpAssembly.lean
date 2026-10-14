import FCompactLpExhaustion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion

/-- The two zero-extended half-interval representatives assemble into one
actual global nested-Lp representative. Their common center is a null singleton;
this remains valid when the whole interval is a singleton. -/
theorem exists_global_nestedLp_of_two_halves
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (I : Set ℝ) (hI : MeasurableSet I) (s : ℝ) (g : ℝ → X → E) (CL CR : ℝ)
    (FL FR : Lp (Lp E r ν) p (volume : Measure ℝ))
    (hL : ‖FL‖ ≤ CL) (hR : ‖FR‖ ≤ CR)
    (hLa : ∀ᵐ t ∂volume.restrict (I ∩ Iic s), (FL t : X → E) =ᵐ[ν] g t)
    (hRa : ∀ᵐ t ∂volume.restrict (I ∩ Ici s), (FR t : X → E) =ᵐ[ν] g t)
    (hLz : ∀ᵐ t ∂volume, t ∉ I ∩ Iic s → FL t=0)
    (hRz : ∀ᵐ t ∂volume, t ∉ I ∩ Ici s → FR t=0) :
    ∃ F : Lp (Lp E r ν) p (volume : Measure ℝ), ‖F‖ ≤ CL+CR ∧
      (∀ᵐ t ∂volume.restrict I, (F t : X → E) =ᵐ[ν] g t) ∧
      (∀ᵐ t ∂volume, t ∉ I → F t=0) := by
  have hLa' := (ae_restrict_iff' (hI.inter measurableSet_Iic)).mp hLa
  have hRa' := (ae_restrict_iff' (hI.inter measurableSet_Ici)).mp hRa
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton s : (volume : Measure ℝ) {s}=0)
  refine ⟨FL+FR,(norm_add_le _ _).trans (add_le_add hL hR),?_,?_⟩
  · apply (ae_restrict_iff' hI).mpr
    filter_upwards [Lp.coeFn_add FL FR,hLa',hRa',hLz,hRz,hne] with t ht hl hr hlz hrz hn
    intro hti
    by_cases hts : t ≤ s
    · have hnot : t ∉ I ∩ Ici s := fun h => hn (le_antisymm hts h.2)
      have heq : (FL+FR) t=FL t := by simpa only [Pi.add_apply,hrz hnot,add_zero] using ht
      rw [heq]
      exact hl ⟨hti,hts⟩
    · have hnot : t ∉ I ∩ Iic s := fun h => hts h.2
      have heq : (FL+FR) t=FR t := by simpa only [Pi.add_apply,hlz hnot,zero_add] using ht
      rw [heq]
      exact hr ⟨hti,le_of_not_ge hts⟩
  · filter_upwards [Lp.coeFn_add FL FR,hLz,hRz] with t ht hlz hrz
    intro hti
    have hl : FL t=0 := hlz (fun h => hti h.1)
    have hr : FR t=0 := hrz (fun h => hti h.1)
    simpa only [Pi.add_apply,hl,hr,zero_add] using ht

#print axioms exists_global_nestedLp_of_two_halves
end HartreeF.IntervalNormExhaustion
