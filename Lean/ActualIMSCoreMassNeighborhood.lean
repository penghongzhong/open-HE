import CompactIMSErrorIntegral

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

/-- The actual cosine-core mass has a uniform positive lower bound throughout a fixed
L6 × L2 × L2 neighborhood of a compact nonzero homogeneous family. -/
theorem compact_actual_core_mass_neighborhood {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K))
    (hnonzero : ∀ f ∈ K, ¬ (f.u =ᵐ[volume] 0)) :
    ∃ N : ℕ, ∃ m > 0, ∃ δ > 0, ∀ n ≥ N, ∀ f ∈ K, ∀ g : HomogeneousData,
      dist g.lpData f.lpData < δ → m ≤ ∫ x, ‖core (cutoffAngle n) g.u x‖^2 := by
  have hL6 := hK.image continuous_fst
  have hz : (0 : Lp ℂ 6 (volume : Measure Space)) ∉ Prod.fst '' (HomogeneousData.lpData '' K) := by
    rintro ⟨v, ⟨f, hf, rfl⟩, hv⟩
    have hzero : f.domain.function_L6.toLp f.u = 0 := hv
    have hae := Lp.eq_zero_iff_ae_eq_zero.mp hzero
    exact hnonzero f hf (f.domain.function_L6.coeFn_toLp.symm.trans hae)
  obtain ⟨N, m, hm, δ, hδ, hmass⟩ := compact_nonzero_local_mass_neighborhood hL6 hz
  refine ⟨N, m, hm, δ, hδ, ?_⟩
  intro n hn f hf g hgf
  have hdist : dist g.lpData.1 f.lpData.1 < δ := by
    rw [Prod.dist_eq] at hgf
    exact (max_lt_iff.mp hgf).1
  have hh := hmass f.lpData.1 (mem_image_of_mem _ (mem_image_of_mem _ hf)) g.lpData.1 hdist
  have hh' : m ≤ ∫ x in localBall N, ‖g.u x‖^2 := by
    simpa only [HomogeneousData.lpData, localBall_toLp_mass_eq] using hh
  exact hh'.trans (local_mass_le_core_mass g.domain hn)

#print axioms compact_actual_core_mass_neighborhood
end HartreeF.ComplexIMS
