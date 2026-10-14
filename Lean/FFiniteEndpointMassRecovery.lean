import FHardyFatou

/-!
The nonnegative Fatou step in manuscript Proposition `crit:global`.
This helper recovers the full L2 domain from genuine integrable localized
charges. The actual Hartree trajectory must still produce the localized
bound, the cutoff convergence, and the subsequent conservation argument.
No finite-endpoint exclusion or scattering conclusion is assumed here.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace HartreeF.FiniteEndpointMassRecovery
open EnergySpace SameStateHardy

/-- Uniformly bounded nonnegative localized square integrals, whose cutoffs
converge to one, give actual scalar L2 membership and the same mass bound.
No global L2 domain is an input and no totalized integral supplies finiteness. -/
theorem memLp_two_of_localized_mass_bound
    {f : V → ℂ} {χ : ℕ → V → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : 0 ≤ C)
    (hχ : ∀ n, 0 ≤ᵐ[volume] χ n)
    (hi : ∀ n, Integrable (fun x => χ n x * ‖f x‖ ^ 2) volume)
    (ht : ∀ᵐ x ∂volume, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hb : ∀ n, (∫ x, χ n x * ‖f x‖ ^ 2) ≤ C) :
    MemLp f 2 volume ∧ (∫ x, ‖f x‖ ^ 2) ≤ C := by
  have hn (n : ℕ) : 0 ≤ᵐ[volume] (fun x => χ n x * ‖f x‖ ^ 2) :=
    (hχ n).mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have hFatou : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) ≤ ENNReal.ofReal C := by
    apply lintegral_le_of_ae_tendsto_of_bounds
      (F := fun n x => ENNReal.ofReal (χ n x * ‖f x‖ ^ 2))
      (b := fun _ => ENNReal.ofReal C)
    · exact fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    · filter_upwards [ht] with x hx
      simpa only [one_mul] using ENNReal.tendsto_ofReal (hx.mul_const (‖f x‖ ^ 2))
    · intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hn n)]
      exact ENNReal.ofReal_le_ofReal (hb n)
    · exact tendsto_const_nhds
  have hscale : 4 * (C / 4) = C := by ring
  obtain ⟨_, _, hmass, hmem, _⟩ :=
    l2_of_square_lintegral_bound (E := C / 4) hf (div_nonneg hC (by norm_num))
      (by simpa only [hscale] using hFatou)
  exact ⟨hmem, by simpa only [hscale] using hmass⟩

#print axioms memLp_two_of_localized_mass_bound
end HartreeF.FiniteEndpointMassRecovery
