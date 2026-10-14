import HartreeForcingDomain

/-! Actual gauge cancellation of the Hartree source. This is pointwise
source algebra, not a proof of conservation for a weak PDE solution. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.ForcingDomain

theorem forcing_gauge_im_zero (α c : ℝ) (f : Space → ℂ) (x : Space) :
    (forcing α c f x * star (f x)).im = 0 := by
  rw [forcing_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem forcing_gauge_pair {α c : ℝ} (hα : 0 < α) (f : Space → ℂ) (x : Space) :
    forcing α c f x * star (f x) =
      ((potential α c f x * powerDensity α f x : ℝ) : ℂ) := by
  have hn : ‖f x‖ ^ (1+α) * ‖f x‖^2 = ‖f x‖^(3+α) := by
    rw [← Real.rpow_natCast (‖f x‖) 2]
    rw [← Real.rpow_add' (norm_nonneg (f x))]
    · congr 1; ring
    · norm_num; linarith
  rw [forcing_apply]
  change (((potential α c f x : ℝ) : ℂ) * ((‖f x‖ ^ (1+α) : ℝ) : ℂ)) *
      (f x) * star (f x) = _
  rw [mul_assoc, mul_assoc]
  simp only [Complex.star_def, Complex.mul_conj']
  norm_cast
  unfold powerDensity
  rw [hn]

theorem forcing_mass_pairing_integrable {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {f : Space → ℂ} (hf6 : MemLp f 6 volume) :
    Integrable (fun x => forcing α c f x * star (f x)) volume := by
  have hi : Integrable (fun x => ((potential α c f x * powerDensity α f x : ℝ) : ℂ)) volume :=
    (interaction_density_integrable hHLS hf6).ofReal
  apply hi.congr
  filter_upwards [] with x
  exact (forcing_gauge_pair hHLS.order_pos f x).symm

theorem forcing_mass_pairing_integral {α c : ℝ} (hα : 0 < α) (f : Space → ℂ) :
    (∫ x, forcing α c f x * star (f x)) =
      ((∫ x, potential α c f x * powerDensity α f x : ℝ) : ℂ) := by
  calc
    _ = ∫ x, ((potential α c f x * powerDensity α f x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact forcing_gauge_pair hα f x
    _ = _ := integral_complex_ofReal

#print axioms forcing_gauge_im_zero
#print axioms forcing_gauge_pair
#print axioms forcing_mass_pairing_integrable
#print axioms forcing_mass_pairing_integral
end HartreeF.ForcingDomain
