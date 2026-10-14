import FPowerMixedRemainders
import HartreeForcingDomain

/-!
Author candidate; exact per-attempt receipts determine native status. Exact original-function specializations for the middle source.
No HLS, norm membership, source budget, second derivative, or FTC premise is used.
Every theorem is pointwise and uses the same actual functions r and z throughout.
-/

noncomputable section
set_option autoImplicit false

namespace HartreeF

/-- Pointwise specialization to original density exponent `3 + α`; the remainder weight is `1 + α`. -/
theorem actual_powerDensity_mixed_remainder_bound {α : ℝ} (hα : 0 < α)
    (r z : Space → ℂ) (x : Space) :
    |powerDensity α (r + z) x - powerDensity α r x - powerDensity α z x| ≤
      WeakHartreeChain.densityMixedConstant (3 + α) * ‖r x‖ * ‖z x‖ *
        (‖r x‖ + ‖z x‖) ^ (1 + α) := by
  simpa only [powerDensity, WeakHartreeChain.density, Pi.add_apply,
    show (3 + α) - 2 = 1 + α by ring] using
    WeakHartreeChain.density_mixed_remainder_abs_bound
      (p := 3 + α) (by linarith) (r x) (z x)

/-- Pointwise specialization to the original local factor, with exponent `α`. -/
theorem actual_localFactor_mixed_remainder_bound {α : ℝ} (hα : 0 < α)
    (r z : Space → ℂ) (x : Space) :
    ‖ForcingDomain.localFactor α (r + z) x -
        ForcingDomain.localFactor α r x - ForcingDomain.localFactor α z x‖ ≤
      WeakHartreeChain.localFactorMixedConstant (1 + α) * ‖r x‖ * ‖z x‖ *
        (‖r x‖ + ‖z x‖) ^ α := by
  simpa only [ForcingDomain.localFactor, WeakHartreeChain.localFactor, Pi.add_apply,
    show (1 + α) - 1 = α by ring] using
    WeakHartreeChain.localFactor_mixed_remainder_bound
      (q := 1 + α) (by linarith) (r x) (z x)

/-- An actual pointwise function, not a source-budget assumption. -/
def actualDensityMixedRemainder (α : ℝ) (r z : Space → ℂ) : Space → ℝ :=
  powerDensity α (r + z) - powerDensity α r - powerDensity α z

/-- An actual pointwise function, not a source-budget assumption. -/
def actualLocalFactorMixedRemainder (α : ℝ) (r z : Space → ℂ) : Space → ℂ :=
  ForcingDomain.localFactor α (r + z) -
    ForcingDomain.localFactor α r - ForcingDomain.localFactor α z

theorem actual_powerDensity_middle_decomposition (α : ℝ) (r z : Space → ℂ) :
    powerDensity α (r + z) - powerDensity α r =
      powerDensity α z + actualDensityMixedRemainder α r z := by
  unfold actualDensityMixedRemainder
  abel

theorem actual_localFactor_middle_decomposition (α : ℝ) (r z : Space → ℂ) :
    ForcingDomain.localFactor α (r + z) - ForcingDomain.localFactor α r =
      ForcingDomain.localFactor α z + actualLocalFactorMixedRemainder α r z := by
  unfold actualLocalFactorMixedRemainder
  abel

theorem actualDensityMixedRemainder_bound {α : ℝ} (hα : 0 < α)
    (r z : Space → ℂ) (x : Space) :
    |actualDensityMixedRemainder α r z x| ≤
      WeakHartreeChain.densityMixedConstant (3 + α) * ‖r x‖ * ‖z x‖ *
        (‖r x‖ + ‖z x‖) ^ (1 + α) := by
  exact actual_powerDensity_mixed_remainder_bound hα r z x

theorem actualLocalFactorMixedRemainder_bound {α : ℝ} (hα : 0 < α)
    (r z : Space → ℂ) (x : Space) :
    ‖actualLocalFactorMixedRemainder α r z x‖ ≤
      WeakHartreeChain.localFactorMixedConstant (1 + α) * ‖r x‖ * ‖z x‖ *
        (‖r x‖ + ‖z x‖) ^ α := by
  exact actual_localFactor_mixed_remainder_bound hα r z x

#print axioms actual_powerDensity_mixed_remainder_bound
#print axioms actual_localFactor_mixed_remainder_bound
#print axioms actual_powerDensity_middle_decomposition
#print axioms actual_localFactor_middle_decomposition
#print axioms actualDensityMixedRemainder_bound
#print axioms actualLocalFactorMixedRemainder_bound

end HartreeF
