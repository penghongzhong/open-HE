import FActualHartreeLocalDualSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge ForcingDomain
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace

variable {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

/-- The genuine coordinate flux, using the original value and original weak gradient. -/
def fluxIntegrand (u : EnergyState) (j : Fin 3) (x : V) : ℂ :=
  (coefficientDerivative χ j x : ℂ) * energyGradient j u x * star (energyValue u x)

include hχ hc

theorem fluxIntegrand_integrable (u : EnergyState) (j : Fin 3) :
    Integrable (fluxIntegrand (χ := χ) u j) volume := by
  let D := cutoffL6L2 (coefficientDerivative_continuous hχ j)
    (coefficientDerivative_compact hc j)
  apply (spatialPair_integrable (energyGradient j u) (D (energyValue u))).congr
  filter_upwards [cutoffL6L2_ae (coefficientDerivative_continuous hχ j)
    (coefficientDerivative_compact hc j) (energyValue u)] with x hx
  change energyGradient j u x * star (D (energyValue u) x) = _
  rw [show D (energyValue u) x = _ from hx]
  apply Complex.ext <;> simp [fluxIntegrand, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

theorem kineticIntegral_im_eq_flux (u : EnergyState) (j : Fin 3) :
    (∫ x : V, kineticIntegrand (χ := χ) u u j x).im =
      (∫ x : V, fluxIntegrand (χ := χ) u j x).im := by
  change Complex.imCLM _ = Complex.imCLM _
  rw [← Complex.imCLM.integral_comp_comm (kineticIntegrand_integrable hχ hc u u j),
    ← Complex.imCLM.integral_comp_comm (fluxIntegrand_integrable hχ hc u j)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [kineticIntegrand, fluxIntegrand, Complex.real_smul, Complex.mul_re, Complex.mul_im]
  ring

theorem sourceToDualCLM_diagonal {α c : ℝ} (hH : OrdinaryHLS α c) (u : EnergyState) :
    sourceToDualCLM hχ hc (ForcingContinuity.forcingLp hH (energyValue u)) u =
      localizedHartreePair α c χ u := by
  rw [sourceToDualCLM_eq_integral hχ hc hH]
  apply integral_congr_ae
  filter_upwards [] with x
  apply Complex.ext <;> simp [sourceIntegrand, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

/-- Legal real Hartree cancellation leaves exactly the original spatial flux candidate.
This is a spatial identity, not a time derivative or a conservation law. -/
theorem actualPDEDual_diagonal_flux {α c : ℝ} (hH : OrdinaryHLS α c) (u : EnergyState) :
    actualPDEDual hχ hc hH u u = ∑ j : Fin 3, (∫ x : V, fluxIntegrand (χ := χ) u j x).im := by
  have hs : (∫ x : V, sourceIntegrand (χ := χ) α c u u x).im = 0 := by
    rw [← sourceToDualCLM_eq_integral hχ hc hH, sourceToDualCLM_diagonal hχ hc hH]
    exact (actual_localized_hartree_cancellation hH hχ.continuous hc u).2.1
  rw [actualPDEDual_apply hχ hc hH]
  simp only [spatialWeakForm, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, Complex.add_im, Complex.neg_im, hs, add_zero, neg_neg]
  change Complex.imCLM (∑ j : Fin 3, ∫ x : V, kineticIntegrand (χ := χ) u u j x) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => kineticIntegral_im_eq_flux hχ hc u j)

omit hχ hc in
/-- Same exact physical cutoff and same actual nonlinearity as the accepted charge form. -/
def physicalPDEDual {R α c : ℝ} (hR : 0 < R) (hH : OrdinaryHLS α c) :
    EnergyState → (EnergyState →L[ℝ] ℝ) :=
  actualPDEDual (LocalChargeRigidity.chargeCutoff_smooth R)
    (LocalChargeRigidity.chargeCutoff_compact hR) hH

omit hχ hc in
theorem physicalPDEDual_continuous {R α c : ℝ} (hR : 0 < R) (hH : OrdinaryHLS α c) :
    Continuous (physicalPDEDual hR hH) :=
  actualPDEDual_continuous (LocalChargeRigidity.chargeCutoff_smooth R)
    (LocalChargeRigidity.chargeCutoff_compact hR) hH

omit hχ hc in
theorem physicalPDEDual_exact_domain {R α c : ℝ} (hR : 0 < R) (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hu : ContinuousOn u S) :
    ContinuousOn (fun t => physicalPDEDual hR hH (u t)) S ∧
    ∀ a b : ℝ, Icc a b ⊆ S →
      IntegrableOn (fun t => physicalPDEDual hR hH (u t)) (Icc a b) volume := by
  have hg := (physicalPDEDual_continuous hR hH).comp_continuousOn hu
  exact ⟨hg, fun a b hab => (hg.mono hab).integrableOn_Icc⟩

end HartreeF.LocalDualSource
