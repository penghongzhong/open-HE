import FHartreeAffinePointwise
import FCriticalAffineIsometry
import FScalarSourceRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineForcing
open CriticalAffine EnergySpace ForcingDomain LocalScalarSource
attribute [local irreducible] energySubmodule

/-- Canonical state representatives obey the literal forcing covariance a.e. -/
theorem affineState_forcing_ae (alpha c : ℝ) {a : ℝ} (ha : 0<a) (b : Space) (u : EnergyState) :
    forcing alpha c (energyValue (affineState ha b u)) =ᵐ[volume]
      (fun x => a^(5/2:ℝ) • forcing alpha c (energyValue u) (affine a b x)) := by
  have h := forcing_ae_of_ae (alpha := alpha) (c := c) (affineState_value_ae ha b u)
  exact h.mono (fun x hx => hx.trans (forcing_valuePullback alpha c ha b (energyValue u) x))

/-- The paper length-scale convention is a=1/lambda and b=-y/lambda. -/
theorem criticalAffineState_forcing_ae (alpha c : ℝ) (lambda : ℝ) (hlambda : 0<lambda)
    (y : Space) (u : EnergyState) :
    forcing alpha c (energyValue (criticalAffineState lambda hlambda y u)) =ᵐ[volume]
      (fun x => lambda^(-(5/2:ℝ)) • forcing alpha c (energyValue u) (lambda⁻¹ • (x-y))) := by
  change forcing alpha c (energyValue (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u)) =ᵐ[volume]
    (fun x => lambda^(-(5/2:ℝ)) • forcing alpha c (energyValue u) (lambda⁻¹ • (x-y)))
  have h := affineState_forcing_ae alpha c (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u
  simpa only [affine, Real.inv_rpow hlambda.le, Real.rpow_neg hlambda.le,
    sub_eq_add_neg, smul_add, smul_neg] using h

/-- HLS produces both genuine potential integral domains and both finite scalar
forcing domains before the canonical covariance is consumed. -/
theorem affineState_forcing_domains_and_covariance {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {a : ℝ} (ha : 0<a) (b : Space) (u : EnergyState) :
    (∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel alpha c (x-y)*powerDensity alpha (energyValue u) y) volume) ∧
    (∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel alpha c (x-y)*powerDensity alpha (energyValue (affineState ha b u)) y) volume) ∧
    MemLp (forcing alpha c (energyValue u)) (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (forcing alpha c (energyValue (affineState ha b u))) (ENNReal.ofReal (6/5:ℝ)) volume ∧
    (forcing alpha c (energyValue (affineState ha b u)) =ᵐ[volume]
      (fun x => a^(5/2:ℝ) • forcing alpha c (energyValue u) (affine a b x))) := by
  obtain ⟨C,hC⟩ := potential_domain_bound hH
  obtain ⟨D,hD⟩ := forcing_energy_domain_bound hH
  exact ⟨(hC _ (Lp.memLp _)).1,(hC _ (Lp.memLp _)).1,
    (hD _ (Lp.memLp _)).1,(hD _ (Lp.memLp _)).1,affineState_forcing_ae alpha c ha b u⟩

#print axioms affineState_forcing_ae
#print axioms criticalAffineState_forcing_ae
#print axioms affineState_forcing_domains_and_covariance
end HartreeF.AffineForcing
