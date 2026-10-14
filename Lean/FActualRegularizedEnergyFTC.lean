import FActualRegularizedMildDerivative
import FStateEnergyCalculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest StateEnergy
open CriticalPathSpace CriticalUniqueness IntervalTimeTransport ForcingContinuity ForcingDomain
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution

def regularizedVectorField (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (u : EnergyState) : EnergyState :=
  Complex.I • deltaJ hDensity hSob n u +
    Complex.I • S.sourceJ B n (forcingLp hH (energyValue u))

def regularizedEnergyRate (hDensity : OrdinaryH1Density) {K alpha : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (n : ℕ) (u : EnergyState) : ℝ :=
  fderiv ℝ (totalEnergy alpha) (J hDensity hSob n u)
    (regularizedVectorField hDensity hSob S B hH n u)

theorem regularizedVectorField_continuous (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c) (n : ℕ) :
    Continuous (regularizedVectorField hDensity hSob S B hH n) := by
  exact ((deltaJ hDensity hSob n).continuous.const_smul Complex.I).add
    (((S.sourceJ B n).continuous.comp
      ((forcingLp_continuous hH).comp energyValue.continuous)).const_smul Complex.I)

theorem regularizedEnergyRate_continuous (hDensity : OrdinaryH1Density)
    {K alpha : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha)) (n : ℕ) :
    Continuous (regularizedEnergyRate hDensity hSob S B hH n) := by
  exact ((totalEnergy_contDiff hH).continuous_fderiv_apply one_ne_zero).comp
    ((J hDensity hSob n).continuous.prodMk
      (regularizedVectorField_continuous hDensity hSob S B hH n))

/-- An actual interior mild trajectory has the derivative of the literal
paper total energy. The vector field was derived from its mild equation. -/
theorem actual_mild_regularized_energy_hasDerivAt (hDensity : OrdinaryH1Density)
    {K alpha a b t : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u)
    (n : ℕ) (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun s => totalEnergy alpha
      (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) s)))
      (regularizedEnergyRate hDensity hSob S B hH n
        (extendEnergyPath hab (energyPath _ u) t)) t := by
  exact ((totalEnergy_contDiff hH).differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (actual_mild_regularized_hasDerivAt hDensity hSob S B hH hab u0 u hmild n ht)

/-- Genuine Bochner integrability is produced from continuity on the closed
finite interval, separately from every estimate on the integral. -/
theorem actual_regularized_energy_rate_integrable (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) (n : ℕ) :
    IntervalIntegrable (fun t => regularizedEnergyRate hDensity hSob S B hH n
      (extendEnergyPath hab (energyPath _ u) t)) volume a b :=
  ((regularizedEnergyRate_continuous hDensity hSob S B hH n).comp
    (extendEnergyPath hab (energyPath _ u)).continuous).intervalIntegrable a b

/-- The finite-interval identity for the actual regularized mild solution.
Subsequent commutator algebra rewrites this native C1 rate. -/
theorem actual_mild_regularized_energy_increment (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u)
    (n : ℕ) :
    totalEnergy alpha (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) b)) -
      totalEnergy alpha (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) a)) =
      ∫ t in a..b, regularizedEnergyRate hDensity hSob S B hH n
        (extendEnergyPath hab (energyPath _ u) t) := by
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (f := fun t => totalEnergy alpha (J hDensity hSob n
      (extendEnergyPath hab (energyPath _ u) t)))
  · exact ((totalEnergy_contDiff hH).continuous.comp
      ((J hDensity hSob n).continuous.comp
        (extendEnergyPath hab (energyPath _ u)).continuous)).continuousOn
  · intro t ht
    exact actual_mild_regularized_energy_hasDerivAt hDensity hSob S B hH hab u0 u hmild n ht
  · exact actual_regularized_energy_rate_integrable hDensity hSob S B hH hab u n

#print axioms regularizedVectorField_continuous
#print axioms regularizedEnergyRate_continuous
#print axioms actual_mild_regularized_energy_hasDerivAt
#print axioms actual_regularized_energy_rate_integrable
#print axioms actual_mild_regularized_energy_increment
end HartreeF.Regularization.Actual
