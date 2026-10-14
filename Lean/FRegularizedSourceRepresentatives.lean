import FActualGradientHartreeCommutator
import FActualL2HartreeCommutator
import FEnergyRegularizerConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport ForcingDomain ForcingContinuity ForcingL2
open ActualDuhamelPath
local instance sourceEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance sourcePathNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule criticalPathIntervalSource
  regularizeCriticalPath criticalL2Source energyPath energyValue
  actualL2Commutator actualGradientCommutator

theorem distribution_eq_of_spatial_ae {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : LpV p) (g : LpV q) (h : (f : V → ℂ) =ᵐ[volume] g) :
    Lp.toTemperedDistribution f = Lp.toTemperedDistribution g := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem forcingLp_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c) (u : L6) :
    (forcingLp hH u : V → ℂ) =ᵐ[volume] forcing alpha c u :=
  (forcing_memLp hH (Lp.memLp u)).coeFn_toLp

theorem sourceJ_value_ae (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (n : ℕ) (f : SourceLp) :
    (energyValue (S.sourceJ B n f) : V → ℂ) =ᵐ[volume] B.cutoffLp n f := by
  apply spatial_ae_eq_of_distribution_eq
  change energyDistribution (S.sourceJ B n f) = _
  rw [S.sourceJ_distribution, B.cutoffLp_distribution]

theorem sourceJ_gradient_ae (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (n : ℕ) (f g : SourceLp) (j : Fin 3)
    (hfg : ∂_{coordinate j} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g) :
    (energyGradient j (S.sourceJ B n f) : V → ℂ) =ᵐ[volume] B.cutoffLp n g := by
  apply spatial_ae_eq_of_distribution_eq
  change energyGradientDistribution j (S.sourceJ B n f) = _
  rw [← energyDistribution_derivative, S.sourceJ_distribution,
    BoundedSymbol.derivative_distribution, hfg, B.cutoffLp_distribution]

theorem sourceJ_value_ae_L2 (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (n : ℕ) (f : SourceLp) (g : EnergySpace.L2)
    (hfg : (f : V → ℂ) =ᵐ[volume] g) :
    (energyValue (S.sourceJ B n f) : V → ℂ) =ᵐ[volume] (cutoff n).l2 g := by
  apply spatial_ae_eq_of_distribution_eq
  change energyDistribution (S.sourceJ B n f) = _
  rw [S.sourceJ_distribution, BoundedSymbol.l2_distribution,
    distribution_eq_of_spatial_ae f g hfg]

theorem firstCutoff_value_gradient_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) (j : Fin 3) :
    (energyValue ((firstCutoff n j).energyCLM hDensity hSob u) : V → ℂ) =ᵐ[volume]
      energyGradient j (J hDensity hSob n u) := by
  apply spatial_ae_eq_of_distribution_eq
  change energyDistribution ((firstCutoff n j).energyCLM hDensity hSob u) =
    energyGradientDistribution j (J hDensity hSob n u)
  rw [← energyDistribution_derivative]
  exact (J_first_two_derivatives hDensity hSob n u).1 j

/-- Literal regularized nonlinear residual, with the actual sourceJ value. -/
def literalHartreeResidual (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (u : EnergyState) (x : V) : ℂ :=
  energyValue (S.sourceJ B n (forcingLp hH (energyValue u))) x -
    forcing alpha c (energyValue (J hDensity hSob n u)) x

def literalHartreeResidualLp (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (B : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha c) (n : ℕ) (u : EnergyState) : SourceLp :=
  B.cutoffLp n (forcingLp hH (energyValue u)) -
    forcingLp hH (energyValue (J hDensity hSob n u))

theorem literalHartreeResidualLp_coeFn (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (u : EnergyState) :
    (literalHartreeResidualLp hDensity hSob B hH n u : V → ℂ) =ᵐ[volume]
      literalHartreeResidual hDensity hSob S B hH n u := by
  filter_upwards [Lp.coeFn_sub (B.cutoffLp n (forcingLp hH (energyValue u)))
    (forcingLp hH (energyValue (J hDensity hSob n u))),
    sourceJ_value_ae S B n (forcingLp hH (energyValue u)),
    forcingLp_coeFn hH (energyValue (J hDensity hSob n u))] with x hx hJ hN
  exact hx.trans (by simp only [Pi.sub_apply, ← hJ, hN]; rfl)

theorem critical_source_value_eq_forcingLp (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b,
      (criticalPathIntervalSource hDensity hSob hH hab u 0).value t =
        forcingLp hH (energyValue (extendEnergyPath hab (energyPath _ u) t)) := by
  filter_upwards [criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u] with t ht
  exact Lp.ext (ht.trans (forcingLp_coeFn hH _).symm)

theorem actual_sourceJ_gradient_ae (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      (energyGradient j (S.sourceJ Bs n (forcingLp hH
        (energyValue (extendEnergyPath hab (energyPath _ u) t)))) : V → ℂ) =ᵐ[volume]
      Bs.cutoffLp n ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t) := by
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  filter_upwards [F.derivative, critical_source_value_eq_forcingLp hDensity hSob hH hab u]
    with t hder hval
  intro j
  apply sourceJ_gradient_ae S Bs n _ _ j
  rw [← hval]
  exact hder j

#print axioms critical_source_value_eq_forcingLp
#print axioms actual_sourceJ_gradient_ae

#print axioms sourceJ_value_ae
#print axioms sourceJ_gradient_ae
#print axioms sourceJ_value_ae_L2
#print axioms firstCutoff_value_gradient_ae
#print axioms literalHartreeResidualLp_coeFn
end HartreeF.Regularization.Actual
