import FRegularizedDuhamelDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace CriticalUniqueness IntervalTimeTransport ForcingContinuity ForcingDomain
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
local instance : SecondCountableTopologyEither ℝ EnergyState :=
  secondCountableTopologyEither_of_left ℝ EnergyState

/-- The literal Schwartz mild equation realizes a genuine EnergyState
Bochner integral after the constructed regularizer. -/
theorem actual_mild_regularized_bochner (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha c u0 u) (n : ℕ) (t : Set.Icc a b) :
    J hDensity hSob n (energyPath _ u t) =
      energyDuhamel hDensity hSob a (J hDensity hSob n u0)
        (sourcePath hDensity hSob S B hH hab u n) t := by
  apply energyDistribution_injective
  ext φ
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  let A := freeEnergyState hDensity hSob ((t : ℝ)-a) (J hDensity hSob n u0)
  let g : ℝ → EnergyState := fun s => freeEnergyState hDensity hSob ((t : ℝ)-s)
    (sourcePath hDensity hSob S B hH hab u n s)
  have hi : IntervalIntegrable g volume a t :=
    (freeEnergyState_continuous_path hDensity hSob _ _
      (continuous_const.sub continuous_id) (sourcePath hDensity hSob S B hH hab u n).continuous).intervalIntegrable _ _
  have hint := D.intervalIntegral_comp_comm hi
  have hlin : D (A + Complex.I • ∫ s in a..(t : ℝ), g s) =
      D A + Complex.I * ∫ s in a..(t : ℝ), D (g s) := by
    calc
      _ = D A + D (Complex.I • ∫ s in a..(t : ℝ), g s) := D.map_add _ _
      _ = D A + Complex.I • D (∫ s in a..(t : ℝ), g s) :=
        congrArg (fun z => D A + z) (D.map_smul Complex.I _)
      _ = D A + Complex.I • ∫ s in a..(t : ℝ), D (g s) :=
        congrArg (fun z : ℂ => D A + Complex.I • z) hint.symm
      _ = _ := rfl
  have hfree : D A = FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) (cutoffTest n φ) := by
    have hJ : energyDistribution (J hDensity hSob n u0) =
        (cutoff n).distribution (energyDistribution u0) := J_distribution hDensity hSob n u0
    have he : energyDistribution A =
        (cutoff n).distribution (FreeFlow.free ((t : ℝ)-a) (energyDistribution u0)) :=
      (freeEnergyState_distribution hDensity hSob ((t : ℝ)-a) _).trans
        ((congrArg (FreeFlow.free ((t : ℝ)-a)) hJ).trans
          ((cutoff n).distribution_free ((t : ℝ)-a) (energyDistribution u0)).symm)
    exact congrArg (fun T : TD => T φ) he
  have htime : (∫ s in a..(t : ℝ), D (g s)) =
      ∫ s in Set.Ioc a (t : ℝ), ∫ x,
        (Retarded.freeTest ((t : ℝ)-s) (cutoffTest n φ)) x •
          forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
    rw [intervalIntegral.integral_of_le t.property.1]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => regularized_duhamel_integrand
      hDensity hSob S B hH hab u n t s φ)
  have hleft : energyDistribution (J hDensity hSob n (energyPath _ u t)) φ =
      energyDistribution (energyPath _ u t) (cutoffTest n φ) :=
    congrArg (fun T : TD => T φ) (J_distribution hDensity hSob n (energyPath _ u t))
  exact (hleft.trans (hmild t (cutoffTest n φ))).trans
    (hlin.trans (congrArg₂ (fun z w : ℂ => z + Complex.I * w) hfree htime)).symm

#print axioms actual_mild_regularized_bochner
end HartreeF.Regularization.Actual
