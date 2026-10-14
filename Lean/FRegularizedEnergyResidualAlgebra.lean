import FRegularizedSpatialEnergyAlgebra

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open WeakSourcePairing RegularizedEnergyPairing StateEnergy ForcingDomain ForcingContinuity
attribute [local instance] canonicalEnergyNormedSpace
attribute [local irreducible] energySubmodule energyValue

/-- Representative identity for the native strong vector field. -/
theorem regularizedVectorField_value_l2 (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (u : EnergyState) (Q : EnergySpace.L2)
    (hQ : (energyValue (S.sourceJ Bs n (forcingLp hH (energyValue u))) : V → ℂ) =ᵐ[volume] Q) :
    (energyValue (regularizedVectorField hDensity hSob S Bs hH n u) : V → ℂ) =ᵐ[volume]
      (Complex.I • deltaJValueL2 n u + Complex.I • Q : EnergySpace.L2) := by
  simp only [regularizedVectorField, map_add, map_smul]
  filter_upwards [Lp.coeFn_add (Complex.I • energyValue (deltaJ hDensity hSob n u))
      (Complex.I • energyValue (S.sourceJ Bs n (forcingLp hH (energyValue u)))),
    Lp.coeFn_add (Complex.I • deltaJValueL2 n u) (Complex.I • Q),
    Lp.coeFn_smul Complex.I (energyValue (deltaJ hDensity hSob n u)),
    Lp.coeFn_smul Complex.I (energyValue (S.sourceJ Bs n (forcingLp hH (energyValue u)))),
    Lp.coeFn_smul Complex.I (deltaJValueL2 n u), Lp.coeFn_smul Complex.I Q,
    deltaJ_value_ae hDensity hSob n u, hQ] with x ha hb hc hd he hf hg hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [ha,hb,hc,hd,he,hf,hg,hh]

/-- Native pointwise energy cancellation. The hypotheses in this algebra
lemma are representative and weak-derivative identities; the actual path
consumer below produces all of them from the canonical Hartree sources. -/
theorem regularizedEnergyRate_residual_algebra (hDensity : OrdinaryH1Density)
    {K alpha : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (n : ℕ) (u : EnergyState) (N Q : EnergySpace.L2)
    (G QG : Fin 3 → SourceLp)
    (hN : forcing alpha (HeatRiesz.standardRieszConstant alpha)
      (energyValue (J hDensity hSob n u)) =ᵐ[volume] N)
    (hQ : (energyValue (S.sourceJ Bs n (forcingLp hH (energyValue u))) : V → ℂ) =ᵐ[volume] Q)
    (hG : ∀ j, ∂_{coordinate j} (Lp.toTemperedDistribution
        (forcingLp hH (energyValue (J hDensity hSob n u)))) =
      Lp.toTemperedDistribution (G j))
    (hQG : ∀ j, (QG j : V → ℂ) =ᵐ[volume]
      energyGradient j (S.sourceJ Bs n (forcingLp hH (energyValue u)))) :
    regularizedEnergyRate hDensity hSob S Bs hH n u =
      (∑ j : Fin 3, sourceIPair (QG j - G j)
        (energyValue ((firstCutoff n j).energyCLM hDensity hSob u))) -
      inner ℝ N (Complex.I • (Q - N)) := by
  have hp := forcing_energy_pair_l2 (J hDensity hSob n u)
    (regularizedVectorField hDensity hSob S Bs hH n u) N
    (Complex.I • deltaJValueL2 n u + Complex.I • Q) hN
    (regularizedVectorField_value_l2 hDensity hSob S Bs hH n u Q hQ)
  have hg (j : Fin 3) : inner ℝ (energyGradient j (J hDensity hSob n u))
      (energyGradient j (regularizedVectorField hDensity hSob S Bs hH n u)) =
      sourceIPair (QG j)
        (energyValue ((firstCutoff n j).energyCLM hDensity hSob u)) := by
    simp only [regularizedVectorField, map_add, map_smul, inner_add_right,
      regularized_kinetic_laplacian_zero, zero_add]
    exact (sourceIPair_l2 (QG j) _ _ _ (hQG j)
      (firstCutoff_value_gradient_ae hDensity hSob n u j)).symm
  have hibp := regularized_source_laplacian_pair hDensity hSob n u
    (forcingLp hH (energyValue (J hDensity hSob n u))) G N
    ((forcingLp_coeFn hH _).trans hN) hG
  unfold regularizedEnergyRate
  rw [totalEnergy_fderiv_apply hH, hp]
  simp only [hg, inner_add_right, hibp, map_sub, sub_apply,
    Finset.sum_sub_distrib, smul_sub, inner_sub_right, l2IPair_self, sub_zero]
  ring

#print axioms regularizedVectorField_value_l2
#print axioms regularizedEnergyRate_residual_algebra
end HartreeF.Regularization.Actual
