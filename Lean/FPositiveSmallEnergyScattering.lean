import FSmallUniformCapFiniteS
import FSharpWFiniteSGlobalScattering

/-! A positive uniform scattering-size seed on the original stable branch.
This additional small-energy conclusion does not replace the full W goal. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.SmallEnergy
open EnergySpace CriticalPathSpace StateEnergy StateSharpThreshold
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open Regularization.Actual SharpOrdinary HeatRiesz MaximalTrajectory MaximalFiniteSGlobal
open DynamicSharpW
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath actualMaximalTrajectory freeEnergyState

theorem exists_positive_uniform_energy_seed (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ M : ℝ≥0, ∀ {s0 : ℝ} {u0 : EnergyState}
      (U : LocalMildTrajectory alpha (standardRieszConstant alpha) s0 u0),
      totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha) →
      pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha) →
      totalEnergy alpha u0 ≤ epsilon → UniformCompactS U M := by
  let choice := exists_small_state_cap_uniformS hDensity hSob h0 hfree hret hefree heret hOrd
  let delta : ℝ := Classical.choose choice
  have hd : 0 < delta := (Classical.choose_spec choice).1
  let mc := (Classical.choose_spec choice).2
  let M : ℝ≥0 := Classical.choose mc
  let A := max (K ^ ((6 : ℝ)⁻¹)) 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let k := 2*(3+alpha)/(2+alpha)
  have ha : 0 < alpha := hH.order_pos
  have hk : 0 < k := by dsimp [k]; positivity
  let sigma := delta/(A+1)
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  let epsilon := sigma^2/(k+1)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hke : k*epsilon ≤ sigma^2 := by
    dsimp [epsilon]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < k+1)).mpr
    nlinarith [sq_nonneg sigma]
  have hAs : A*sigma ≤ delta := by
    dsimp [sigma]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < A+1)).mpr
    nlinarith
  refine ⟨epsilon, hepsilon, M, ?_⟩
  intro s0 u0 U henergy hgradient hsmall
  have hcap : ∀ t ∈ U.domain, ‖U.state t‖ ≤ delta := by
    intro t ht
    have hg := (localMildTrajectory_pureGradient_cap hDensity hSob h0 hfree hret hefree
      heret hOrd hH hS S Bw Bs B6 U henergy hgradient t ht).1
    have hsqrt : Real.sqrt (k*totalEnergy alpha u0) ≤ sigma :=
      (Real.sqrt_le_left hsigma.le).mpr ((mul_le_mul_of_nonneg_left hsmall hk.le).trans hke)
    exact (energyState_le_pureGradient hSob (U.state t)).trans
      ((mul_le_mul_of_nonneg_left (hg.trans hsqrt) hA.le).trans hAs)
  exact (Classical.choose_spec mc) U hcap

/-- A uniform positive energy seed produces finite S, the actual global
lifespan and both scattering states. Finite S is a conclusion here. -/
theorem exists_positive_small_energy_scattering (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ M : ℝ≥0, ∀ (s0 : ℝ) (u0 : EnergyState),
      totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha) →
      pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha) →
      totalEnergy alpha u0 ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
      UniformCompactS U M ∧ U.domain = Set.univ ∧ ∃ uMinus uPlus : EnergyState,
        Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  let choice := exists_positive_uniform_energy_seed hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6
  let epsilon : ℝ := Classical.choose choice
  have he : 0 < epsilon := (Classical.choose_spec choice).1
  let mc := (Classical.choose_spec choice).2
  let M : ℝ≥0 := Classical.choose mc
  refine ⟨epsilon, he, M, ?_⟩
  intro s0 u0 henergy hgradient hsmall
  dsimp only
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
  have hfinite : UniformCompactS U M := (Classical.choose_spec mc) U henergy hgradient hsmall
  exact ⟨hfinite, actualMaximalTrajectory_global_scattering_of_W_and_finiteS hDensity hSob h0
    hfree hret hefree heret hOrd hH hS S Bw Bs B6 s0 u0 henergy hgradient ⟨M, hfinite⟩⟩

#print axioms exists_positive_uniform_energy_seed
#print axioms exists_positive_small_energy_scattering
end HartreeF.SmallEnergy
