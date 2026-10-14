import FLocalMildTrajectory

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness
open SobolevStretch StationarySelfTest ActualStrichartz
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap

/-- The actual free-plus-retarded path associated with a constructed compatible
source. Its source is data; its closed energy and critical path are outputs. -/
def closedSourcePath (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (u0 : EnergyState)
    (F : CompatibleIntervalSource a T) : CriticalPath (intervalMeasure a T) :=
  freeCriticalPath hDensity hSob hfree a T (freeEnergyState hDensity hSob (-a) u0) +
    Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret F

theorem closedSourcePath_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (u0 : EnergyState)
    (F : CompatibleIntervalSource a T) (t : Set.Icc a T) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _
      (closedSourcePath hDensity hSob h0 hfree hret u0 F) t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Ioc a (t : ℝ),
          Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  simp only [closedSourcePath, map_add, map_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, add_apply, smul_apply,
    freeCriticalPath_energy, intervalRetardedCriticalPath_forward_scalar, smul_eq_mul]
  rw [← freeEnergyState_add_time, freeEnergyState_distribution]
  simp only [sub_eq_add_neg]

attribute [local irreducible] closedSourcePath

/-- Agreement of actual source classes on an earlier interval identifies every
actual energy state there, including the closed right endpoint. -/
theorem closedSourcePath_agrees (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (hbT : b ≤ T) (u0 : EnergyState)
    (F : CompatibleIntervalSource a T) (u : CriticalPath (intervalMeasure a b))
    (hu : IsMildHartreePath hab alpha kernel u0 u)
    (hsource : ∀ᵐ s ∂localMeasure a b, F.value s =
      (criticalPathIntervalSource hDensity hSob hH hab u 0).value s)
    (t : Set.Icc a b) :
    energyPath _ (closedSourcePath hDensity hSob h0 hfree hret u0 F)
      ⟨t, t.property.1, t.property.2.trans hbT⟩ = energyPath _ u t := by
  apply energyDistribution_injective
  ext φ
  rw [closedSourcePath_formula hDensity hSob h0 hfree hret u0 F
    ⟨t, t.property.1, t.property.2.trans hbT⟩ φ]
  have hf := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab u0 u).mp hu
  have hu' := hartreeDuhamelMap_source_formula hDensity hSob h0 hfree hret hH hab u0 u t φ
  have hu'' := (congrArg (fun z : CriticalPath (intervalMeasure a b) =>
    energyDistribution (energyPath _ z t) φ) hf).symm.trans hu'
  have hforward := localPast_integral_eq_forward t (fun s =>
    Lp.toTemperedDistribution
      ((criticalPathIntervalSource hDensity hSob hH hab u 0).value s)
      (freeTest ((t : ℝ)-s) φ))
  apply Eq.trans ?_ (hu''.trans (congrArg
    (fun z : ℂ => FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) φ + Complex.I*z)
    hforward)).symm
  apply congrArg (fun z : ℂ => FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) φ + Complex.I*z)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show Set.Ioc a (t : ℝ) ⊆ Set.Icc a b from
      fun _ hs => ⟨hs.1.le, hs.2.trans t.property.2⟩) hsource] with s hs
  exact congrArg (fun z : SourceSpace => Lp.toTemperedDistribution z
    (freeTest ((t : ℝ)-s) φ)) hs

/-- Once its actual source has been identified with its own literal forcing,
the constructed closed path satisfies the genuine Hartree mild equation. -/
theorem closedSourcePath_mild (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (haT : a ≤ T) (u0 : EnergyState)
    (F : CompatibleIntervalSource a T)
    (hsource : ∀ᵐ s ∂localMeasure a T, (F.value s : Space → ℂ) =ᵐ[volume]
      forcing alpha kernel (energyValue (extendEnergyPath haT (energyPath _
        (closedSourcePath hDensity hSob h0 hfree hret u0 F)) s))) :
    IsMildHartreePath haT alpha kernel u0
      (closedSourcePath hDensity hSob h0 hfree hret u0 F) := by
  intro t φ
  rw [closedSourcePath_formula hDensity hSob h0 hfree hret u0 F t φ]
  apply congrArg (fun z : ℂ => FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) φ + Complex.I*z)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show Set.Ioc a (t : ℝ) ⊆ Set.Icc a T from
      fun _ hs => ⟨hs.1.le, hs.2.trans t.property.2⟩) hsource] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact hs.mono (fun x hx => congrArg (fun z : ℂ => (freeTest ((t : ℝ)-s) φ) x • z) hx)

#print axioms HartreeF.FiniteEndpoint.closedSourcePath_formula
#print axioms HartreeF.FiniteEndpoint.closedSourcePath_agrees
#print axioms HartreeF.FiniteEndpoint.closedSourcePath_mild
end HartreeF.FiniteEndpoint
