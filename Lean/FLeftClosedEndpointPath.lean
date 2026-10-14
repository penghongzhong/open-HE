import FLocalMildTrajectory
import FBackwardMildHartreeDefinition

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option diagnostics true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness
open SobolevStretch StationarySelfTest ActualStrichartz
local instance leftClosureEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance leftClosureGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource backwardHartreeDuhamelMap

/-- The closed path at a finite left endpoint is the free path anchored at the
right endpoint minus i times the genuine future source integral. -/
def leftClosedSourcePath (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (uc : EnergyState)
    (F : CompatibleIntervalSource T c) : CriticalPath (intervalMeasure T c) :=
  freeCriticalPath hDensity hSob hfree T c (freeEnergyState hDensity hSob (-c) uc) -
    Complex.I • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F

theorem leftClosedSourcePath_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (uc : EnergyState)
    (F : CompatibleIntervalSource T c) (t : Set.Icc T c) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _
      (leftClosedSourcePath hDensity hSob h0 hfree hret uc F) t) φ =
      FreeFlow.free ((t : ℝ)-c) (energyDistribution uc) φ - Complex.I *
        ∫ s in Set.Ioc (t : ℝ) c,
          Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  let f := freeCriticalPath hDensity hSob hfree T c (freeEnergyState hDensity hSob (-c) uc)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have he := complexDecrement_map_eval (energyPath (intervalMeasure T c)) D f r t
  have hf : D (energyPath _ f t) = FreeFlow.free ((t : ℝ)-c) (energyDistribution uc) φ := by
    change energyDistribution (energyPath _ f t) φ = _
    rw [freeCriticalPath_energy, ← freeEnergyState_add_time, freeEnergyState_distribution]
    rfl
  have hr : D (energyPath _ r t) = ∫ s in Set.Ioc (t : ℝ) c,
      Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) :=
    intervalAdvancedCriticalPath_scalar hDensity hSob h0 hfree hret F t φ
  unfold leftClosedSourcePath
  change D (energyPath _ (f - Complex.I • r) t) = _
  exact he.trans (congrArg₂ (fun x y : ℂ => x - Complex.I * y) hf hr)

attribute [local irreducible] leftClosedSourcePath

/-- Equality of the actual sources identifies every state on the smaller
interval, using the unchanged backward equation of the actual trajectory. -/
theorem leftClosedSourcePath_agrees (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel T b c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hbc : b ≤ c) (hTb : T ≤ b) (uc : EnergyState)
    (F : CompatibleIntervalSource T c) (u : CriticalPath (intervalMeasure b c))
    (hu : IsBackwardMildHartreePath (a := b) (b := c) hbc alpha kernel uc u)
    (hsource : ∀ᵐ s ∂localMeasure b c, F.value s =
      (criticalPathIntervalSource (a := b) (b := c) hDensity hSob hH hbc u 0).value s)
    (t : Set.Icc b c) :
    energyPath (intervalMeasure T c) (leftClosedSourcePath (T := T) (c := c) hDensity hSob h0 hfree hret uc F)
      ⟨(t : ℝ), hTb.trans t.property.1, t.property.2⟩ = energyPath (intervalMeasure b c) u t := by
  apply energyDistribution_injective
  ext φ
  rw [leftClosedSourcePath_formula hDensity hSob h0 hfree hret uc F
    ⟨t, hTb.trans t.property.1, t.property.2⟩ φ]
  apply Eq.trans ?_ (hu t φ).symm
  apply congrArg (fun z : ℂ => FreeFlow.free ((t : ℝ)-c) (energyDistribution uc) φ - Complex.I*z)
  apply integral_congr_ae
  have hsub : Set.Ioc (t : ℝ) c ⊆ Set.Icc b c :=
    fun _ hs => ⟨t.property.1.trans hs.1.le, hs.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsource,
    ae_restrict_of_ae_restrict_of_subset hsub
      (criticalPathIntervalSource_single_coeFn hDensity hSob hH hbc u)] with s hs ha
  rw [hs, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact ha.mono (fun x hx => congrArg (fun z : ℂ => (freeTest ((t : ℝ)-s) φ) x • z) hx)

/-- Identification with the literal Hartree forcing gives the genuine
backward mild equation on the entire closed interval. -/
theorem leftClosedSourcePath_mild (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hTc : T ≤ c) (uc : EnergyState)
    (F : CompatibleIntervalSource T c)
    (hsource : ∀ᵐ s ∂localMeasure T c, (F.value s : Space → ℂ) =ᵐ[volume]
      forcing alpha kernel (energyValue (extendEnergyPath hTc (energyPath _
        (leftClosedSourcePath hDensity hSob h0 hfree hret uc F)) s))) :
    IsBackwardMildHartreePath hTc alpha kernel uc
      (leftClosedSourcePath hDensity hSob h0 hfree hret uc F) := by
  intro t φ
  rw [leftClosedSourcePath_formula hDensity hSob h0 hfree hret uc F t φ]
  apply congrArg (fun z : ℂ => FreeFlow.free ((t : ℝ)-c) (energyDistribution uc) φ - Complex.I*z)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show Set.Ioc (t : ℝ) c ⊆ Set.Icc T c from
      fun _ hs => ⟨t.property.1.trans hs.1.le, hs.2⟩) hsource] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact hs.mono (fun x hx => congrArg (fun z : ℂ => (freeTest ((t : ℝ)-s) φ) x • z) hx)

#print axioms HartreeF.FiniteEndpoint.leftClosedSourcePath_formula
#print axioms HartreeF.FiniteEndpoint.leftClosedSourcePath_agrees
#print axioms HartreeF.FiniteEndpoint.leftClosedSourcePath_mild
end HartreeF.FiniteEndpoint
