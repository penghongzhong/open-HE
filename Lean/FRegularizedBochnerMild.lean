import FRegularizerBesselLp
import FMildHartreeDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace CriticalUniqueness IntervalTimeTransport ForcingContinuity ForcingDomain
local instance canonicalEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance canonicalPathNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution

/-- Joint continuity follows from the native unitary gradient action; no
operator-norm continuity of the unbounded free generator is presumed. -/
theorem freeEnergyState_continuous_path (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {T : Type*} [TopologicalSpace T]
    (q : T → ℝ) (u : T → EnergyState) (hq : Continuous q) (hu : Continuous u) :
    Continuous (fun t => freeEnergyState hDensity hSob (q t) (u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_of_gradientTendsto hSob
  intro j
  have hsmall : Tendsto (fun s => FreeFlow.freeL2 (q s)
      (energyGradient j (u s) - energyGradient j (u t))) (𝓝 t) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [FreeFlow.freeL2_norm]
    have h := (((energyGradient j).continuous.comp hu).tendsto t).sub_const (energyGradient j (u t))
    simpa only [sub_self, norm_zero, Function.comp_def] using h.norm
  have hfixed := ((FreeFlow.freeL2_time_continuous (energyGradient j (u t))).tendsto (q t)).comp
    (hq.tendsto t)
  simpa only [freeEnergyState_gradient, map_sub, Function.comp_def, sub_add_cancel, zero_add] using hsmall.add hfixed

/-- Bilinear transpose of the literal bounded Fourier multiplier. -/
def cutoffTest (n : ℕ) : Test →L[ℂ] Test :=
  fourierCLM ℂ Test ∘L SchwartzMap.smulLeftCLM ℂ (symbol n) ∘L fourierInvCLM ℂ Test

theorem cutoff_distribution_apply (n : ℕ) (T : TD) (φ : Test) :
    (cutoff n).distribution T φ = T (cutoffTest n φ) := rfl

def sourcePath (_hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (_hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) (n : ℕ) : C(ℝ, EnergyState) :=
  ⟨fun s => S.sourceJ B n (forcingLp hH
      (energyValue (extendEnergyPath hab (energyPath _ u) s))),
    (S.sourceJ B n).continuous.comp ((forcingLp_continuous hH).comp
      (energyValue.continuous.comp (extendEnergyPath hab (energyPath _ u)).continuous))⟩

theorem sourcePath_distribution (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) (n : ℕ) (s : ℝ) :
    energyDistribution (sourcePath hDensity hSob S B hH hab u n s) =
      (cutoff n).distribution (Lp.toTemperedDistribution (forcingLp hH
        (energyValue (extendEnergyPath hab (energyPath _ u) s)))) :=
  S.sourceJ_distribution B n _

attribute [local irreducible] sourcePath

theorem regularized_duhamel_integrand (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) (n : ℕ)
    (t s : ℝ) (φ : Test) :
    energyDistribution (freeEnergyState hDensity hSob (t-s)
      (sourcePath hDensity hSob S B hH hab u n s)) φ =
      ∫ x, (Retarded.freeTest (t-s) (cutoffTest n φ)) x •
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  let F := forcingLp hH (energyValue (extendEnergyPath hab (energyPath _ u) s))
  have hsrc : energyDistribution (sourcePath hDensity hSob S B hH hab u n s) =
      (cutoff n).distribution (Lp.toTemperedDistribution F) :=
    sourcePath_distribution hDensity hSob S B hH hab u n s
  have he : energyDistribution (freeEnergyState hDensity hSob (t-s)
      (sourcePath hDensity hSob S B hH hab u n s)) =
      (cutoff n).distribution (FreeFlow.free (t-s) (Lp.toTemperedDistribution F)) :=
    (freeEnergyState_distribution hDensity hSob (t-s) _).trans
      ((congrArg (FreeFlow.free (t-s)) hsrc).trans
        ((cutoff n).distribution_free (t-s) (Lp.toTemperedDistribution F)).symm)
  refine (congrArg (fun T : TD => T φ) he).trans ?_
  change Lp.toTemperedDistribution F (Retarded.freeTest (t-s) (cutoffTest n φ)) = _
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(forcing_memLp hH
    (Lp.memLp (energyValue (extendEnergyPath hab (energyPath _ u) s)))).coeFn_toLp]
    with x hx
  exact congrArg (fun z : ℂ => (Retarded.freeTest (t-s) (cutoffTest n φ)) x • z) hx

#print axioms freeEnergyState_continuous_path
#print axioms regularized_duhamel_integrand
end HartreeF.Regularization.Actual
