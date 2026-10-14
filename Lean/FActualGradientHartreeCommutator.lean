import FActualCriticalPathRegularization
import FIntervalGradientSourceContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace EnergyRegularizer SobolevStretch StationarySelfTest
open StrongOperatorPaths ForcingDomain CriticalSourceBounds ActualDuhamelPath
open IntervalTimeTransport Retarded

attribute [local irreducible] energySubmodule criticalPathSubmodule
  regularizeCriticalPath criticalPathIntervalSource

def actualGradientCommutator (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (n : ℕ) (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    LocalEndpointSource (Set.Icc a b) :=
  (Bs.cutoffLp n).compLp
    ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j) -
      (criticalPathIntervalSource hDensity hSob hH hab
        (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u) 0).gradient j

/-- The actual gradient commutator converges strongly; smallness is a
conclusion from the actual nonlinear continuity and actual graph approximation. -/
theorem actualGradientCommutator_tendsto (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    Tendsto (fun n => actualGradientCommutator hDensity hSob hH hab Bw Bs n u j)
      atTop (𝓝 0) := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  have hb (n : ℕ) : ‖Bs.cutoffLp n‖ ≤ (2 : ℝ≥0) :=
    (Bs.cutoffLp n).opNorm_le_bound (by norm_num) (Bs.cutoffLp_bound n)
  have h1 := compLp_tendsto (localMeasure a b) (q := 2) (by decide)
    Bs.cutoffLp 2 hb Bs.cutoffLp_strong
    ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j)
  have h2 := criticalPathIntervalSource_gradient_tendsto hDensity hSob hH hab j
    (fun n => regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u) u
    (regularizeCriticalPath_tendsto (intervalMeasure a b) hDensity hSob Bw u)
  simpa only [actualGradientCommutator, Function.comp_def, sub_self] using h1.sub h2

theorem actualGradientCommutator_norm_tendsto (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    Tendsto (fun n => ‖actualGradientCommutator hDensity hSob hH hab Bw Bs n u j‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (actualGradientCommutator_tendsto hDensity hSob hH hab Bw Bs u j).norm

#print axioms actualGradientCommutator
#print axioms actualGradientCommutator_tendsto
#print axioms actualGradientCommutator_norm_tendsto
end HartreeF.Regularization.Actual
