import FActualCriticalPathRegularization
import FCriticalPathL2Continuity

/-! Literal scalar Hartree commutator: its Bochner L2_t L2_x norm vanishes
under the actual regularizers. No residual-smallness hypothesis is supplied. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace EnergyRegularizer SobolevStretch StationarySelfTest
open StrongOperatorPaths ForcingDomain ForcingContinuity ForcingL2

attribute [local irreducible] energySubmodule criticalPathSubmodule criticalL2Source
  regularizeCriticalPath

theorem cutoff_l2_strong (f : EnergySpace.L2) :
    Tendsto (fun n => (cutoff n).l2 f) atTop (𝓝 f) := by
  apply BoundedSymbol.l2_tendsto cutoff (C := 1) (fun _ => le_rfl)
  filter_upwards [(volume : Measure V).ae_ne (0 : V)] with ξ hξ
  exact symbol_tendsto ξ hξ

theorem cutoff_l2_opNorm_le_one (n : ℕ) : ‖(cutoff n).l2‖ ≤ 1 := by
  apply (cutoff n).l2.opNorm_le_bound zero_le_one
  intro f
  exact (cutoff n).l2_norm_le f

section Paths
variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ]

def actualL2Commutator (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (B : OrdinaryBesselLp criticalExponent) (n : ℕ) (u : CriticalPath μ) :
    Lp EnergySpace.L2 2 μ :=
  (cutoff n).l2.compLp (criticalL2Source μ hDensity hSob hH u) -
    criticalL2Source μ hDensity hSob hH
      (regularizeCriticalPath μ hDensity hSob B n u)

theorem actualL2Commutator_tendsto (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (B : OrdinaryBesselLp criticalExponent) (u : CriticalPath μ) :
    Tendsto (fun n => actualL2Commutator μ hDensity hSob hH B n u)
      atTop (𝓝 0) := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  have h1 := compLp_tendsto μ (q := 2) (by decide)
    (fun n => (cutoff n).l2) 1 cutoff_l2_opNorm_le_one cutoff_l2_strong
    (criticalL2Source μ hDensity hSob hH u)
  have h2 := (criticalL2Source_continuous μ hDensity hSob hH).tendsto u |>.comp
    (regularizeCriticalPath_tendsto μ hDensity hSob B u)
  simpa only [actualL2Commutator, Function.comp_def, sub_self] using h1.sub h2

theorem actualL2Commutator_norm_tendsto (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (B : OrdinaryBesselLp criticalExponent) (u : CriticalPath μ) :
    Tendsto (fun n => ‖actualL2Commutator μ hDensity hSob hH B n u‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (actualL2Commutator_tendsto μ hDensity hSob hH B u).norm

end Paths
#print axioms cutoff_l2_strong
#print axioms cutoff_l2_opNorm_le_one
#print axioms actualL2Commutator
#print axioms actualL2Commutator_tendsto
#print axioms actualL2Commutator_norm_tendsto
end HartreeF.Regularization.Actual
