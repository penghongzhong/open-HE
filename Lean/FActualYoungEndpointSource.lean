import FYoungKernelScaling
import FConditionalMassRepresentative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.YoungSource
open EnergySpace EnergySpace.Highpass MassRecovery Retarded SobolevStretch StationarySelfTest

/-- Genuine projected endpoint source; no output source or Young bound is an input. -/
def projectedSource (q : Cutoff) {L : ℝ} (hL : 0 < L) (F : EndpointOne) : EndpointSource :=
  youngSourceCLM (p := sourceExponent) (by norm_num [sourceExponent])
    ((cutoffKernel q hL).toLp sourceExponent volume) F

theorem projectedSource_coe (q : Cutoff) {L : ℝ} (hL : 0 < L) (F : EndpointOne) :
    (projectedSource q hL F : ℝ → SourceSpace) =ᵐ[volume]
      fun s => youngCLM (p := sourceExponent) (by norm_num [sourceExponent])
        ((cutoffKernel q hL).toLp sourceExponent volume) (F s) :=
  youngSource_coe _ _ _

/-- One a.e. set of times carries equality of the entire distributions. -/
theorem projectedSource_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (F : EndpointOne) :
    ∀ᵐ s : ℝ ∂volume, Lp.toTemperedDistribution (projectedSource q hL F s) =
      low q L (Lp.toTemperedDistribution (F s)) := by
  filter_upwards [projectedSource_coe q hL F] with s hs
  rw [hs]
  exact young_cutoff_distribution _ q hL _

theorem projectedSource_tail_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (F : EndpointOne) (t : ℝ) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ici t)),
      Lp.toTemperedDistribution (projectedSource q hL F s) =
        low q L (Lp.toTemperedDistribution (F s)) :=
  ae_restrict_of_ae (projectedSource_distribution q hL F)

/-- The exact all-tail estimate has the cutoff-only constant Cq and sqrt(L). -/
theorem projectedSource_tail_norm (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (F : EndpointOne) (t : ℝ) :
    tailNorm t (projectedSource q hL F) ≤ cutoffYoungConstant q * Real.sqrt L * tailNorm t F := by
  exact (youngSource_tail_norm (p := sourceExponent) (by norm_num [sourceExponent])
    ((cutoffKernel q hL).toLp sourceExponent volume) F t).trans_eq
    (by rw [cutoffKernel_norm q hL])

/-- Quantified producer of the actual source used by the accepted conditional mass consumer. -/
theorem exists_actual_projected_source (q : Cutoff) {L : ℝ} (hL : 0 < L) (F : EndpointOne) :
    ∃ G : EndpointSource,
      (∀ᵐ s : ℝ ∂volume, Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s))) ∧
      ∀ t : ℝ, tailNorm t G ≤ cutoffYoungConstant q * Real.sqrt L * tailNorm t F :=
  ⟨projectedSource q hL F, projectedSource_distribution q hL F, projectedSource_tail_norm q hL F⟩

/-- The previous conditional consumer now needs only the original source, not a supplied G.
The original scalar no-waste statement and ordinary endpoint theorem remain explicit. -/
theorem conditional_mass_from_actual_source
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne)
    (hNW : OriginalScalarNoWaste σ t u F) {B : ℝ} (hB : pureGradientNorm u ≤ B) :
    ∃ v : L2, (v : V → ℂ) =ᵐ[volume] energyValue u ∧
      Lp.toTemperedDistribution v = energyDistribution u ∧
      (∀ j : Fin 3, LineDeriv.lineDerivOp (coordinate j) (Lp.toTemperedDistribution v) =
        Lp.toTemperedDistribution (energyGradient j u)) ∧
      ‖v‖ ≤ B / L + (C0 * cutoffYoungConstant q) * Real.sqrt L * tailNorm t F :=
  conditional_actual_mass_recovery hDensity hSob hE q hL hσ t u F
    (projectedSource q hL F) (projectedSource_tail_distribution q hL F t) hNW hB
    (projectedSource_tail_norm q hL F t)

end HartreeF.YoungSource
