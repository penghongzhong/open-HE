import FConditionalActualMassDecay
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.MassAsymptotics
open EnergySpace EnergySpace.Highpass MassRecovery YoungSource Retarded SobolevStretch StationarySelfTest

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
variable {C0 : ℝ} (hE : OrdinaryEndpointBound C0) (q : Cutoff)
variable {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)

/-- A concrete positive cutoff sequence tending to zero. -/
def continuityCutoff (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) ^ 2

theorem continuityCutoff_pos (n : ℕ) : 0 < continuityCutoff n := by
  unfold continuityCutoff
  positivity

theorem continuityCutoff_tendsto_zero : Tendsto continuityCutoff atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0)
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

include hDensity hSob hE q hσ

/-- The same actual original L2 representative is uniformly approximated on the exact
no-waste time domain by the fixed-frequency highpass maps. -/
theorem highpass_tendstoUniformlyOn_actualValue (F : EndpointOne) (u : ℝ → EnergyState)
    (S : Set ℝ) (hNW : ∀ t ∈ S, OriginalScalarNoWaste σ t (u t) F) :
    TendstoUniformlyOn
      (fun n t => highValueL2 hDensity hSob q (continuityCutoff_pos n) (u t))
      (fun t => actualValue hDensity hSob hE q hσ F t (u t)) atTop S := by
  have hr : Tendsto (fun n => (C0 * cutoffYoungConstant q) *
      Real.sqrt (continuityCutoff n) * ‖F‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_mul] using
      (continuityCutoff_tendsto_zero.sqrt.const_mul (C0 * cutoffYoungConstant q)).mul_const ‖F‖
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hr.eventually (gt_mem_nhds hε)] with n hn
  intro t ht
  rw [dist_eq_norm]
  exact (actualValue_low_error_uniform hDensity hSob hE q hσ F t (u t)
    (hNW t ht) (continuityCutoff_pos n)).trans_lt hn

/-- C_t L2 for the original value on its stated time domain follows natively from
C_t EnergyState and the actual source/no-waste inputs. No mass-continuity premise. -/
theorem actualValue_continuousOn (F : EndpointOne) (u : ℝ → EnergyState)
    (S : Set ℝ) (hu : ContinuousOn u S)
    (hNW : ∀ t ∈ S, OriginalScalarNoWaste σ t (u t) F) :
    ContinuousOn (fun t => actualValue hDensity hSob hE q hσ F t (u t)) S := by
  apply (highpass_tendstoUniformlyOn_actualValue hDensity hSob hE q hσ F u S hNW).continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  exact (highValueL2CLM hDensity hSob q (continuityCutoff_pos n)).continuous.comp_continuousOn hu

/-- Full real-time continuity when the inputs genuinely hold on all of R. -/
theorem actualValue_continuous (F : EndpointOne) (u : ℝ → EnergyState)
    (hu : Continuous u) (hNW : ∀ t, OriginalScalarNoWaste σ t (u t) F) :
    Continuous (fun t => actualValue hDensity hSob hE q hσ F t (u t)) := by
  apply continuousOn_univ.mp
  exact actualValue_continuousOn hDensity hSob hE q hσ F u univ hu.continuousOn
    (fun t _ => hNW t)

/-- Continuity of the norm refers to the same canonical original EnergyState value. -/
theorem originalValue_massNorm_continuousOn (F : EndpointOne) (u : ℝ → EnergyState)
    (S : Set ℝ) (hu : ContinuousOn u S)
    (hNW : ∀ t ∈ S, OriginalScalarNoWaste σ t (u t) F) :
    ContinuousOn (fun t => (eLpNorm (energyValue (u t) : V → ℂ) 2 volume).toReal) S := by
  apply (actualValue_continuousOn hDensity hSob hE q hσ F u S hu hNW).norm.congr
  intro t ht
  exact (originalValue_memLp_and_norm hDensity hSob hE q hσ F t (u t) (hNW t ht)).2

theorem originalValue_continuousL2_representative (F : EndpointOne) (u : ℝ → EnergyState)
    (S : Set ℝ) (hu : ContinuousOn u S)
    (hNW : ∀ t ∈ S, OriginalScalarNoWaste σ t (u t) F) :
    ∃ v : ℝ → L2, ContinuousOn v S ∧
      ∀ t ∈ S, (v t : V → ℂ) =ᵐ[volume] energyValue (u t) ∧
        Lp.toTemperedDistribution (v t) = energyDistribution (u t) :=
  ⟨fun t => actualValue hDensity hSob hE q hσ F t (u t),
    actualValue_continuousOn hDensity hSob hE q hσ F u S hu hNW,
    fun t ht => ⟨actualValue_same_value hDensity hSob hE q hσ F t (u t) (hNW t ht),
      actualValue_distribution hDensity hSob hE q hσ F t (u t) (hNW t ht)⟩⟩

/-- One actual representative simultaneously carries the original value, the exact time-domain
continuity, and full-halfline decay. The source/no-waste/ordinary inputs remain visible. -/
theorem original_halfline_mass_recovery_decay_continuity
    (F : EndpointOne) (u : ℝ → EnergyState) (a B : ℝ)
    (hu : ContinuousOn u (Ici a))
    (hNW : ∀ t ∈ Ici a, OriginalScalarNoWaste σ t (u t) F)
    (hB : ∀ t ∈ Ici a, pureGradientNorm (u t) ≤ B) :
    ∃ v : ℝ → L2, ContinuousOn v (Ici a) ∧
      (∀ t ∈ Ici a, (v t : V → ℂ) =ᵐ[volume] energyValue (u t) ∧
        Lp.toTemperedDistribution (v t) = energyDistribution (u t)) ∧
      Tendsto (fun t : ℝ => ‖v t‖) atTop (𝓝 0) :=
  ⟨fun t => actualValue hDensity hSob hE q hσ F t (u t),
    actualValue_continuousOn hDensity hSob hE q hσ F u (Ici a) hu hNW,
    fun t ht => ⟨actualValue_same_value hDensity hSob hE q hσ F t (u t) (hNW t ht),
      actualValue_distribution hDensity hSob hE q hσ F t (u t) (hNW t ht)⟩,
    actualValue_norm_tendsto_zero hDensity hSob hE q hσ F u a B hNW hB⟩

end HartreeF.MassAsymptotics
