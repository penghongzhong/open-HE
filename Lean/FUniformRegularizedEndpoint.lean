import FActualCriticalPathRegularization
import FEndpointHartreeDuhamelOutput

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest EndpointOutput
open ForcingDomain TimeHolder

attribute [local irreducible] energySubmodule criticalPathSubmodule regularizeCriticalPath

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} {g : T → EnergyState}

/-- The endpoint field is the actual L6 Bessel multiplier applied to the
existing genuine L2_t L6_x field, not a new endpoint regularity premise. -/
def regularizeEndpointWitness (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B6 : OrdinaryBesselLp 6) (n : ℕ)
    (W : EndpointGradientWitness μ g) :
    EndpointGradientWitness μ (fun t => J hDensity hSob n (g t)) where
  field j := (B6.cutoffLp n).compLp (W.field j)
  agrees j := by
    filter_upwards [W.agrees j, (B6.cutoffLp n).coeFn_compLp (W.field j)] with t ht hc
    have hd : Lp.toTemperedDistribution (W.field j t) = energyGradientDistribution j (g t) := by
      ext φ
      change Lp.toTemperedDistribution (W.field j t) φ =
        Lp.toTemperedDistribution (energyGradient j (g t)) φ
      simp only [Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      exact ht.mono (fun x hx => congrArg (fun z : ℂ => φ x • z) hx)
    change ((B6.cutoffLp n).compLp (W.field j) t : V → ℂ) =ᵐ[volume] _
    rw [hc]
    exact (J_Lp_gradient_ae B6 hDensity hSob n (g t) j (W.field j t) hd).symm

/-- The same constant 2 works for every regularization index n. -/
theorem regularizeEndpointWitness_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B6 : OrdinaryBesselLp 6) (n : ℕ)
    (W : EndpointGradientWitness μ g) (j : Fin 3) :
    ‖(regularizeEndpointWitness hDensity hSob B6 n W).field j‖ ≤ 2 * ‖W.field j‖ := by
  have hb : ‖B6.cutoffLp n‖ ≤ 2 :=
    (B6.cutoffLp n).opNorm_le_bound (by norm_num) (B6.cutoffLp_bound n)
  exact ((B6.cutoffLp n).norm_compLp_le (W.field j)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem regularized_gradient_mixedNorm_uniform (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B6 : OrdinaryBesselLp 6) (n : ℕ)
    (W : EndpointGradientWitness μ g) (j : Fin 3) :
    mixedNorm μ volume 2 6 (fun t => energyGradient j (J hDensity hSob n (g t))) ≤
      2 * mixedNorm μ volume 2 6 (fun t => energyGradient j (g t)) := by
  rw [(regularizeEndpointWitness hDensity hSob B6 n W).mixedNorm_eq j, W.mixedNorm_eq j]
  have h := ENNReal.ofReal_le_ofReal (regularizeEndpointWitness_norm_le hDensity hSob B6 n W j)
  simpa only [ofReal_norm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] using h

/-- Actual full endpoint membership survives actual critical-graph smoothing. -/
theorem regularizeCriticalPath_fullZ (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (Bw : OrdinaryBesselLp criticalExponent)
    (B6 : OrdinaryBesselLp 6) (n : ℕ) (u : CriticalPath (intervalMeasure a b))
    (hu : FullZPath u) :
    FullZPath (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u) := by
  obtain ⟨W⟩ := hu
  let R := regularizeEndpointWitness hDensity hSob B6 n W
  refine ⟨⟨R.field, ?_⟩⟩
  intro j
  filter_upwards [R.agrees j] with t ht
  rw [regularizeCriticalPath_energy]
  exact ht

#print axioms regularizeEndpointWitness
#print axioms regularizeEndpointWitness_norm_le
#print axioms regularized_gradient_mixedNorm_uniform
#print axioms regularizeCriticalPath_fullZ
end HartreeF.Regularization.Actual
