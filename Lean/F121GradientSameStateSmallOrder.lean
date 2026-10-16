import FLowEnergyHartreeL1Gradient

/-!
Author candidate; exact native per-attempt receipts determine status. Preserve an arbitrary, genuine AE value bound of the same
physical lowEnergyState. The parameter A is not an independent Hartree estimate.
No relationship between A and a dyadic D_L has been established here.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct WeakHartreeChain GradientMajorants YoungSource

/-- The lower-order same-state estimate keeps the actual bounded-value number A.
A valid explicit choice is 12 * C0 * (K^(1/6))^(3+2*alpha), where C0 is obtained
from projected_forcing_gradient_L1_smallOrder before q, M, u and A are introduced.
The original state's scalar value is not assumed to lie in L2. -/
theorem lowEnergyState_forcing_L1_gradient_sameState_smallOrder
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState)
      (A : ℝ), 0 ≤ A →
      (∀ᵐ x ∂volume, ‖energyValue (lowEnergyState hDensity hSob q hM u) x‖ ≤ A) →
      let v := lowEnergyState hDensity hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * A * pureGradientNorm v ^ (4 + 2 * α) := by
  obtain ⟨C0, hC0, hC⟩ := projected_forcing_gradient_L1_smallOrder hH hα1
  let S := K ^ ((6 : ℝ)⁻¹)
  have hS : 0 ≤ S := Real.rpow_nonneg hSob.nonneg _
  let C := 12 * C0 * S ^ (3 + 2 * α)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q M hM u A hA0 hA
  let v := lowEnergyState hDensity hSob q hM u
  let N := pureGradientNorm v
  have hN : 0 ≤ N := pureGradientNorm_nonneg v
  have hα := hH.order_pos
  have hvN : pureGradientNorm v ≤ N := le_rfl
  have hE : spatialNorm 6 (fun x => ‖energyValue v x‖) ≤ S * N := by
    have he := (energyValue_le_pureGradient hSob v).trans (mul_le_mul_of_nonneg_left hvN hS)
    simpa [spatialNorm, eLpNorm_norm _ (Lp.aestronglyMeasurable _), ← Lp.norm_def] using he
  have hD : spatialNorm 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
      ‖energyProjectedGradient Complex.imCLM v x‖) ≤ 6 * N := by
    have hd := (energyProjectedGradient_norm_sum_le_six_pureGradient v).trans
      (mul_le_mul_of_nonneg_left hvN (by norm_num))
    simpa [spatialNorm] using hd
  have hE0 := spatialNorm_nonneg 6 (fun x => ‖energyValue v x‖)
  have hD0 := spatialNorm_nonneg 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
      ‖energyProjectedGradient Complex.imCLM v x‖)
  have hn : N ^ (4 + 2 * α) = N ^ (3 + 2 * α) * N := by
    rw [show 4 + 2 * α = (3 + 2 * α) + 1 by ring]
    exact Real.rpow_add_one' hN (by linarith)
  have hp (B : ℂ →L[ℝ] ℝ) (hB : ‖B‖ ≤ 1) :
      (eLpNorm (potentialProductGradient α c (projectedLocalFactor (1 + α) B)
        (energyValue v) (energyProjectedGradient Complex.reCLM v)
        (energyProjectedGradient Complex.imCLM v)) 1 volume).toReal ≤
      (6 * C0 * S ^ (3 + 2 * α)) * A * N ^ (4 + 2 * α) := by
    have hh := (hC B hB (energyValue v) (energyProjectedGradient Complex.reCLM v)
      (energyProjectedGradient Complex.imCLM v) A (Lp.memLp _)
      (lowEnergyState_memLp_ten hDensity hSob q hM u)
      (energyProjectedGradient_memLp Complex.reCLM v)
      (energyProjectedGradient_memLp Complex.imCLM v)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.reCLM q hM u)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.imCLM q hM u)
      hA0 hA).2
    calc
      _ ≤ C0 * A * spatialNorm 6 (fun x => ‖energyValue v x‖) ^ (3 + 2 * α) *
          spatialNorm 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
            ‖energyProjectedGradient Complex.imCLM v x‖) := hh
      _ ≤ C0 * A * (S * N) ^ (3 + 2 * α) * (6 * N) := by
        gcongr
      _ = _ := by
        rw [Real.mul_rpow hS hN, hn]
        ring
  have hr := hp Complex.reCLM reCLM_norm_le_one
  have hi := hp Complex.imCLM imCLM_norm_le_one
  simpa only [forcingGradientRe, forcingGradientIm] using
    (show _ ≤ C * A * N ^ (4 + 2 * α) from
      (add_le_add hr hi).trans_eq (by dsimp [C]; ring))

end HartreeF.BoundedHartreeGradient
