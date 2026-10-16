import FBoundedHartreeGradientUpperOrder
import FLowEnergyHartreeWeakGradient
import FEnergyProjectedGradientNorm

/-!
UNCOMPILED DRAFT. The state is the previously defined physical fixed-cutoff
lowEnergyState. All fields are its canonical projected gradients. No L2
value of the original state, finite variance, or independent gradient field
is assumed.
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

/-- The actual upper-order low-state forcing has its existing L1 weak gradients. -/
theorem lowEnergyState_forcing_L1_weakGradients_upperOrder
    (hDensity : OrdinaryH1Density) {K α c c' : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c) (hLowerHLS : OrdinaryHLS (α - 1) c')
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    let v := lowEnergyState hDensity hSob q hL u
    let U := energyProjectedGradient Complex.reCLM v
    let V := energyProjectedGradient Complex.imCLM v
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
      (forcingGradientRe α c (energyValue v) U V) ∧
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
      (forcingGradientIm α c (energyValue v) U V) ∧
    MemLp (forcingGradientRe α c (energyValue v) U V) 1 volume ∧
    MemLp (forcingGradientIm α c (energyValue v) U V) 1 volume := by
  let v := lowEnergyState hDensity hSob q hL u
  have hw := lowEnergyState_forcing_hasWeakGradients hDensity hSob hH q hL u
  obtain ⟨C, _, hC⟩ := projected_forcing_gradient_L1_upperOrder hDensity hH hLowerHLS
  let M := cutoffYoungConstant q * Real.sqrt L * ‖energyValue u‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg L)) (norm_nonneg _)
  have hb : ∀ᵐ x ∂volume, ‖energyValue v x‖ ≤ M := by
    filter_upwards [lowPhysical_same_value hDensity hSob q hL u] with x hx
    rw [← hx]
    exact lowPhysical_bound q hL u x
  have hdom (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) :=
    hC A hA (energyValue v) (energyProjectedGradient Complex.reCLM v)
      (energyProjectedGradient Complex.imCLM v) M (energyState_inDotH1 v)
      (lowEnergyState_memLp_ten hDensity hSob q hL u)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.reCLM q hL u)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.imCLM q hL u)
      hM hb
  exact ⟨hw.1, hw.2, (hdom Complex.reCLM reCLM_norm_le_one).1,
    (hdom Complex.imCLM imCLM_norm_le_one).1⟩

/-- The full upper-order numerical bound uses the original state's pure
coordinate-gradient norm only. The constant is independent of q, L and u. -/
theorem lowEnergyState_forcing_L1_gradient_bound_upperOrder
    (hDensity : OrdinaryH1Density) {K α c c' : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c) (hLowerHLS : OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (L : ℝ) (hL : 0 < L) (u : EnergyState),
      let v := lowEnergyState hDensity hSob q hL u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * cutoffYoungConstant q * Real.sqrt L * pureGradientNorm u ^ (5 + 2 * α) := by
  obtain ⟨C0, hC0, hC⟩ := projected_forcing_gradient_L1_upperOrder hDensity hH hLowerHLS
  let S := K ^ ((6 : ℝ)⁻¹)
  have hS : 0 ≤ S := Real.rpow_nonneg hSob.nonneg _
  let P := C0 * (S ^ (5 + 2 * α) + 6 * S ^ (4 + 2 * α))
  let C := 2 * P
  refine ⟨C, by dsimp [C, P]; positivity, ?_⟩
  intro q L hL u
  let v := lowEnergyState hDensity hSob q hL u
  let N := pureGradientNorm u
  let M := cutoffYoungConstant q * Real.sqrt L * S * N
  have hN : 0 ≤ N := pureGradientNorm_nonneg u
  have hq : 0 ≤ cutoffYoungConstant q := cutoffYoungConstant_nonneg q
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hα := hH.order_pos
  have hvN : pureGradientNorm v ≤ N := lowEnergyState_pureGradient_bound hDensity hSob q hL u
  have hE : spatialNorm 6 (fun x => ‖energyValue v x‖) ≤ S * N := by
    have he := (energyValue_le_pureGradient hSob v).trans (mul_le_mul_of_nonneg_left hvN hS)
    simpa [spatialNorm, eLpNorm_norm _ (Lp.aestronglyMeasurable _), ← Lp.norm_def] using he
  have hD : spatialNorm 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
      ‖energyProjectedGradient Complex.imCLM v x‖) ≤ 6 * N := by
    have hd := (energyProjectedGradient_norm_sum_le_six_pureGradient v).trans
      (mul_le_mul_of_nonneg_left hvN (by norm_num))
    simpa [spatialNorm] using hd
  have hb : ∀ᵐ x ∂volume, ‖energyValue v x‖ ≤ M := by
    filter_upwards [lowPhysical_same_value hDensity hSob q hL u] with x hx
    rw [← hx]
    exact lowPhysical_pureGradient_bound hSob q hL u x
  have hE0 := spatialNorm_nonneg 6 (fun x => ‖energyValue v x‖)
  have hD0 := spatialNorm_nonneg 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
      ‖energyProjectedGradient Complex.imCLM v x‖)
  have hs4 : S ^ (4 + 2 * α) = S ^ (3 + 2 * α) * S := by
    rw [show 4 + 2 * α = (3 + 2 * α) + 1 by ring]
    exact Real.rpow_add_one' hS (by linarith)
  have hs5 : S ^ (5 + 2 * α) = S ^ (3 + 2 * α) * S ^ 2 := by
    calc
      _ = S ^ ((3 + 2 * α) + 2) := by congr 1; ring
      _ = S ^ (3 + 2 * α) * S ^ (2 : ℝ) := Real.rpow_add' hS (by linarith)
      _ = _ := by rw [Real.rpow_two]
  have hn4 : N ^ (4 + 2 * α) = N ^ (3 + 2 * α) * N := by
    rw [show 4 + 2 * α = (3 + 2 * α) + 1 by ring]
    exact Real.rpow_add_one' hN (by linarith)
  have hn5 : N ^ (5 + 2 * α) = N ^ (3 + 2 * α) * N ^ 2 := by
    calc
      _ = N ^ ((3 + 2 * α) + 2) := by congr 1; ring
      _ = N ^ (3 + 2 * α) * N ^ (2 : ℝ) := Real.rpow_add' hN (by linarith)
      _ = _ := by rw [Real.rpow_two]
  have hp (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) :
      (eLpNorm (potentialProductGradient α c (projectedLocalFactor (1 + α) A)
        (energyValue v) (energyProjectedGradient Complex.reCLM v)
        (energyProjectedGradient Complex.imCLM v)) 1 volume).toReal ≤
      P * cutoffYoungConstant q * Real.sqrt L * N ^ (5 + 2 * α) := by
    have hh := (hC A hA (energyValue v) (energyProjectedGradient Complex.reCLM v)
      (energyProjectedGradient Complex.imCLM v) M (energyState_inDotH1 v)
      (lowEnergyState_memLp_ten hDensity hSob q hL u)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.reCLM q hL u)
      (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.imCLM q hL u)
      hM hb).2
    calc
      _ ≤ C0 * M * spatialNorm 6 (fun x => ‖energyValue v x‖) ^ (4 + 2 * α) +
          C0 * M * spatialNorm 6 (fun x => ‖energyValue v x‖) ^ (3 + 2 * α) *
            spatialNorm 2 (fun x => ‖energyProjectedGradient Complex.reCLM v x‖ +
              ‖energyProjectedGradient Complex.imCLM v x‖) := hh
      _ ≤ C0 * M * (S * N) ^ (4 + 2 * α) +
          C0 * M * (S * N) ^ (3 + 2 * α) * (6 * N) := by
        gcongr
      _ = _ := by
        dsimp [M, P]
        simp only [Real.mul_rpow hS hN, hs4, hs5, hn4, hn5]
        ring
  have hr := hp Complex.reCLM reCLM_norm_le_one
  have hi := hp Complex.imCLM imCLM_norm_le_one
  simpa only [forcingGradientRe, forcingGradientIm] using
    (show _ ≤ C * cutoffYoungConstant q * Real.sqrt L * N ^ (5 + 2 * α) from
      (add_le_add hr hi).trans_eq (by dsimp [C]; ring))

#print axioms lowEnergyState_forcing_L1_weakGradients_upperOrder
#print axioms lowEnergyState_forcing_L1_gradient_bound_upperOrder
end HartreeF.BoundedHartreeGradient
