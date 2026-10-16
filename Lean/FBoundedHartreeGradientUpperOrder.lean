import FUpperHartreeKernelGradient

/-! UNCOMPILED DRAFT: actual projected forcing gradients for 1 < alpha < 3. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.BoundedHartreeGradient
open ForcingDomain GradientMajorants RieszWeakDerivative WeakHartreeChain
  WeakHartreeProduct SobolevStretch StationarySelfTest

/-- Majorization of the actual, previously defined projected forcing gradient. -/
theorem projected_forcing_gradient_majorant_upperOrder
    (hDensity : OrdinaryH1Density) {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c')
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume) :
    ∀ᵐ x ∂volume,
      ‖potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V x‖ ≤
      upperKernelMajorant α c c' (fun y => ‖u y‖) x +
        (3 * (2 + α)) * majorant1 α c (fun y => ‖u y‖) (fun y => ‖U y‖ + ‖V y‖) x := by
  have hb := localFactor_growth_bounds hH.order_pos A hA
  filter_upwards [fourthGradientMagnitude_le_upperKernelMajorant
    hDensity hH hL hu hu10 hU hV] with x hx
  apply (potentialProductGradient_norm_bound (c := c) hb.1 hb.2 u U V x).trans
  unfold gradientMagnitude
  rw [firstGradientMagnitude_eq_majorant hH.normalization_pos.le]
  exact add_le_add hx le_rfl

/-- The precise normalization ratio is visible in the sharper kernel term.
The second term is the unchanged local differentiation estimate. -/
theorem projected_forcing_gradient_L1_upperOrder_exact
    (hDensity : OrdinaryH1Density) {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c') :
    ∃ Ck Cl : ℝ≥0, ∀ (A : ℂ →L[ℝ] ℝ), ‖A‖ ≤ 1 →
      ∀ (u : Space → ℂ) (U V : Space → Space) (M : ℝ),
      InDotH1 u U V → MemLp u 10 volume →
      MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      0 ≤ M → (∀ᵐ x ∂volume, ‖u x‖ ≤ M) →
      MemLp (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume ∧
      (eLpNorm (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume).toReal ≤
        ((c * (3 - α) / c') * (Ck : ℝ)) * M * spatialNorm 6 (fun x => ‖u x‖) ^ (4 + 2 * α) +
        ((3 * (2 + α)) * (Cl : ℝ)) * M * spatialNorm 6 (fun x => ‖u x‖) ^ (3 + 2 * α) *
          spatialNorm 2 (fun x => ‖U x‖ + ‖V x‖) := by
  obtain ⟨Ck, hCk⟩ := upperKernelMajorant_domain_bound hH hL
  obtain ⟨Cl, hCl⟩ := bounded_majorant1_domain_bound hH
  refine ⟨Ck, Cl, ?_⟩
  intro A hA u U V M hu hu10 hU hV hM huM
  have hα := hH.order_pos
  have hZ : MemLp (fun x => ‖U x‖ + ‖V x‖) 2 volume :=
    hu.real_gradient_L2.norm.add hu.imag_gradient_L2.norm
  have hn : ∀ x, 0 ≤ ‖u x‖ := fun x => norm_nonneg _
  have hnM : ∀ᵐ x ∂volume, ‖‖u x‖‖ ≤ M := by simpa only [norm_norm] using huM
  obtain ⟨_, hk⟩ := hCk _ M hn hu.function_L6.norm hM hnM
  obtain ⟨_, hl⟩ := hCl _ _ M hn hu.function_L6.norm hZ hM hnM
  have hb := hk.add (spatialBound_const_mul hl (show 0 ≤ 3 * (2 + α) by positivity))
    (by norm_num)
  have hm := potentialProductGradient_aestronglyMeasurable hH
    (projectedLocalFactor_contDiff_one (by linarith : 1 < 1 + α) A)
    hu.function_L6 hu10 hU hV
  have hr := memLp_one_bound_of_majorant hb hm
    (projected_forcing_gradient_majorant_upperOrder hDensity hH hL A hA hu hu10 hU hV)
  refine ⟨hr.1, ?_⟩
  convert hr.2 using 1
  ring

/-- A one-constant form convenient for the fixed-cutoff physical low-state.
The exact coefficient remains available in the preceding theorem. -/
theorem projected_forcing_gradient_L1_upperOrder
    (hDensity : OrdinaryH1Density) {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℂ →L[ℝ] ℝ), ‖A‖ ≤ 1 →
      ∀ (u : Space → ℂ) (U V : Space → Space) (M : ℝ),
      InDotH1 u U V → MemLp u 10 volume →
      MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      0 ≤ M → (∀ᵐ x ∂volume, ‖u x‖ ≤ M) →
      MemLp (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume ∧
      (eLpNorm (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume).toReal ≤
        C * M * spatialNorm 6 (fun x => ‖u x‖) ^ (4 + 2 * α) +
        C * M * spatialNorm 6 (fun x => ‖u x‖) ^ (3 + 2 * α) *
          spatialNorm 2 (fun x => ‖U x‖ + ‖V x‖) := by
  obtain ⟨Ck, Cl, hC⟩ := projected_forcing_gradient_L1_upperOrder_exact hDensity hH hL
  let X : ℝ := (c * (3 - α) / c') * Ck
  let Y : ℝ := (3 * (2 + α)) * Cl
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg
      (div_nonneg (mul_nonneg hH.normalization_pos.le (by linarith [hH.order_lt_three]))
        hL.normalization_pos.le) Ck.coe_nonneg
  have hα := hH.order_pos
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  refine ⟨X + Y, add_nonneg hX hY, ?_⟩
  intro A hA u U V M hu hu10 hU hV hM huM
  obtain ⟨hm, hb⟩ := hC A hA u U V M hu hu10 hU hV hM huM
  refine ⟨hm, hb.trans ?_⟩
  change X * M * _ + Y * M * _ * _ ≤ _
  have hEk := Real.rpow_nonneg (spatialNorm_nonneg 6 (fun x => ‖u x‖)) (4 + 2 * α)
  have hEl := Real.rpow_nonneg (spatialNorm_nonneg 6 (fun x => ‖u x‖)) (3 + 2 * α)
  have hD0 := spatialNorm_nonneg 2 (fun x => ‖U x‖ + ‖V x‖)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hY) hM) hEk
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hX) hM) hEl) hD0

#print axioms projected_forcing_gradient_L1_upperOrder_exact
#print axioms projected_forcing_gradient_L1_upperOrder
end HartreeF.BoundedHartreeGradient
