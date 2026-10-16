import FBoundedSpatialBounds
import HartreeGradientSingle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.BoundedHartreeGradient
open ForcingDomain GradientMajorants

/-- The differentiated outer-factor majorant has a genuine L1 bound for all orders. -/
theorem bounded_majorant1_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V Z : Space → ℝ) (M : ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp Z 2 volume → 0 ≤ M →
      (∀ᵐ x ∂volume, ‖V x‖ ≤ M) →
      RieszDomain α c (fun x => V x ^ (3 + α)) ∧
      SpatialBound (majorant1 α c V Z) 1
        ((C : ℝ) * M * spatialNorm 6 V ^ (3 + 2 * α) * spatialNorm 2 Z) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨C, hC⟩ := convolution_bound hH (s := (3 + α) / 6)
    (by linarith) (by linarith)
  refine ⟨C, fun V Z M hn h6 hZ hM hVM => ?_⟩
  obtain ⟨hd, hp⟩ := hC _ _ (spatialBound_power_six hn h6 (show 0 < 3 + α by linarith))
  have ho := spatialBound_power_six hn h6 hα
  have hz := spatialBound_self (q := 2) (by norm_num) (by simpa using hZ)
  have hb := spatialBound_mul_bounded ((hp.mul ho).mul hz) h6.aestronglyMeasurable hM hVM
  refine ⟨hd, ?_⟩
  convert hb using 1
  · funext x
    dsimp [majorant1]
    rw [Real.rpow_add' (hn x) (show 1 + α ≠ 0 by linarith), Real.rpow_one]
    ring
  · ring
  · have hE := spatialNorm_nonneg 6 V
    calc
      _ = (C : ℝ) * M *
          (spatialNorm 6 V ^ (3 + α) * spatialNorm 6 V ^ α) * spatialNorm 2 Z := by
        rw [← Real.rpow_add' hE (show 3 + α + α ≠ 0 by linarith)]
        congr 3
        ring
      _ = _ := by ring

/-- The actual differentiated density lies in the sharper HLS input space.
The single bounded factor is extracted without using a derivative L-infinity norm. -/
theorem bounded_density_gradient_majorant {α : ℝ} (hα : 0 < α)
    {V Z : Space → ℝ} {M : ℝ} (hn : ∀ x, 0 ≤ V x)
    (h6 : MemLp V 6 volume) (hZ : MemLp Z 2 volume) (hM : 0 ≤ M)
    (hVM : ∀ᵐ x ∂volume, ‖V x‖ ≤ M) :
    SpatialBound (fun x => V x ^ (2 + α) * Z x) ((4 + α) / 6)
      (M * spatialNorm 6 V ^ (1 + α) * spatialNorm 2 Z) := by
  have hv := spatialBound_power_six hn h6 (show 0 < 1 + α by linarith)
  have hz := spatialBound_self (q := 2) (by norm_num) (by simpa using hZ)
  have hb := spatialBound_mul_bounded (hv.mul hz) h6.aestronglyMeasurable hM hVM
  convert hb using 1
  · funext x
    have he : 2 + α = 1 + (1 + α) := by ring
    rw [he, Real.rpow_add' (hn x) (show 1 + (1 + α) ≠ 0 by linarith), Real.rpow_one]
    ring
  · ring
  · ring

/-- Direct strong-HLS density differentiation covers 0<alpha<=1, including alpha=1.
No HLS at order zero appears. -/
theorem bounded_majorant4_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) (hα1 : α ≤ 1) :
    ∃ C : ℝ≥0, ∀ (V Z : Space → ℝ) (M : ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp Z 2 volume → 0 ≤ M →
      (∀ᵐ x ∂volume, ‖V x‖ ≤ M) →
      RieszDomain α c (fun x => V x ^ (2 + α) * Z x) ∧
      SpatialBound (majorant4 α c V Z) 1
        ((C : ℝ) * M * spatialNorm 6 V ^ (3 + 2 * α) * spatialNorm 2 Z) := by
  have hα := hH.order_pos
  obtain ⟨C, hC⟩ := convolution_bound hH (s := (4 + α) / 6)
    (by linarith) (by linarith)
  refine ⟨C, fun V Z M hn h6 hZ hM hVM => ?_⟩
  obtain ⟨hd, hp⟩ := hC _ _ (bounded_density_gradient_majorant hα hn h6 hZ hM hVM)
  have ho := spatialBound_power_six hn h6 (show 0 < 2 + α by linarith)
  refine ⟨hd, ?_⟩
  convert hp.mul ho using 1
  · rfl
  · ring
  · have hE := spatialNorm_nonneg 6 V
    calc
      _ = (C : ℝ) * M *
          (spatialNorm 6 V ^ (1 + α) * spatialNorm 6 V ^ (2 + α)) * spatialNorm 2 Z := by
        rw [← Real.rpow_add' hE (show 1 + α + (2 + α) ≠ 0 by linarith)]
        congr 3
        ring
      _ = _ := by ring

end HartreeF.BoundedHartreeGradient
