import GradientLpBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.GradientMajorants
open ForcingDomain

/-- The first literal nonnegative majorant in the weak-gradient difference formula. -/
def majorant1 (α c : ℝ) (V Z : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (3+α)) x * V x ^ (1+α) * Z x

/-- The fourth literal nonnegative majorant in the weak-gradient difference formula. -/
def majorant4 (α c : ℝ) (V Z : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (2+α) * Z y) x * V x ^ (2+α)

/-- Actual absolute Bochner-integrability of the defining convolution, almost everywhere. -/
def RieszDomain (α c : ℝ) (f : Space → ℝ) : Prop :=
  ∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) * f y) volume

/-- First strong HLS input reciprocal exponent. -/
def reciprocalA (α : ℝ) : ℝ := (9+7*α)/30
/-- Second strong HLS input reciprocal exponent. -/
def reciprocalB (α : ℝ) : ℝ := (57+11*α)/90

theorem gradient_hls_ranges {α : ℝ} (_hα : 0 < α) (hα3 : α < 3) :
    α/3 < reciprocalA α ∧ reciprocalA α < 1 ∧
    α/3 < reciprocalB α ∧ reciprocalB α < 1 := by
  dsimp [reciprocalA, reciprocalB]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The exact inner first allocation: E^(2 alpha) S^(3-alpha). -/
theorem first_density_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {V : Space → ℝ} (hn : ∀ x, 0 ≤ V x)
    (h6 : MemLp V 6 volume) (h10 : MemLp V 10 volume) :
    SpatialBound (fun x => V x ^ (3+α)) (reciprocalA α)
      (spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (3-α)) := by
  convert split_power_bound hn h6 h10 (show 0 < 2*α by positivity)
    (show 0 < 3-α by linarith) using 1
  · ring_nf
  · dsimp [reciprocalA]
    ring_nf

/-- The exact second inner allocation, including its genuine derivative L^(30/13) input. -/
theorem second_density_bound {α : ℝ} (hα : 0 < α) (_hα3 : α < 3)
    {V Y : Space → ℝ} (hn : ∀ x, 0 ≤ V x)
    (h6 : MemLp V 6 volume) (h10 : MemLp V 10 volume)
    (hY : MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume) :
    SpatialBound (fun x => V x ^ (2+α) * Y x) (reciprocalB α)
      (spatialNorm 6 V ^ (α/3) * spatialNorm 10 V ^ (2+2*α/3) * spatialNorm (30/13) Y) := by
  have hv := split_power_bound hn h6 h10 (show 0 < α/3 by positivity)
    (show 0 < 2+2*α/3 by linarith)
  have hy := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) hY
  convert hv.mul hy using 1
  · ext x
    congr 2
    ring_nf
  · dsimp [reciprocalB]
    ring_nf

/-- T1 has its actual convolution domain and a finite critical L^(6/5) bound.
No weak-gradient identity is asserted or assumed by this theorem. -/
theorem majorant1_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V Z : Space → ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp V 10 volume →
      MemLp Z (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (3+α)) ∧
      SpatialBound (majorant1 α c V Z) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (4 : ℝ) *
          spatialNorm (30/13) Z) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨ha,ha1,_,_⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH ha ha1
  refine ⟨C, fun V Z hn h6 h10 hZ => ?_⟩
  obtain ⟨hd,hp⟩ := hC _ _ (first_density_bound hα hα3 hn h6 h10)
  have ho := spacetime_power_bound hn h10 (show 0 < 1+α by linarith)
  have hz := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) hZ
  refine ⟨hd, ?_⟩
  convert (hp.mul ho).mul hz using 1
  · rfl
  · dsimp [reciprocalA]
    ring_nf
  · symm
    have hS := spatialNorm_nonneg 10 V
    calc
      _ = (C : ℝ) * spatialNorm 6 V ^ (2*α) *
          (spatialNorm 10 V ^ (3-α) * spatialNorm 10 V ^ (1+α)) * spatialNorm (30/13) Z := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' hS (show 3-α+(1+α) ≠ 0 by ring_nf; norm_num)]
        congr 3
        ring_nf

/-- T4 has its actual convolution domain and the same full-range critical bound. -/
theorem majorant4_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V Z : Space → ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp V 10 volume →
      MemLp Z (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (2+α) * Z x) ∧
      SpatialBound (majorant4 α c V Z) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (4 : ℝ) *
          spatialNorm (30/13) Z) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨_,_,hb,hb1⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH hb hb1
  refine ⟨C, fun V Z hn h6 h10 hZ => ?_⟩
  obtain ⟨hd,hp⟩ := hC _ _ (second_density_bound hα hα3 hn h6 h10 hZ)
  have ho := split_power_bound hn h6 h10 (show 0 < 5*α/3 by positivity)
    (show 0 < 2-2*α/3 by linarith)
  refine ⟨hd, ?_⟩
  convert hp.mul ho using 1
  · ext x
    dsimp [majorant4]
    congr 2
    ring_nf
  · dsimp [reciprocalB]
    ring_nf
  · symm
    have hE := spatialNorm_nonneg 6 V
    have hS := spatialNorm_nonneg 10 V
    calc
      _ = (C : ℝ) * (spatialNorm 6 V ^ (α/3) * spatialNorm 6 V ^ (5*α/3)) *
          (spatialNorm 10 V ^ (2+2*α/3) * spatialNorm 10 V ^ (2-2*α/3)) *
          spatialNorm (30/13) Z := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' hE (by linarith : α/3+5*α/3 ≠ 0),
          ← Real.rpow_add' hS (by linarith : 2+2*α/3+(2-2*α/3) ≠ 0)]
        congr 3 <;> ring_nf

end HartreeF.GradientMajorants
