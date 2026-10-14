import HartreeGradientSingle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.GradientMajorants
open ForcingDomain

def theta (α : ℝ) : ℝ := (3-α)/3

def majorant2 (α c : ℝ) (V W Y : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (2+α) * W y) x * V x ^ (1+α) * Y x

def majorant3 (α c : ℝ) (V W Y : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (3+α)) x * V x ^ α * W x * Y x

def majorant5 (α c : ℝ) (V W Y : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (1+α) * W y * Y y) x * V x ^ (2+α)

def majorant6 (α c : ℝ) (V W Y : Space → ℝ) : Space → ℝ :=
  fun x => rieszConvolution α c (fun y => V y ^ (2+α) * Y y) x * V x ^ (1+α) * W x

/-- T3: replace one outer spacetime power by the L10 difference. -/
theorem majorant3_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V W Y : Space → ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp V 10 volume → MemLp W 10 volume →
      MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (3+α)) ∧
      SpatialBound (majorant3 α c V W Y) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (3 : ℝ) *
          spatialNorm (30/13) Y * spatialNorm 10 W) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨ha,ha1,_,_⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH ha ha1
  refine ⟨C, fun V W Y hn h6 h10 hW hY => ?_⟩
  obtain ⟨hd,hp⟩ := hC _ _ (first_density_bound hα hα3 hn h6 h10)
  have ho := spacetime_power_bound hn h10 hα
  have hw := spatialBound_self (q := 10) (by norm_num) (by simpa using hW)
  have hy := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) hY
  refine ⟨hd, ?_⟩
  convert ((hp.mul ho).mul hw).mul hy using 1
  · rfl
  · dsimp [reciprocalA]
    ring_nf
  · symm
    calc
      _ = (C : ℝ) * spatialNorm 6 V ^ (2*α) *
          (spatialNorm 10 V ^ (3-α) * spatialNorm 10 V ^ α) *
          spatialNorm (30/13) Y * spatialNorm 10 W := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' (spatialNorm_nonneg 10 V) (by linarith : 3-α+α ≠ 0)]
        congr 4
        ring_nf

/-- T5: replace one inner spacetime power by the L10 difference. -/
theorem majorant5_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V W Y : Space → ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp V 10 volume → MemLp W 10 volume →
      MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (1+α) * W x * Y x) ∧
      SpatialBound (majorant5 α c V W Y) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (3 : ℝ) *
          spatialNorm (30/13) Y * spatialNorm 10 W) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨_,_,hb,hb1⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH hb hb1
  refine ⟨C, fun V W Y hn h6 h10 hW hY => ?_⟩
  have hv := split_power_bound hn h6 h10 (show 0 < α/3 by positivity)
    (show 0 < 1+2*α/3 by linarith)
  have hw := spatialBound_self (q := 10) (by norm_num) (by simpa using hW)
  have hy := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) hY
  have hi : SpatialBound (fun x => V x ^ (1+α) * W x * Y x) (reciprocalB α)
      (spatialNorm 6 V ^ (α/3) * spatialNorm 10 V ^ (1+2*α/3) *
        spatialNorm 10 W * spatialNorm (30/13) Y) := by
    convert (hv.mul hw).mul hy using 1
    · ext x
      congr 3
      ring_nf
    · dsimp [reciprocalB]
      ring_nf
  obtain ⟨hd,hp⟩ := hC _ _ hi
  have ho := split_power_bound hn h6 h10 (show 0 < 5*α/3 by positivity)
    (show 0 < 2-2*α/3 by linarith)
  refine ⟨hd, ?_⟩
  convert hp.mul ho using 1
  · ext x
    dsimp [majorant5]
    congr 2
    ring_nf
  · dsimp [reciprocalB]
    ring_nf
  · symm
    calc
      _ = (C : ℝ) * (spatialNorm 6 V ^ (α/3) * spatialNorm 6 V ^ (5*α/3)) *
          (spatialNorm 10 V ^ (1+2*α/3) * spatialNorm 10 V ^ (2-2*α/3)) *
          spatialNorm (30/13) Y * spatialNorm 10 W := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' (spatialNorm_nonneg 6 V) (by linarith : α/3+5*α/3 ≠ 0),
          ← Real.rpow_add' (spatialNorm_nonneg 10 V) (by linarith : 1+2*α/3+(2-2*α/3) ≠ 0)]
        congr 4 <;> ring_nf

/-- The exact mixed difference allocation, including zero factors. -/
theorem difference_power_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {W : Space → ℝ} (hn : ∀ x, 0 ≤ W x)
    (h6 : MemLp W 6 volume) (h10 : MemLp W 10 volume) :
    SpatialBound W (α/18+theta α/10)
      (spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α) := by
  have ht : 0 < theta α := by dsimp [theta]; linarith
  convert split_power_bound hn h6 h10 (show 0 < α/3 by positivity) ht using 1
  · ext x
    rw [show α/3+theta α = 1 by dsimp [theta]; ring_nf, Real.rpow_one]
  · ring_nf

/-- T2: the difference uses the exact energy alpha/3 and spacetime theta shares. -/
theorem majorant2_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V W Y : Space → ℝ), (∀ x, 0 ≤ V x) → (∀ x, 0 ≤ W x) →
      MemLp V 6 volume → MemLp V 10 volume → MemLp W 6 volume → MemLp W 10 volume →
      MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (2+α) * W x) ∧
      SpatialBound (majorant2 α c V W Y) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (4-theta α) *
          spatialNorm (30/13) Y * spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨ha,ha1,_,_⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH ha ha1
  refine ⟨C, fun V W Y hnV hnW h6 h10 hW6 hW10 hY => ?_⟩
  have hv := split_power_bound hnV h6 h10 (show 0 < 5*α/3 by positivity)
    (show 0 < 2-2*α/3 by linarith)
  have hw := difference_power_bound hα hα3 hnW hW6 hW10
  have hi : SpatialBound (fun x => V x ^ (2+α) * W x) (reciprocalA α)
      ((spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (2-2*α/3)) *
        (spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α)) := by
    convert hv.mul hw using 1
    · ext x
      congr 2
      ring_nf
    · dsimp [reciprocalA, theta]
      ring_nf
  obtain ⟨hd,hp⟩ := hC _ _ hi
  have ho := spacetime_power_bound hnV h10 (show 0 < 1+α by linarith)
  have hy := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) hY
  refine ⟨hd, ?_⟩
  convert (hp.mul ho).mul hy using 1
  · rfl
  · dsimp [reciprocalA]
    ring_nf
  · symm
    calc
      _ = (C : ℝ) * spatialNorm 6 V ^ (5*α/3) *
          (spatialNorm 10 V ^ (2-2*α/3) * spatialNorm 10 V ^ (1+α)) *
          spatialNorm (30/13) Y * spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' (spatialNorm_nonneg 10 V) (by linarith : 2-2*α/3+(1+α) ≠ 0)]
        congr 5
        dsimp [theta]
        ring_nf

/-- T6: the outer mixed difference allocation uses the same strong HLS input as T4. -/
theorem majorant6_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V W Y : Space → ℝ), (∀ x, 0 ≤ V x) → (∀ x, 0 ≤ W x) →
      MemLp V 6 volume → MemLp V 10 volume → MemLp W 6 volume → MemLp W 10 volume →
      MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (2+α) * Y x) ∧
      SpatialBound (majorant6 α c V W Y) (5/6)
        ((C : ℝ) * spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (4-theta α) *
          spatialNorm (30/13) Y * spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  have ht : 0 < theta α := by dsimp [theta]; linarith
  obtain ⟨_,_,hb,hb1⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH hb hb1
  refine ⟨C, fun V W Y hnV hnW h6 h10 hW6 hW10 hY => ?_⟩
  obtain ⟨hd,hp⟩ := hC _ _ (second_density_bound hα hα3 hnV h6 h10 hY)
  have hv := split_power_bound hnV h6 h10 (show 0 < 4*α/3 by positivity) ht
  have hw := difference_power_bound hα hα3 hnW hW6 hW10
  refine ⟨hd, ?_⟩
  convert (hp.mul hv).mul hw using 1
  · ext x
    dsimp [majorant6]
    congr 3
    dsimp [theta]
    ring_nf
  · dsimp [reciprocalB, theta]
    ring_nf
  · symm
    calc
      _ = (C : ℝ) * (spatialNorm 6 V ^ (α/3) * spatialNorm 6 V ^ (4*α/3)) *
          (spatialNorm 10 V ^ (2+2*α/3) * spatialNorm 10 V ^ theta α) *
          spatialNorm (30/13) Y * spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α := by ring_nf
      _ = _ := by
        rw [← Real.rpow_add' (spatialNorm_nonneg 6 V) (by linarith : α/3+4*α/3 ≠ 0),
          ← Real.rpow_add' (spatialNorm_nonneg 10 V) (by dsimp [theta]; linarith : 2+2*α/3+theta α ≠ 0)]
        dsimp [theta]
        congr 5 <;> ring_nf

end HartreeF.GradientMajorants
