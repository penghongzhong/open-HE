import FFinitePowerDefects
import FLocalProductHolder

/-!
Finite-profile local defects in genuine extended mixed spaces. Author source,
UNCOMPILED. Zero powers are eliminated algebraically before Hölder: no constant
function is ever placed in a finite Lp space on infinite-volume space-time.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteProfileMixedDefects
open TimeHolder ProfileApproximation GeneralProfileCross LocalProfileProducts
open WeakHartreeChain FinitePowerDefects

/-- Unlike `ofReal s⁻¹`, this convention sends reciprocal zero to infinity. -/
def reciprocal (s : ℝ) : ℝ≥0∞ := (ENNReal.ofReal s)⁻¹

@[simp] theorem reciprocal_zero : reciprocal 0 = ∞ := by simp [reciprocal]

theorem reciprocal_ne_zero (s : ℝ) : reciprocal s ≠ 0 := by simp [reciprocal]

theorem reciprocal_ne_top {s : ℝ} (hs : 0 < s) : reciprocal s ≠ ∞ := by
  simp [reciprocal, ne_of_gt (ENNReal.ofReal_pos.mpr hs)]

theorem reciprocal_eq {s : ℝ} (hs : 0 < s) :
    reciprocal s = ENNReal.ofReal s⁻¹ := by
  exact (ENNReal.ofReal_inv_of_pos hs).symm

theorem reciprocal_holder {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.HolderTriple (reciprocal a) (reciprocal b) (reciprocal (a+b)) := by
  constructor
  simp only [reciprocal, inv_inv, ← ENNReal.ofReal_add ha hb]

theorem reciprocal_mul_ofReal {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    reciprocal (s*d) * ENNReal.ofReal d = reciprocal s := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp [reciprocal, ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr hd))]
  rw [reciprocal_eq (mul_pos hs hd), reciprocal_eq hs,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg hs.le hd.le))]
  congr 1
  field_simp [ne_of_gt hs, ne_of_gt hd]

/-- Both finite and essential-supremum time exponents supply genuine spatial domains. -/
theorem mixed_ae_slice {E : Type*} [NormedAddCommGroup E]
    {p q : ℝ≥0∞} (hp : p ≠ 0) (f : ℝ → Space → E)
    (hf : mixedNorm volume volume p q f ≠ ∞) :
    ∀ᵐ t ∂volume, MemLp (f t) q volume := by
  by_cases hpt : p = ∞
  · subst p
    exact finite_top_mixedNorm_ae_slice q f hf
  · exact finite_mixedNorm_ae_slice_memLp volume volume p q hp hpt f hf

/-- General two-step Hölder. Time exponents may equal infinity. All spatial
`toReal` operations occur only after both actual spatial norms are finite. -/
theorem mixed_normProduct_le {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {p₁ p₂ p q₁ q₂ q : ℝ≥0∞}
    [ENNReal.HolderTriple p₁ p₂ p] [ENNReal.HolderTriple q₁ q₂ q]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hq₁ : q₁ ≠ 0) (hq₁T : q₁ ≠ ∞) (hq₂ : q₂ ≠ 0) (hq₂T : q₂ ≠ ∞)
    (hq : q ≠ 0) (hqT : q ≠ ∞)
    (f : ℝ → Space → E) (g : ℝ → Space → F)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume))
    (hff : mixedNorm volume volume p₁ q₁ f ≠ ∞)
    (hgf : mixedNorm volume volume p₂ q₂ g ≠ ∞) :
    mixedNorm volume volume p q (normProduct f g) ≤
      mixedNorm volume volume p₁ q₁ f * mixedNorm volume volume p₂ q₂ g := by
  let A : ℝ → ℝ := fun t => (eLpNorm (f t) q₁ volume).toReal
  let B : ℝ → ℝ := fun t => (eLpNorm (g t) q₂ volume).toReal
  have hmA := spatial_lp_time_toReal_measurable volume volume q₁ hq₁ hq₁T f hf
  have hmB := spatial_lp_time_toReal_measurable volume volume q₂ hq₂ hq₂T g hg
  have hsA := mixed_ae_slice hp₁ f hff
  have hsB := mixed_ae_slice hp₂ g hgf
  have hmP : AEStronglyMeasurable (fun z : ℝ × Space => normProduct f g z.1 z.2)
      (volume.prod volume) := hf.norm.mul hg.norm
  have hslice : ∀ᵐ t ∂volume, eLpNorm (normProduct f g t) q volume ≤ ‖A t * B t‖ₑ := by
    filter_upwards [hsA,hsB] with t hft hgt
    have hh := temporal_real_product_norm (p := q₁) (q := q₂) (r := q) volume
      (fun x => ‖f t x‖) (fun x => ‖g t x‖)
      hft.aestronglyMeasurable.norm hgt.aestronglyMeasurable.norm
    rw [eLpNorm_norm _ hft.aestronglyMeasurable, eLpNorm_norm _ hgt.aestronglyMeasurable] at hh
    change eLpNorm (normProduct f g t) q volume ≤ _ at hh
    simpa only [A,B,Real.enorm_eq_ofReal (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hft.eLpNorm_ne_top,
      ENNReal.ofReal_toReal hgt.eLpNorm_ne_top] using hh
  calc
    mixedNorm volume volume p q (normProduct f g) ≤ eLpNorm (fun t => A t * B t) p volume := by
      apply eLpNorm_mono_enorm_ae (spatial_lp_time_measurable volume volume q hq hqT _ hmP)
      simpa only [enorm_eq_self] using hslice
    _ ≤ eLpNorm A p₁ volume * eLpNorm B p₂ volume := temporal_real_product_norm volume A B hmA hmB
    _ = _ := by
      rw [real_slice_mixed_eq volume p₁ q₁ hq₁ hq₁T f hf hsA,
        real_slice_mixed_eq volume p₂ q₂ hq₂ hq₂T g hg hsB]

/-- Literal real or complex multiplication, for downstream HLS/Holder consumers. -/
theorem mixed_mul_le {E : Type*} [NormedRing E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {p₁ p₂ p q₁ q₂ q : ℝ≥0∞}
    [ENNReal.HolderTriple p₁ p₂ p] [ENNReal.HolderTriple q₁ q₂ q]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hq₁ : q₁ ≠ 0) (hq₁T : q₁ ≠ ∞) (hq₂ : q₂ ≠ 0) (hq₂T : q₂ ≠ ∞)
    (hq : q ≠ 0) (hqT : q ≠ ∞)
    (f g : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume))
    (hff : mixedNorm volume volume p₁ q₁ f ≠ ∞)
    (hgf : mixedNorm volume volume p₂ q₂ g ≠ ∞) :
    mixedNorm volume volume p q (fun t x => f t x * g t x) ≤
      mixedNorm volume volume p₁ q₁ f * mixedNorm volume volume p₂ q₂ g := by
  apply le_trans (mixed_mono hq hqT (hf.mul hg) ?_)
    (mixed_normProduct_le hp₁ hp₂ hq₁ hq₁T hq₂ hq₂T hq hqT f g hf hg hff hgf)
  intro t x
  simpa only [normProduct, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    using norm_mul_le (f t x) (g t x)

/-- Positive powers have their exact extended mixed norm; no finiteness or
real-norm replacement is needed for this identity. -/
theorem mixed_rpow_eq {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {τ σ d : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) (hd : 0 < d)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume (reciprocal (τ*d)) (reciprocal (σ*d))
      (fun t x => ‖f t x‖ ^ d) =
      mixedNorm volume volume (reciprocal τ) (reciprocal σ) f ^ d := by
  unfold mixedNorm
  calc
    eLpNorm (fun t => eLpNorm (fun x => ‖f t x‖ ^ d) (reciprocal (σ*d)) volume)
        (reciprocal (τ*d)) volume =
      eLpNorm (fun t => eLpNorm (f t) (reciprocal σ) volume ^ d) (reciprocal (τ*d)) volume := by
        apply eLpNorm_congr_ae
        filter_upwards [hf.prodMk_left] with t ht
        rw [eLpNorm_norm_rpow (f t) ht hd, reciprocal_mul_ofReal hσ.le hd]
    _ = _ := by
      have hm := spatial_lp_time_measurable volume volume (reciprocal σ)
        (reciprocal_ne_zero σ) (reciprocal_ne_top hσ) f hf
      simpa only [enorm_eq_self, reciprocal_mul_ofReal hτ hd] using
        (eLpNorm_enorm_rpow (fun t => eLpNorm (f t) (reciprocal σ) volume) hm hd
          (p := reciprocal (τ*d)))

/-- A finite sum of literal functions, including the empty sum. -/
theorem mixed_sum_le {ι E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (s : Finset ι) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqT : q ≠ ∞)
    (f : ι → ℝ → Space → E)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => f i z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => ∑ i ∈ s, f i t x) ≤
      ∑ i ∈ s, mixedNorm volume volume p q (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp [mixedNorm]
  | @insert i s his ih =>
    intro hf
    have hsi := hf i (Finset.mem_insert_self i s)
    have hss := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : AEStronglyMeasurable (fun z : ℝ × Space => ∑ j ∈ s, f j z.1 z.2)
        (volume.prod volume) := by
      exact Finset.aestronglyMeasurable_fun_sum s hss
    simp only [Finset.sum_insert his]
    exact (mixed_add_le hp hq hqT _ _ hsi hsum).trans (add_le_add le_rfl (ih hss))

/-- Scalar domination passes through both norm layers with one finite
multiplicative factor. -/
theorem mixed_le_const_mul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hq : q ≠ 0) (hqT : q ≠ ∞) {K : ℝ} (hK : 0 ≤ K)
    (f : ℝ → Space → E) (g : ℝ → Space → F)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfg : ∀ t x, ‖f t x‖ ≤ K * ‖g t x‖) :
    mixedNorm volume volume p q f ≤ ENNReal.ofReal K * mixedNorm volume volume p q g := by
  let C : ℝ≥0 := ⟨K,hK⟩
  have hs : ∀ᵐ t ∂volume, eLpNorm (f t) q volume ≤ (C : ℝ≥0∞) * eLpNorm (g t) q volume := by
    filter_upwards [hf.prodMk_left] with t ht
    simpa only [ENNReal.smul_def, smul_eq_mul] using
      (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ht
        (Filter.Eventually.of_forall fun x => show ‖f t x‖₊ ≤ C * ‖g t x‖₊ from hfg t x) q)
  have hm := spatial_lp_time_measurable volume volume q hq hqT f hf
  have ho := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (c := C) (g := fun t => eLpNorm (g t) q volume) hm
    (by simpa only [enorm_eq_self] using hs) p
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal K := by
    exact (ENNReal.ofReal_eq_coe_nnreal hK).symm
  simpa only [mixedNorm, hC, ENNReal.smul_def, smul_eq_mul] using ho

private theorem power_joint {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (a : ℝ) : AEStronglyMeasurable (fun z : ℝ × Space => ‖f z.1 z.2‖ ^ a)
      (volume.prod volume) := (hf.norm.aemeasurable.pow_const a).aestronglyMeasurable

/-- One positive power and an already formed true mixed-space factor. -/
theorem mixed_power_mul_le {τ σ τ' σ' a : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 < σ) (hτ' : 0 ≤ τ') (hσ' : 0 < σ') (ha : 0 < a)
    (R P : ℝ → Space → ℝ)
    (hR : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) (volume.prod volume))
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) (volume.prod volume))
    (hRf : mixedNorm volume volume (reciprocal τ) (reciprocal σ) R ≠ ∞)
    (hPf : mixedNorm volume volume (reciprocal τ') (reciprocal σ') P ≠ ∞) :
    mixedNorm volume volume (reciprocal (τ*a+τ')) (reciprocal (σ*a+σ'))
      (fun t x => ‖R t x‖ ^ a * P t x) ≤
      mixedNorm volume volume (reciprocal τ) (reciprocal σ) R ^ a *
        mixedNorm volume volume (reciprocal τ') (reciprocal σ') P := by
  let := reciprocal_holder (mul_nonneg hτ ha.le) hτ'
  let := reciprocal_holder (mul_pos hσ ha).le hσ'.le
  have he := mixed_rpow_eq hτ hσ ha R hR
  have hf : mixedNorm volume volume (reciprocal (τ*a)) (reciprocal (σ*a))
      (fun t x => ‖R t x‖ ^ a) ≠ ∞ := by rw [he]; finiteness
  simpa only [he] using mixed_mul_le (reciprocal_ne_zero _) (reciprocal_ne_zero _)
    (reciprocal_ne_zero _) (reciprocal_ne_top (mul_pos hσ ha))
    (reciprocal_ne_zero _) (reciprocal_ne_top hσ')
    (reciprocal_ne_zero _) (reciprocal_ne_top (add_pos (mul_pos hσ ha) hσ'))
    (fun t x => ‖R t x‖ ^ a) P (power_joint R hR a) hP hf hPf

/-- Generic V/S/overlap monomial. The zero-a and zero-b branches omit their
factors before calling Hölder. In particular the Y0 row never asks for 1 in S. -/
theorem weighted_pair_le {a b d τ σ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hτ : 0 < τ) (hσ : 0 < σ)
    (R P : ℝ → Space → ℝ)
    (hR : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) (volume.prod volume))
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) (volume.prod volume))
    (hV : mixedNorm volume volume ∞ 6 R ≠ ∞)
    (hS : mixedNorm volume volume 10 10 R ≠ ∞)
    (hPfin : mixedNorm volume volume (reciprocal τ) (reciprocal σ) P ≠ ∞) :
    mixedNorm volume volume (reciprocal (b/10+τ*d)) (reciprocal (a/6+b/10+σ*d))
      (fun t x => ‖R t x‖ ^ a * ‖R t x‖ ^ b * ‖P t x‖ ^ d) ≤
      mixedNorm volume volume ∞ 6 R ^ a * mixedNorm volume volume 10 10 R ^ b *
        mixedNorm volume volume (reciprocal τ) (reciprocal σ) P ^ d := by
  let D : ℝ → Space → ℝ := fun t x => ‖P t x‖ ^ d
  have hD := power_joint P hP d
  have hDeq : mixedNorm volume volume (reciprocal (τ*d)) (reciprocal (σ*d)) D =
      mixedNorm volume volume (reciprocal τ) (reciprocal σ) P ^ d :=
    mixed_rpow_eq hτ.le hσ hd P hP
  have hDf : mixedNorm volume volume (reciprocal (τ*d)) (reciprocal (σ*d)) D ≠ ∞ := by
    rw [hDeq]; finiteness
  let B : ℝ → Space → ℝ := fun t x => ‖R t x‖ ^ b * D t x
  have hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) (volume.prod volume) :=
    (power_joint R hR b).mul hD
  have hBbound : mixedNorm volume volume (reciprocal (b/10+τ*d)) (reciprocal (b/10+σ*d)) B ≤
      mixedNorm volume volume 10 10 R ^ b *
        mixedNorm volume volume (reciprocal τ) (reciprocal σ) P ^ d := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simpa only [B, Real.rpow_zero, one_mul, zero_div, zero_add,
        ENNReal.rpow_zero] using hDeq.le
    · have hR10 : mixedNorm volume volume (reciprocal (1/10)) (reciprocal (1/10)) R ≠ ∞ := by
        simpa only [show reciprocal ((1:ℝ)/10)=10 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/10)]; norm_num] using hS
      have h := mixed_power_mul_le (by norm_num : (0:ℝ) ≤ 1/10) (by norm_num)
        (mul_pos hτ hd).le (mul_pos hσ hd) hb R D hR hD hR10 hDf
      simpa only [B, show (1:ℝ)/10*b=b/10 by ring, hDeq,
        show reciprocal ((1:ℝ)/10)=10 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/10)]; norm_num] using h
  have hBf : mixedNorm volume volume (reciprocal (b/10+τ*d)) (reciprocal (b/10+σ*d)) B ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) hBbound
  rcases eq_or_lt_of_le ha with rfl | ha
  · simpa only [B,D, Real.rpow_zero, one_mul, zero_div, zero_add,
      ENNReal.rpow_zero] using hBbound
  · have hR6 : mixedNorm volume volume (reciprocal 0) (reciprocal (1/6)) R ≠ ∞ := by
      simpa only [reciprocal_zero, show reciprocal ((1:ℝ)/6)=6 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/6)]; norm_num] using hV
    have h := mixed_power_mul_le (by norm_num : (0:ℝ) ≤ 0) (by norm_num)
      (add_nonneg (div_nonneg hb (by norm_num)) (mul_pos hτ hd).le)
      (add_pos_of_nonneg_of_pos (div_nonneg hb (by norm_num)) (mul_pos hσ hd)) ha R B hR hB hR6 hBf
    have hh := h.trans (mul_le_mul' le_rfl hBbound)
    simpa only [B,D, zero_mul, zero_add, reciprocal_zero,
      show (1:ℝ)/6*a=a/6 by ring,
      show reciprocal ((1:ℝ)/6)=6 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/6)]; norm_num, mul_assoc, add_assoc] using hh

/-- The exact exponents in the finite-profile ledger. -/
def delta0 (α : ℝ) : ℝ := min 1 ((3-α)/2)
def delta2 (α : ℝ) : ℝ := 1-α/3

def t0 (α : ℝ) : ℝ≥0∞ := reciprocal ((3-α)/10)
def x0 (α : ℝ) : ℝ≥0∞ := reciprocal ((9+7*α)/30)
def t1 (α : ℝ) : ℝ≥0∞ := reciprocal ((3+2*α/3)/10)
def x1 (α : ℝ) : ℝ≥0∞ := reciprocal ((57+11*α)/90)
def t2 (α : ℝ) : ℝ≥0∞ := reciprocal ((2-2*α/3)/10)
def x2 (α : ℝ) : ℝ≥0∞ := reciprocal ((18+19*α)/90)
def t3 (α : ℝ) : ℝ≥0∞ := reciprocal ((2+α)/10)
def x3 (α : ℝ) : ℝ≥0∞ := reciprocal ((16+3*α)/30)

theorem delta0_pos {α : ℝ} (hα : α < 3) : 0 < delta0 α := by
  unfold delta0
  exact lt_min (by norm_num) (by linarith)

theorem delta0_le_one (α : ℝ) : delta0 α ≤ 1 := min_le_left _ _

theorem delta0_remaining_nonneg (α : ℝ) : 0 ≤ 3-α-2*delta0 α := by
  have h := min_le_right (1:ℝ) ((3-α)/2)
  dsimp [delta0]
  linarith

theorem delta2_pos {α : ℝ} (hα : α < 3) : 0 < delta2 α := by dsimp [delta2]; linarith

theorem delta2_le_one {α : ℝ} (hα : 0 < α) : delta2 α ≤ 1 := by dsimp [delta2]; linarith

private theorem reciprocal_one_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    1 ≤ reciprocal r := by
  rw [reciprocal_eq hr]
  apply ENNReal.one_le_ofReal.mpr
  exact (one_le_inv₀ hr).mpr hr1

theorem ledger_domains {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    (1 ≤ t0 α ∧ 1 ≤ x0 α ∧ x0 α ≠ ∞) ∧
    (1 ≤ t1 α ∧ 1 ≤ x1 α ∧ x1 α ≠ ∞) ∧
    (1 ≤ t2 α ∧ 1 ≤ x2 α ∧ x2 α ≠ ∞) ∧
    (1 ≤ t3 α ∧ 1 ≤ x3 α ∧ x3 α ≠ ∞) := by
  have h0 : 0 < (3-α)/10 := by linarith
  have h1 : 0 < (3+2*α/3)/10 := by linarith
  have h2 : 0 < (2-2*α/3)/10 := by linarith
  have h3 : 0 < (2+α)/10 := by linarith
  have k0 : 0 < (9+7*α)/30 := by linarith
  have k1 : 0 < (57+11*α)/90 := by linarith
  have k2 : 0 < (18+19*α)/90 := by linarith
  have k3 : 0 < (16+3*α)/30 := by linarith
  exact ⟨⟨reciprocal_one_le h0 (by linarith), reciprocal_one_le k0 (by linarith), reciprocal_ne_top k0⟩,
    ⟨reciprocal_one_le h1 (by linarith), reciprocal_one_le k1 (by linarith), reciprocal_ne_top k1⟩,
    ⟨reciprocal_one_le h2 (by linarith), reciprocal_one_le k2 (by linarith), reciprocal_ne_top k2⟩,
    ⟨reciprocal_one_le h3 (by linarith), reciprocal_one_le k3 (by linarith), reciprocal_ne_top k3⟩⟩

/-- Ordinary HLS is strictly interior for both density input rows on all 0<α<3. -/
theorem ledger_hls_interior {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    1 < 30/(9+7*α) ∧ 30/(9+7*α) < 3/α ∧
    1 < 90/(57+11*α) ∧ 90/(57+11*α) < 3/α ∧
    (9+7*α)/30-α/3 = (3-α)/10 ∧
    (57+11*α)/90-α/3 = 19*(3-α)/90 ∧
    (3-α)/10+(16+3*α)/30 = 5/6 ∧
    19*(3-α)/90+(18+19*α)/90 = 5/6 ∧
    (3-α)/10+(2+α)/10 = 1/2 ∧
    (3+2*α/3)/10+(2-2*α/3)/10 = 1/2 := by
  have hp0 : 0 < 9+7*α := by linarith
  have hp1 : 0 < 57+11*α := by linarith
  refine ⟨(one_lt_div hp0).mpr (by linarith), (div_lt_div_iff₀ hp0 hα).mpr (by nlinarith),
    (one_lt_div hp1).mpr (by linarith), (div_lt_div_iff₀ hp1 hα).mpr (by nlinarith),
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

section FiniteFamily
variable {ι : Type*} [instDec : DecidableEq ι]

def radiusField (s : Finset ι) (u : ι → ℝ → Space → ℂ) : ℝ → Space → ℝ :=
  fun t x => radius s (fun i => u i t x)

def R0 (α : ℝ) (s : Finset ι) (u : ι → ℝ → Space → ℂ) : ℝ → Space → ℝ :=
  fun t x => densityDefect α s (fun i => u i t x)
def R1 (α : ℝ) (s : Finset ι) (u h : ι → ℝ → Space → ℂ) : ℝ → Space → ℝ :=
  fun t x => densityDerivativeDefect α s (fun i => u i t x) (fun i => h i t x)
def T0 (α : ℝ) (s : Finset ι) (u : ι → ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => localDefect α s (fun i => u i t x)
def T1 (α : ℝ) (s : Finset ι) (u h : ι → ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => localDerivativeDefect α s (fun i => u i t x) (fun i => h i t x)

def Pbudget (s : Finset ι) (u : ι → ℝ → Space → ℂ) (d : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ s, ∑ i ∈ s.erase j, localProductNorm 5 (u i) (u j) ^ d

def Qbudget (s : Finset ι) (u h : ι → ℝ → Space → ℂ) : ℝ≥0∞ :=
  ∑ j ∈ s, ∑ i ∈ s.erase j, localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u i) (h j)

def Vsize (s : Finset ι) (u : ι → ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume ∞ 6 (radiusField s u)
def Ssize (s : Finset ι) (u : ι → ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume 10 10 (radiusField s u)

omit instDec in
theorem radiusField_joint [DecidableEq ι] (s : Finset ι) (u : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, StronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => radiusField s u z.1 z.2) :=
  Finset.stronglyMeasurable_fun_sum s (fun i hi => (hu i hi).norm)

omit instDec in
theorem radiusField_norm_le [DecidableEq ι] (s : Finset ι) (u : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, StronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2))
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqT : q ≠ ∞) :
    mixedNorm volume volume p q (radiusField s u) ≤
      ∑ i ∈ s, mixedNorm volume volume p q (u i) := by
  have h := mixed_sum_le s hp hq hqT (fun i t x => ‖u i t x‖)
    (fun i hi => (hu i hi).aestronglyMeasurable.norm)
  change mixedNorm volume volume p q (radiusField s u) ≤
    ∑ i ∈ s, mixedNorm volume volume p q (fun t x => ‖u i t x‖) at h
  exact h.trans_eq (Finset.sum_congr rfl (fun i hi =>
    mixed_norm_norm_eq volume p q (u i) (hu i hi).aestronglyMeasurable))

theorem radiusField_finite (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) : Vsize s u ≠ ∞ ∧ Ssize s u ≠ ∞ := by
  have hj := fun i hi => (hu i hi).value_joint
  exact ⟨ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi => (hu i hi).value_V))
      (radiusField_norm_le s u hj (by simp) (by norm_num) (by norm_num)),
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi => (hu i hi).value_S))
      (radiusField_norm_le s u hj (by norm_num) (by norm_num) (by norm_num))⟩

omit instDec in
/-- The four defects are formed from genuine joint representatives and genuine
real Frechet derivatives; these are not target-domain hypotheses. -/
theorem defects_joint [DecidableEq ι] {α : ℝ} (hα : 0 < α) (s : Finset ι)
    (u h : ι → ℝ → Space → ℂ) (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    StronglyMeasurable (fun z : ℝ × Space => R0 α s u z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => R1 α s u h z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => T0 α s u z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => T1 α s u h z.1 z.2) := by
  have hZ := Finset.stronglyMeasurable_fun_sum s (fun i hi => (hu i hi).value_joint)
  have hH := Finset.stronglyMeasurable_fun_sum s (fun i hi => (hu i hi).gradient_joint)
  have hd := (density_contDiff_one (show 1 < 3+α by linarith)).continuous
  have hl := (localFactor_contDiff_one (show 1 < 1+α by linarith)).continuous
  have hd' := densityDerivative_continuous (show 1 < 3+α by linarith)
  have hl' := localFactorDerivative_continuous (show 1 < 1+α by linarith)
  have evR : Continuous (fun z : (ℂ →L[ℝ] ℝ) × ℂ => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have evC : Continuous (fun z : (ℂ →L[ℝ] ℂ) × ℂ => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  refine ⟨(hd.comp_stronglyMeasurable hZ).sub
      (Finset.stronglyMeasurable_fun_sum s (fun i hi => hd.comp_stronglyMeasurable (hu i hi).value_joint)),
    ?_, (hl.comp_stronglyMeasurable hZ).sub
      (Finset.stronglyMeasurable_fun_sum s (fun i hi => hl.comp_stronglyMeasurable (hu i hi).value_joint)), ?_⟩
  · exact (evR.comp_stronglyMeasurable ((hd'.comp_stronglyMeasurable hZ).prodMk hH)).sub
      (Finset.stronglyMeasurable_fun_sum s (fun i hi => evR.comp_stronglyMeasurable
        ((hd'.comp_stronglyMeasurable (hu i hi).value_joint).prodMk (hu i hi).gradient_joint)))
  · exact (evC.comp_stronglyMeasurable ((hl'.comp_stronglyMeasurable hZ).prodMk hH)).sub
      (Finset.stronglyMeasurable_fun_sum s (fun i hi => evC.comp_stronglyMeasurable
        ((hl'.comp_stronglyMeasurable (hu i hi).value_joint).prodMk (hu i hi).gradient_joint)))

omit instDec in
theorem local_pairs_finite [DecidableEq ι] (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    ∀ i ∈ s, ∀ j ∈ s,
      localProductNorm 5 (u i) (u j) ≠ ∞ ∧
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u i) (h j) ≠ ∞ := by
  intro i hi j hj
  exact ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top (hu i hi).value_S (hu j hj).value_S)
    (P_le _ _ (hu i hi).value_joint.aestronglyMeasurable (hu j hj).value_joint.aestronglyMeasurable
      (hu i hi).value_S (hu j hj).value_S),
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (hu i hi).value_S (hu j hj).gradient_W)
    (Q_le _ _ (hu i hi).value_joint.aestronglyMeasurable (hu j hj).gradient_joint.aestronglyMeasurable
      (hu i hi).value_S (hu j hj).gradient_W)⟩

private theorem weighted_double_sum_le (s : Finset ι)
    {a b d τ σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hτ : 0 < τ) (hσ : 0 < σ)
    (hp : 1 ≤ reciprocal (b/10+τ*d)) (hq : 1 ≤ reciprocal (a/6+b/10+σ*d))
    (R : ℝ → Space → ℝ) (P : ι → ι → ℝ → Space → ℝ)
    (hR : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) (volume.prod volume))
    (hP : ∀ j ∈ s, ∀ i ∈ s.erase j,
      AEStronglyMeasurable (fun z : ℝ × Space => P i j z.1 z.2) (volume.prod volume))
    (hV : mixedNorm volume volume ∞ 6 R ≠ ∞)
    (hS : mixedNorm volume volume 10 10 R ≠ ∞)
    (hPf : ∀ j ∈ s, ∀ i ∈ s.erase j,
      mixedNorm volume volume (reciprocal τ) (reciprocal σ) (P i j) ≠ ∞) :
    mixedNorm volume volume (reciprocal (b/10+τ*d)) (reciprocal (a/6+b/10+σ*d))
      (fun t x => ∑ j ∈ s, ∑ i ∈ s.erase j, ‖R t x‖ ^ a * ‖R t x‖ ^ b * ‖P i j t x‖ ^ d) ≤
      mixedNorm volume volume ∞ 6 R ^ a * mixedNorm volume volume 10 10 R ^ b *
        ∑ j ∈ s, ∑ i ∈ s.erase j,
          mixedNorm volume volume (reciprocal τ) (reciprocal σ) (P i j) ^ d := by
  have hqt := reciprocal_ne_top (show 0 < a/6+b/10+σ*d by positivity)
  have hm (j : ι) (hj : j ∈ s) (i : ι) (hi : i ∈ s.erase j) :
      AEStronglyMeasurable (fun z : ℝ × Space =>
        ‖R z.1 z.2‖ ^ a * ‖R z.1 z.2‖ ^ b * ‖P i j z.1 z.2‖ ^ d) (volume.prod volume) :=
    ((power_joint R hR a).mul (power_joint R hR b)).mul (power_joint (P i j) (hP j hj i hi) d)
  have hout := mixed_sum_le s hp hq hqt
    (fun j t x => ∑ i ∈ s.erase j, ‖R t x‖ ^ a * ‖R t x‖ ^ b * ‖P i j t x‖ ^ d)
    (fun j hj => Finset.aestronglyMeasurable_fun_sum (s.erase j) (hm j hj))
  apply hout.trans
  calc
    _ ≤ ∑ j ∈ s, ∑ i ∈ s.erase j,
        (mixedNorm volume volume ∞ 6 R ^ a * mixedNorm volume volume 10 10 R ^ b *
          mixedNorm volume volume (reciprocal τ) (reciprocal σ) (P i j) ^ d) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (mixed_sum_le (s.erase j) hp hq hqt _ (hm j hj)).trans
      exact Finset.sum_le_sum (fun i hi => weighted_pair_le ha hb hd hτ hσ R (P i j)
        hR (hP j hj i hi) hV hS (hPf j hj i hi))
    _ = _ := by simp only [Finset.mul_sum]

private theorem weighted_defect_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (s : Finset ι) {a b d τ σ K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hτ : 0 < τ) (hσ : 0 < σ) (hK : 0 ≤ K)
    (hp : 1 ≤ reciprocal (b/10+τ*d)) (hq : 1 ≤ reciprocal (a/6+b/10+σ*d))
    (R : ℝ → Space → ℝ) (P : ι → ι → ℝ → Space → ℝ) (f : ℝ → Space → E)
    (hRn : ∀ t x, 0 ≤ R t x)
    (hR : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) (volume.prod volume))
    (hP : ∀ j ∈ s, ∀ i ∈ s.erase j,
      AEStronglyMeasurable (fun z : ℝ × Space => P i j z.1 z.2) (volume.prod volume))
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hV : mixedNorm volume volume ∞ 6 R ≠ ∞)
    (hS : mixedNorm volume volume 10 10 R ≠ ∞)
    (hPf : ∀ j ∈ s, ∀ i ∈ s.erase j,
      mixedNorm volume volume (reciprocal τ) (reciprocal σ) (P i j) ≠ ∞)
    (hbound : ∀ t x, ‖f t x‖ ≤ K * R t x ^ (a+b) *
      ∑ j ∈ s, ∑ i ∈ s.erase j, ‖P i j t x‖ ^ d) :
    mixedNorm volume volume (reciprocal (b/10+τ*d)) (reciprocal (a/6+b/10+σ*d)) f ≤
      ENNReal.ofReal K * (mixedNorm volume volume ∞ 6 R ^ a * mixedNorm volume volume 10 10 R ^ b *
        ∑ j ∈ s, ∑ i ∈ s.erase j, mixedNorm volume volume (reciprocal τ) (reciprocal σ) (P i j) ^ d) := by
  let G : ℝ → Space → ℝ := fun t x =>
    ∑ j ∈ s, ∑ i ∈ s.erase j, ‖R t x‖ ^ a * ‖R t x‖ ^ b * ‖P i j t x‖ ^ d
  have hG (t : ℝ) (x : Space) : 0 ≤ G t x := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hdom (t : ℝ) (x : Space) : ‖f t x‖ ≤ K * ‖G t x‖ := by
    rw [Real.norm_of_nonneg (hG t x)]
    dsimp only [G]
    simp only [← Finset.mul_sum, Real.norm_of_nonneg (hRn t x),
      ← Real.rpow_add_of_nonneg (hRn t x) ha hb]
    simpa only [mul_assoc] using hbound t x
  exact (mixed_le_const_mul (reciprocal_ne_zero _)
    (reciprocal_ne_top (by positivity)) hK f G hf hdom).trans
      (mul_le_mul' le_rfl (weighted_double_sum_le s ha hb hd hτ hσ hp hq R P hR hP hV hS hPf))

/-- X0: the true density defect, with fractional P overlap. -/
theorem R0_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    mixedNorm volume volume (t0 α) (x0 α) (R0 α s u) ≤
      ENNReal.ofReal (densityMixedConstant (3+α)) *
        (Vsize s u ^ (2*α) * Ssize s u ^ (3-α-2*delta0 α) * Pbudget s u (delta0 α)) := by
  have ha : 0 ≤ 2*α := by positivity
  have hb := delta0_remaining_nonneg α
  have hd := delta0_pos hα3
  have ht : (3-α-2*delta0 α)/10+(1/5)*delta0 α=(3-α)/10 := by ring
  have hx : (2*α)/6+(3-α-2*delta0 α)/10+(1/5)*delta0 α=(9+7*α)/30 := by ring
  have hdegree : 2*α+(3-α-2*delta0 α)=3+α-2*delta0 α := by ring
  have hdom := (ledger_domains hα hα3).1
  have hfin := radiusField_finite s u h hu
  have hp := local_pairs_finite s u h hu
  have h := weighted_defect_le s ha hb hd (by norm_num : (0:ℝ)<1/5) (by norm_num : (0:ℝ)<1/5)
    (densityMixedConstant_pos (by linarith : 3<3+α)).le
    (by simpa only [ht,t0] using hdom.1) (by simpa only [hx,x0] using hdom.2.1)
    (radiusField s u) (fun i j => normProduct (u i) (u j)) (R0 α s u)
    (fun t x => radius_nonneg s _) (radiusField_joint s u (fun i hi => (hu i hi).value_joint)).aestronglyMeasurable
    (fun j hj i hi => (hu i (Finset.mem_of_mem_erase hi)).value_joint.aestronglyMeasurable.norm.mul
      (hu j hj).value_joint.aestronglyMeasurable.norm)
    (defects_joint hα s u h hu).1.aestronglyMeasurable hfin.1 hfin.2
    (fun j hj i hi => by
      simpa only [show reciprocal ((1:ℝ)/5)=5 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num, localProductNorm] using
        (hp i (Finset.mem_of_mem_erase hi) j hj).1)
    (fun t x => by
      simpa only [hdegree,R0,radiusField,normProduct,norm_mul,norm_norm,pairSum] using
        densityDefect_fractional_bound hα hd (delta0_le_one α) s (fun i => u i t x))
  simpa only [ht,hx,t0,x0,Vsize,Ssize,Pbudget,localProductNorm,
    show reciprocal ((1:ℝ)/5)=5 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num] using h

/-- X1: every ordered value/direction label is retained. -/
theorem R1_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    mixedNorm volume volume (t1 α) (x1 α) (R1 α s u h) ≤
      ENNReal.ofReal (densityMixedConstant (3+α)) *
        (Vsize s u ^ (α/3) * Ssize s u ^ (1+2*α/3) * Qbudget s u h) := by
  have ha : 0 ≤ α/3 := by positivity
  have hb : 0 ≤ 1+2*α/3 := by positivity
  have ht : (1+2*α/3)/10+(1/5)*1=(3+2*α/3)/10 := by ring
  have hx : (α/3)/6+(1+2*α/3)/10+(8/15)*1=(57+11*α)/90 := by ring
  have hdegree : α/3+(1+2*α/3)=1+α := by ring
  have hdom := (ledger_domains hα hα3).2.1
  have hfin := radiusField_finite s u h hu
  have hp := local_pairs_finite s u h hu
  have he5 : reciprocal ((1:ℝ)/5)=5 := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num
  have heq : reciprocal ((8:ℝ)/15)=ENNReal.ofReal (15/8 : ℝ) := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 8/15)]; norm_num
  have hh := weighted_defect_le s ha hb (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1/5) (by norm_num : (0:ℝ)<8/15)
    (densityMixedConstant_pos (by linarith : 3<3+α)).le
    (by simpa only [ht,t1] using hdom.1) (by simpa only [hx,x1] using hdom.2.1)
    (radiusField s u) (fun i j => normProduct (u i) (h j)) (R1 α s u h)
    (fun t x => radius_nonneg s _) (radiusField_joint s u (fun i hi => (hu i hi).value_joint)).aestronglyMeasurable
    (fun j hj i hi => (hu i (Finset.mem_of_mem_erase hi)).value_joint.aestronglyMeasurable.norm.mul
      (hu j hj).gradient_joint.aestronglyMeasurable.norm)
    (defects_joint hα s u h hu).2.1.aestronglyMeasurable hfin.1 hfin.2
    (fun j hj i hi => by simpa only [he5,heq,localProductNorm] using
      (hp i (Finset.mem_of_mem_erase hi) j hj).2)
    (fun t x => by
      simpa only [hdegree,R1,radiusField,normProduct,norm_mul,norm_norm,Real.rpow_one,directionSum] using
        densityDerivativeDefect_bound hα s (fun i => u i t x) (fun i => h i t x))
  simpa only [ht,hx,t1,x1,Vsize,Ssize,Qbudget,localProductNorm,he5,heq,ENNReal.rpow_one] using hh

/-- Y0: the remaining S power is identically zero and is omitted in the output. -/
theorem T0_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    mixedNorm volume volume (t2 α) (x2 α) (T0 α s u) ≤
      ENNReal.ofReal (localFactorMixedConstant (1+α)) *
        (Vsize s u ^ (5*α/3) * Pbudget s u (delta2 α)) := by
  have ha : 0 ≤ 5*α/3 := by positivity
  have hd := delta2_pos hα3
  have ht : (0:ℝ)/10+(1/5)*delta2 α=(2-2*α/3)/10 := by unfold delta2; ring
  have hx : (5*α/3)/6+0/10+(1/5)*delta2 α=(18+19*α)/90 := by unfold delta2; ring
  have hdegree : 5*α/3+0=2+α-2*delta2 α := by unfold delta2; ring
  have hdom := (ledger_domains hα hα3).2.2.1
  have hfin := radiusField_finite s u h hu
  have hp := local_pairs_finite s u h hu
  have hh := weighted_defect_le s ha (by norm_num : (0:ℝ)≤0) hd
    (by norm_num : (0:ℝ)<1/5) (by norm_num : (0:ℝ)<1/5)
    (localFactorMixedConstant_pos (by linarith : 1<1+α)).le
    (by simpa only [ht,t2] using hdom.1) (by simpa only [hx,x2] using hdom.2.1)
    (radiusField s u) (fun i j => normProduct (u i) (u j)) (T0 α s u)
    (fun t x => radius_nonneg s _) (radiusField_joint s u (fun i hi => (hu i hi).value_joint)).aestronglyMeasurable
    (fun j hj i hi => (hu i (Finset.mem_of_mem_erase hi)).value_joint.aestronglyMeasurable.norm.mul
      (hu j hj).value_joint.aestronglyMeasurable.norm)
    (defects_joint hα s u h hu).2.2.1.aestronglyMeasurable hfin.1 hfin.2
    (fun j hj i hi => by
      simpa only [show reciprocal ((1:ℝ)/5)=5 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num,localProductNorm] using
        (hp i (Finset.mem_of_mem_erase hi) j hj).1)
    (fun t x => by
      simpa only [hdegree,T0,radiusField,normProduct,norm_mul,norm_norm,pairSum] using
        localDefect_fractional_bound hα hd (delta2_le_one hα) s (fun i => u i t x))
  simpa only [ht,hx,t2,x2,Vsize,Ssize,Pbudget,localProductNorm,
    show reciprocal ((1:ℝ)/5)=5 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num,ENNReal.rpow_zero,mul_one] using hh

/-- Y1: the endpoint value V power is zero; only a true S power remains. -/
theorem T1_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    mixedNorm volume volume (t3 α) (x3 α) (T1 α s u h) ≤
      ENNReal.ofReal (localFactorMixedConstant (1+α)) * (Ssize s u ^ α * Qbudget s u h) := by
  have ht : α/10+(1/5)*1=(2+α)/10 := by ring
  have hx : (0:ℝ)/6+α/10+(8/15)*1=(16+3*α)/30 := by ring
  have hdom := (ledger_domains hα hα3).2.2.2
  have hfin := radiusField_finite s u h hu
  have hp := local_pairs_finite s u h hu
  have he5 : reciprocal ((1:ℝ)/5)=5 := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/5)]; norm_num
  have heq : reciprocal ((8:ℝ)/15)=ENNReal.ofReal (15/8 : ℝ) := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 8/15)]; norm_num
  have hh := weighted_defect_le s (by norm_num : (0:ℝ)≤0) hα.le (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1/5) (by norm_num : (0:ℝ)<8/15)
    (localFactorMixedConstant_pos (by linarith : 1<1+α)).le
    (by simpa only [ht,t3] using hdom.1) (by simpa only [hx,x3] using hdom.2.1)
    (radiusField s u) (fun i j => normProduct (u i) (h j)) (T1 α s u h)
    (fun t x => radius_nonneg s _) (radiusField_joint s u (fun i hi => (hu i hi).value_joint)).aestronglyMeasurable
    (fun j hj i hi => (hu i (Finset.mem_of_mem_erase hi)).value_joint.aestronglyMeasurable.norm.mul
      (hu j hj).gradient_joint.aestronglyMeasurable.norm)
    (defects_joint hα s u h hu).2.2.2.aestronglyMeasurable hfin.1 hfin.2
    (fun j hj i hi => by simpa only [he5,heq,localProductNorm] using
      (hp i (Finset.mem_of_mem_erase hi) j hj).2)
    (fun t x => by
      simpa only [zero_add,T1,radiusField,normProduct,norm_mul,norm_norm,Real.rpow_one,directionSum] using
        localDerivativeDefect_bound hα s (fun i => u i t x) (fun i => h i t x))
  simpa only [ht,hx,t3,x3,Vsize,Ssize,Qbudget,localProductNorm,he5,heq,
    ENNReal.rpow_one,ENNReal.rpow_zero,one_mul] using hh

theorem Pbudget_ne_top (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) {d : ℝ} (hd : 0 ≤ d) : Pbudget s u d ≠ ∞ := by
  have hp := local_pairs_finite s u h hu
  exact ENNReal.sum_ne_top.mpr (fun j hj => ENNReal.sum_ne_top.mpr (fun i hi =>
    ENNReal.rpow_ne_top_of_nonneg hd (hp i (Finset.mem_of_mem_erase hi) j hj).1))

theorem Qbudget_ne_top (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) : Qbudget s u h ≠ ∞ := by
  have hp := local_pairs_finite s u h hu
  exact ENNReal.sum_ne_top.mpr (fun j hj => ENNReal.sum_ne_top.mpr (fun i hi =>
    (hp i (Finset.mem_of_mem_erase hi) j hj).2))

/-- Each-index domains precede all limits and all real mixed-norm conversions. -/
theorem defects_finite {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    mixedNorm volume volume (t0 α) (x0 α) (R0 α s u) ≠ ∞ ∧
    mixedNorm volume volume (t1 α) (x1 α) (R1 α s u h) ≠ ∞ ∧
    mixedNorm volume volume (t2 α) (x2 α) (T0 α s u) ≠ ∞ ∧
    mixedNorm volume volume (t3 α) (x3 α) (T1 α s u h) ≠ ∞ := by
  have hV := (radiusField_finite s u h hu).1
  have hS := (radiusField_finite s u h hu).2
  have hP0 := Pbudget_ne_top s u h hu (delta0_pos hα3).le
  have hP2 := Pbudget_ne_top s u h hu (delta2_pos hα3).le
  have hQ := Qbudget_ne_top s u h hu
  have ha0 : 0 ≤ 2*α := by positivity
  have hb0 := delta0_remaining_nonneg α
  have ha1 : 0 ≤ α/3 := by positivity
  have hb1 : 0 ≤ 1+2*α/3 := by positivity
  have ha2 : 0 ≤ 5*α/3 := by positivity
  exact ⟨ne_top_of_le_ne_top (by finiteness) (R0_bound hα hα3 s u h hu),
    ne_top_of_le_ne_top (by finiteness) (R1_bound hα hα3 s u h hu),
    ne_top_of_le_ne_top (by finiteness) (T0_bound hα hα3 s u h hu),
    ne_top_of_le_ne_top (by finiteness) (T1_bound hα hα3 s u h hu)⟩

theorem Pbudget_tendsto_zero {κ : Type*} {l : Filter κ} (s : Finset ι)
    (u : κ → ι → ℝ → Space → ℂ) {d : ℝ} (hd : 0 < d)
    (hP : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Tendsto (fun n => localProductNorm 5 (u n i) (u n j)) l (𝓝 0)) :
    Tendsto (fun n => Pbudget s (u n) d) l (𝓝 0) := by
  have hinner (j : ι) (hj : j ∈ s) :
      Tendsto (fun n => ∑ i ∈ s.erase j, localProductNorm 5 (u n i) (u n j) ^ d) l (𝓝 0) := by
    have hh := tendsto_finsetSum (s.erase j) (fun i hi =>
      ((ENNReal.continuous_rpow_const (y := d)).tendsto 0).comp
        (hP i (Finset.mem_of_mem_erase hi) j hj (Finset.mem_erase.mp hi).1))
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hd, Finset.sum_const_zero] using hh
  simpa only [Pbudget, Finset.sum_const_zero] using tendsto_finsetSum s hinner

theorem Qbudget_tendsto_zero {κ : Type*} {l : Filter κ} (s : Finset ι)
    (u h : κ → ι → ℝ → Space → ℂ)
    (hQ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u n i) (h n j)) l (𝓝 0)) :
    Tendsto (fun n => Qbudget s (u n) (h n)) l (𝓝 0) := by
  have hinner (j : ι) (hj : j ∈ s) :
      Tendsto (fun n => ∑ i ∈ s.erase j,
        localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u n i) (h n j)) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (s.erase j)
      (fun i hi => hQ i (Finset.mem_of_mem_erase hi) j hj (Finset.mem_erase.mp hi).1)
  simpa only [Qbudget, Finset.sum_const_zero] using tendsto_finsetSum s hinner

private theorem tendsto_zero_of_const_mul_bound {κ : Type*} {l : Filter κ}
    {f b : κ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : Tendsto b l (𝓝 0)) (hfb : ∀ n, f n ≤ C*b n) : Tendsto f l (𝓝 0) := by
  have hlim := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC (by norm_num : (0:ℝ)<1)).comp hb
  have hlim' : Tendsto (fun n => C*b n) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.rpow_one] using hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun _ => bot_le) hfb

/-- The four limits use the original index filter. There is no subsequence
selection and no target-defect smallness or target-domain premise. -/
theorem defects_tendsto_zero {κ : Type*} {l : Filter κ} {α : ℝ}
    (hα : 0 < α) (hα3 : α < 3) (s : Finset ι)
    (u h : κ → ι → ℝ → Space → ℂ)
    (hu : ∀ n, ∀ i ∈ s, ScalarProfile (u n i) (h n i)) (M : ℝ≥0)
    (hV : ∀ n, Vsize s (u n) ≤ M) (hS : ∀ n, Ssize s (u n) ≤ M)
    (hP : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Tendsto (fun n => localProductNorm 5 (u n i) (u n j)) l (𝓝 0))
    (hQ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u n i) (h n j)) l (𝓝 0)) :
    Tendsto (fun n => mixedNorm volume volume (t0 α) (x0 α) (R0 α s (u n))) l (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume (t1 α) (x1 α) (R1 α s (u n) (h n))) l (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume (t2 α) (x2 α) (T0 α s (u n))) l (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume (t3 α) (x3 α) (T1 α s (u n) (h n))) l (𝓝 0) := by
  have ha0 : 0 ≤ 2*α := by positivity
  have hb0 := delta0_remaining_nonneg α
  have ha1 : 0 ≤ α/3 := by positivity
  have hb1 : 0 ≤ 1+2*α/3 := by positivity
  have ha2 : 0 ≤ 5*α/3 := by positivity
  have hp0 := Pbudget_tendsto_zero s u (delta0_pos hα3) hP
  have hp2 := Pbudget_tendsto_zero s u (delta2_pos hα3) hP
  have hq := Qbudget_tendsto_zero s u h hQ
  refine ⟨?_,?_,?_,?_⟩
  · apply tendsto_zero_of_const_mul_bound
      (C := ENNReal.ofReal (densityMixedConstant (3+α)) * ((M:ℝ≥0∞)^(2*α)*(M:ℝ≥0∞)^(3-α-2*delta0 α)))
      (by finiteness) hp0
    intro n
    have hb := (R0_bound hα hα3 s (u n) (h n) (hu n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul'
        (ENNReal.rpow_le_rpow (hV n) ha0) (ENNReal.rpow_le_rpow (hS n) hb0)) le_rfl))
    simpa only [mul_assoc] using hb
  · apply tendsto_zero_of_const_mul_bound
      (C := ENNReal.ofReal (densityMixedConstant (3+α)) * ((M:ℝ≥0∞)^(α/3)*(M:ℝ≥0∞)^(1+2*α/3)))
      (by finiteness) hq
    intro n
    have hb := (R1_bound hα hα3 s (u n) (h n) (hu n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul'
        (ENNReal.rpow_le_rpow (hV n) ha1) (ENNReal.rpow_le_rpow (hS n) hb1)) le_rfl))
    simpa only [mul_assoc] using hb
  · apply tendsto_zero_of_const_mul_bound
      (C := ENNReal.ofReal (localFactorMixedConstant (1+α)) * (M:ℝ≥0∞)^(5*α/3))
      (by finiteness) hp2
    intro n
    have hb := (T0_bound hα hα3 s (u n) (h n) (hu n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow (hV n) ha2) le_rfl))
    simpa only [mul_assoc] using hb
  · apply tendsto_zero_of_const_mul_bound
      (C := ENNReal.ofReal (localFactorMixedConstant (1+α)) * (M:ℝ≥0∞)^α)
      (by finiteness) hq
    intro n
    have hb := (T1_bound hα hα3 s (u n) (h n) (hu n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow (hS n) hα.le) le_rfl))
    simpa only [mul_assoc] using hb

omit instDec in
/-- A finite literal sum is again an actual scalar profile. -/
theorem scalarProfile_sum [DecidableEq ι] (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    ScalarProfile (fun t x => ∑ i ∈ s, u i t x) (fun t x => ∑ i ∈ s, h i t x) := by
  refine ⟨Finset.stronglyMeasurable_fun_sum s (fun i hi => (hu i hi).value_joint),
    Finset.stronglyMeasurable_fun_sum s (fun i hi => (hu i hi).gradient_joint), ?_, ?_, ?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi => (hu i hi).value_V))
      (mixed_sum_le s (by simp) (by norm_num) (by norm_num) u
        (fun i hi => (hu i hi).value_joint.aestronglyMeasurable))
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi => (hu i hi).value_S))
      (mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) u
        (fun i hi => (hu i hi).value_joint.aestronglyMeasurable))
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi => (hu i hi).gradient_W))
      (mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) h
        (fun i hi => (hu i hi).gradient_joint.aestronglyMeasurable))

end FiniteFamily

/-- Pure V/S powers, reused for both coefficient rows. -/
theorem power_VS_le {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    mixedNorm volume volume (reciprocal (b/10)) (reciprocal (a/6+b/10))
      (fun t x => ‖u t x‖ ^ (a+b)) ≤
      mixedNorm volume volume ∞ 6 u ^ a * mixedNorm volume volume 10 10 u ^ b := by
  let R : ℝ → Space → ℝ := fun t x => ‖u t x‖
  have hR := (hu.value_joint.aestronglyMeasurable (μ := volume.prod volume)).norm
  have hReq (p q : ℝ≥0∞) : mixedNorm volume volume p q R = mixedNorm volume volume p q u :=
    mixed_norm_norm_eq volume p q u hu.value_joint.aestronglyMeasurable
  have hV : mixedNorm volume volume ∞ 6 R ≠ ∞ := by rw [hReq]; exact hu.value_V
  have hS : mixedNorm volume volume 10 10 R ≠ ∞ := by rw [hReq]; exact hu.value_S
  have h := weighted_pair_le ha (by norm_num : (0:ℝ)≤0) hb
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/10) R R hR hR hV hS
    (by simpa only [show reciprocal ((1:ℝ)/10)=10 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/10)]; norm_num] using hS)
  simp only [hReq, show reciprocal ((1:ℝ)/10)=10 by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/10)]; norm_num,
    ENNReal.rpow_zero,mul_one] at h
  simpa only [R,norm_norm,Real.rpow_zero,mul_one,zero_div,zero_add,add_zero,
    show (1:ℝ)/10*b=b/10 by ring,
    ← Real.rpow_add_of_nonneg (norm_nonneg _) ha hb.le] using h

/-- Pure V/S/W powers, with one true gradient direction. -/
theorem power_VSW_le {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mixedNorm volume volume (reciprocal ((b+1)/10)) (reciprocal (a/6+b/10+13/30))
      (fun t x => ‖u t x‖ ^ (a+b) * ‖h t x‖) ≤
      mixedNorm volume volume ∞ 6 u ^ a * mixedNorm volume volume 10 10 u ^ b *
        mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h := by
  let R : ℝ → Space → ℝ := fun t x => ‖u t x‖
  let H : ℝ → Space → ℝ := fun t x => ‖h t x‖
  have hR := (hu.value_joint.aestronglyMeasurable (μ := volume.prod volume)).norm
  have hH := (hu.gradient_joint.aestronglyMeasurable (μ := volume.prod volume)).norm
  have hReq (p q : ℝ≥0∞) : mixedNorm volume volume p q R = mixedNorm volume volume p q u :=
    mixed_norm_norm_eq volume p q u hu.value_joint.aestronglyMeasurable
  have hHeq (p q : ℝ≥0∞) : mixedNorm volume volume p q H = mixedNorm volume volume p q h :=
    mixed_norm_norm_eq volume p q h hu.gradient_joint.aestronglyMeasurable
  have hV : mixedNorm volume volume ∞ 6 R ≠ ∞ := by rw [hReq]; exact hu.value_V
  have hS : mixedNorm volume volume 10 10 R ≠ ∞ := by rw [hReq]; exact hu.value_S
  have he10 : reciprocal ((1:ℝ)/10)=10 := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 1/10)]; norm_num
  have heW : reciprocal ((13:ℝ)/30)=ENNReal.ofReal (30/13 : ℝ) := by rw [reciprocal_eq (by norm_num : (0:ℝ) < 13/30)]; norm_num
  have hW : mixedNorm volume volume (reciprocal (1/10)) (reciprocal (13/30)) H ≠ ∞ := by
    rw [he10,heW,hHeq]; exact hu.gradient_W
  have hh := weighted_pair_le ha hb (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<13/30) R H hR hH hV hS hW
  simp only [hReq,hHeq,he10,heW,ENNReal.rpow_one] at hh
  simpa only [R,H,norm_norm,Real.rpow_one,mul_one,
    ← Real.rpow_add_of_nonneg (norm_nonneg _) ha hb,
    show b/10+(1:ℝ)/10=(b+1)/10 by ring] using hh

/-- The four coefficient fields paired with X0/X1/Y0/Y1 in the six-term identity. -/
def pureDensity (α : ℝ) (u : ℝ → Space → ℂ) : ℝ → Space → ℝ :=
  fun t x => WeakHartreeChain.density (3+α) (u t x)
def pureDensityDerivative (α : ℝ) (u h : ℝ → Space → ℂ) : ℝ → Space → ℝ :=
  fun t x => densityDerivative (3+α) (u t x) (h t x)
def pureLocal (α : ℝ) (u : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => localFactor (1+α) (u t x)
def pureLocalDerivative (α : ℝ) (u h : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => localFactorDerivative (1+α) (u t x) (h t x)

theorem pure_coefficients_joint {α : ℝ} (hα : 0 < α) {u h : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) :
    StronglyMeasurable (fun z : ℝ × Space => pureDensity α u z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => pureDensityDerivative α u h z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => pureLocal α u z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => pureLocalDerivative α u h z.1 z.2) := by
  have evR : Continuous (fun z : (ℂ →L[ℝ] ℝ) × ℂ => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have evC : Continuous (fun z : (ℂ →L[ℝ] ℂ) × ℂ => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact ⟨(density_contDiff_one (by linarith : 1<3+α)).continuous.comp_stronglyMeasurable hu.value_joint,
    evR.comp_stronglyMeasurable
      (((densityDerivative_continuous (by linarith : 1<3+α)).comp_stronglyMeasurable hu.value_joint).prodMk hu.gradient_joint),
    (localFactor_contDiff_one (by linarith : 1<1+α)).continuous.comp_stronglyMeasurable hu.value_joint,
    evC.comp_stronglyMeasurable
      (((localFactorDerivative_continuous (by linarith : 1<1+α)).comp_stronglyMeasurable hu.value_joint).prodMk hu.gradient_joint)⟩

/-- Exact coefficient estimates for a single profile, hence also for the literal
finite sum by `scalarProfile_sum`. These use only V, S and the true W direction. -/
theorem pure_coefficients_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h) :
    mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≤
      mixedNorm volume volume ∞ 6 u ^ (2*α) * mixedNorm volume volume 10 10 u ^ (3-α) ∧
    mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≤
      ENNReal.ofReal (3+α) * (mixedNorm volume volume ∞ 6 u ^ (α/3) *
        mixedNorm volume volume 10 10 u ^ (2+2*α/3) * mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h) ∧
    mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≤
      mixedNorm volume volume ∞ 6 u ^ (5*α/3) * mixedNorm volume volume 10 10 u ^ (2-2*α/3) ∧
    mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≤
      ENNReal.ofReal (2+α) * (mixedNorm volume volume 10 10 u ^ (1+α) *
        mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h) := by
  have hm := pure_coefficients_joint hα hu
  have hd := ledger_domains hα hα3
  refine ⟨?_,?_,?_,?_⟩
  · have hh := power_VS_le hu (show 0 ≤ 2*α by positivity) (show 0 < 3-α by linarith)
    unfold HartreeF.FiniteProfileMixedDefects.pureDensity HartreeF.WeakHartreeChain.density
    simpa only [t0,x0,
      show 2*α+(3-α)=3+α by ring,
      show (2*α)/6+(3-α)/10=(9+7*α)/30 by ring] using hh
  · let B : ℝ → Space → ℝ := fun t x => ‖u t x‖^(2+α)*‖h t x‖
    have hdom (t : ℝ) (x : Space) : ‖pureDensityDerivative α u h t x‖ ≤ (3+α)*‖B t x‖ := by
      have hh := (densityDerivative (3+α) (u t x)).le_opNorm (h t x)
      rw [densityDerivative_norm (by linarith : 1<3+α)] at hh
      simpa only [pureDensityDerivative,B,show (3+α)-1=2+α by ring,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)),mul_assoc] using hh
    have hbound := power_VSW_le hu (show 0 ≤ α/3 by positivity) (show 0 ≤ 2+2*α/3 by positivity)
    have hb : mixedNorm volume volume (t1 α) (x1 α) B ≤
        mixedNorm volume volume ∞ 6 u ^ (α/3) * mixedNorm volume volume 10 10 u ^ (2+2*α/3) *
          mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h := by
      simpa only [B,t1,x1,show α/3+(2+2*α/3)=2+α by ring,
        show (2+2*α/3)+1=3+2*α/3 by ring,
        show (α/3)/6+(2+2*α/3)/10+13/30=(57+11*α)/90 by ring] using hbound
    exact (mixed_le_const_mul (reciprocal_ne_zero _) hd.2.1.2.2
      (by linarith : 0≤3+α) _ B hm.2.1.aestronglyMeasurable hdom).trans (mul_le_mul' le_rfl hb)
  · have hpow := power_VS_le hu (show 0 ≤ 5*α/3 by positivity) (show 0 < 2-2*α/3 by linarith)
    have hb : mixedNorm volume volume (t2 α) (x2 α) (fun t x => ‖u t x‖^(2+α)) ≤
        mixedNorm volume volume ∞ 6 u ^ (5*α/3) * mixedNorm volume volume 10 10 u ^ (2-2*α/3) := by
      simpa only [t2,x2,show 5*α/3+(2-2*α/3)=2+α by ring,
        show (5*α/3)/6+(2-2*α/3)/10=(18+19*α)/90 by ring] using hpow
    apply (mixed_mono (reciprocal_ne_zero _) hd.2.2.1.2.2 hm.2.2.1.aestronglyMeasurable ?_).trans hb
    intro t x
    simp only [pureLocal,localFactor,norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : (1+α)+1≠0)]
    simp only [show (1+α)+1=2+α by ring]
    exact le_rfl
  · let B : ℝ → Space → ℝ := fun t x => ‖u t x‖^(1+α)*‖h t x‖
    have hdom (t : ℝ) (x : Space) : ‖pureLocalDerivative α u h t x‖ ≤ (2+α)*‖B t x‖ := by
      have hh := (localFactorDerivative (1+α) (u t x)).le_opNorm (h t x)
      have hb := mul_le_mul_of_nonneg_right (localFactorDerivative_bound (by linarith : 1<1+α) (u t x))
        (norm_nonneg (h t x))
      simpa only [pureLocalDerivative,B,show (1+α)+1=2+α by ring,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)),mul_assoc] using hh.trans hb
    have hbound := power_VSW_le hu (by norm_num : (0:ℝ)≤0) (show 0≤1+α by linarith)
    have hb : mixedNorm volume volume (t3 α) (x3 α) B ≤
        mixedNorm volume volume 10 10 u ^ (1+α) * mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h := by
      simpa only [B,t3,x3,zero_add,zero_div,ENNReal.rpow_zero,one_mul,
        show (1+α)+1=2+α by ring,
        show (1+α)/10+13/30=(16+3*α)/30 by ring] using hbound
    exact (mixed_le_const_mul (reciprocal_ne_zero _) hd.2.2.2.2.2
      (by linarith : 0≤2+α) _ B hm.2.2.2.aestronglyMeasurable hdom).trans (mul_le_mul' le_rfl hb)

theorem pure_coefficients_finite {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h) :
    mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≠ ∞ ∧
    mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≠ ∞ ∧
    mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≠ ∞ ∧
    mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≠ ∞ := by
  have hV := hu.value_V
  have hS := hu.value_S
  have hW := hu.gradient_W
  have ha0 : 0 ≤ 2*α := by positivity
  have hb0 : 0 ≤ 3-α := by linarith
  have ha1 : 0 ≤ α/3 := by positivity
  have hb1 : 0 ≤ 2+2*α/3 := by positivity
  have ha2 : 0 ≤ 5*α/3 := by positivity
  have hb2 : 0 ≤ 2-2*α/3 := by linarith
  have hb3 : 0 ≤ 1+α := by linarith
  obtain ⟨h0,h1,h2,h3⟩ := pure_coefficients_bound hα hα3 hu
  exact ⟨ne_top_of_le_ne_top (by finiteness) h0,
    ne_top_of_le_ne_top (by finiteness) h1,
    ne_top_of_le_ne_top (by finiteness) h2,
    ne_top_of_le_ne_top (by finiteness) h3⟩

/-- One finite NNReal cap works for all coefficient fields with the same finite
V/S/W cap. In particular it can be fixed before the original filter index. -/
theorem pure_coefficients_uniform_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (u h : ℝ → Space → ℂ), ScalarProfile u h →
      mixedNorm volume volume ∞ 6 u ≤ M → mixedNorm volume volume 10 10 u ≤ M →
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h ≤ M →
      mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≤ C ∧
      mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≤ C ∧
      mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≤ C ∧
      mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≤ C := by
  let B0 : ℝ≥0∞ := (M:ℝ≥0∞)^(2*α)*(M:ℝ≥0∞)^(3-α)
  let B1 : ℝ≥0∞ := ENNReal.ofReal (3+α)*((M:ℝ≥0∞)^(α/3)*(M:ℝ≥0∞)^(2+2*α/3)*M)
  let B2 : ℝ≥0∞ := (M:ℝ≥0∞)^(5*α/3)*(M:ℝ≥0∞)^(2-2*α/3)
  let B3 : ℝ≥0∞ := ENNReal.ofReal (2+α)*((M:ℝ≥0∞)^(1+α)*M)
  have ha0 : 0 ≤ 2*α := by positivity
  have hb0 : 0 ≤ 3-α := by linarith
  have ha1 : 0 ≤ α/3 := by positivity
  have hb1 : 0 ≤ 2+2*α/3 := by positivity
  have ha2 : 0 ≤ 5*α/3 := by positivity
  have hb2 : 0 ≤ 2-2*α/3 := by linarith
  have hb3 : 0 ≤ 1+α := by linarith
  have hfin : B0+B1+B2+B3 ≠ ∞ := by dsimp [B0,B1,B2,B3]; finiteness
  refine ⟨(B0+B1+B2+B3).toNNReal, ?_⟩
  intro u h hu hV hS hW
  simp only [ENNReal.coe_toNNReal hfin]
  obtain ⟨h0,h1,h2,h3⟩ := pure_coefficients_bound hα hα3 hu
  have h0' : mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≤ B0 :=
    h0.trans (mul_le_mul' (ENNReal.rpow_le_rpow hV ha0) (ENNReal.rpow_le_rpow hS hb0))
  have h1' : mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≤ B1 :=
    h1.trans (mul_le_mul' le_rfl (mul_le_mul'
      (mul_le_mul' (ENNReal.rpow_le_rpow hV ha1) (ENNReal.rpow_le_rpow hS hb1)) hW))
  have h2' : mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≤ B2 :=
    h2.trans (mul_le_mul' (ENNReal.rpow_le_rpow hV ha2) (ENNReal.rpow_le_rpow hS hb2))
  have h3' : mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≤ B3 :=
    h3.trans (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hS hb3) hW))
  have h01 : B0 ≤ B0+B1 := le_add_of_nonneg_right (by positivity)
  have h10 : B1 ≤ B0+B1 := le_add_of_nonneg_left (by positivity)
  have h012 : B0+B1 ≤ B0+B1+B2 := le_add_of_nonneg_right (by positivity)
  have h201 : B2 ≤ B0+B1+B2 := le_add_of_nonneg_left (by positivity)
  have h0123 : B0+B1+B2 ≤ B0+B1+B2+B3 := le_add_of_nonneg_right (by positivity)
  have h3012 : B3 ≤ B0+B1+B2+B3 := le_add_of_nonneg_left (by positivity)
  exact ⟨h0'.trans (h01.trans (h012.trans h0123)),
    h1'.trans (h10.trans (h012.trans h0123)), h2'.trans (h201.trans h0123), h3'.trans h3012⟩

#print axioms mixed_mul_le
#print axioms mixed_rpow_eq
#print axioms weighted_pair_le
#print axioms ledger_hls_interior
#print axioms R0_bound
#print axioms R1_bound
#print axioms T0_bound
#print axioms T1_bound
#print axioms defects_finite
#print axioms defects_tendsto_zero
#print axioms pure_coefficients_finite
#print axioms pure_coefficients_uniform_bound
end HartreeF.FiniteProfileMixedDefects
