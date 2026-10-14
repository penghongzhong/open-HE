import FFreeQuadraticSlices
import FFreeCylinderDomains
import FHighpassFourierCore
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Chebyshev

/-! Actual finite-cylinder high-frequency localization for the F free group.
Static draft; no compilation or acceptance claim is made. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal Topology
namespace HartreeF.FreeLocalCompactness
open FreeFlow ActualStrichartz EnergySpace.Highpass

/-- A coordinate split into a real coordinate and an ordinary two-coordinate
product. No isometry between Pi Fin 2 and Euclidean Fin 2 is asserted. -/
def axisSplit (k : Fin 3) : V ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k)

theorem axisSplit_measurePreserving (k : Fin 3) : MeasurePreserving (axisSplit k) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) k).comp
    (PiLp.volume_preserving_ofLp (ι := Fin 3))

@[simp] theorem axisSplit_fst (k : Fin 3) (x : V) : (axisSplit k x).1 = x k := rfl
@[simp] theorem axisSplit_snd (k : Fin 3) (x : V) (j : Fin 2) :
    (axisSplit k x).2 j = x (k.succAbove j) := rfl

/-- Swap the scalar time coordinate with one physical coordinate. -/
def timeAxisSwap (k : Fin 3) : (ℝ × V) ≃ᵐ (ℝ × V) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (axisSplit k)).trans
    ((MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin 2 → ℝ) ≃ᵐ
      ℝ × (ℝ × (Fin 2 → ℝ))).symm.trans
      (((MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).prodCongr
        (MeasurableEquiv.refl (Fin 2 → ℝ))).trans
        ((MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin 2 → ℝ) ≃ᵐ
          ℝ × (ℝ × (Fin 2 → ℝ))).trans
          ((MeasurableEquiv.refl ℝ).prodCongr (axisSplit k).symm))))

theorem timeAxisSwap_measurePreserving (k : Fin 3) :
    MeasurePreserving (timeAxisSwap k) := by
  have h₁ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (axisSplit_measurePreserving k)
  have h₂ := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin 2 → ℝ) ≃ᵐ ℝ × (ℝ × (Fin 2 → ℝ)))
    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := Fin 2 → ℝ))
  have h₃ := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).prod
      (MeasurePreserving.id (volume : Measure (Fin 2 → ℝ)))
  have h₄ := volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := Fin 2 → ℝ)
  have h₅ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (MeasurePreserving.symm (axisSplit k) (axisSplit_measurePreserving k))
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

theorem timeAxisSwap_apply (k : Fin 3) (t : ℝ) (x : V) :
    timeAxisSwap k (t, x) = (x k, spatialSlice k t x) := by
  change (x k, (axisSplit k).symm (t, (axisSplit k x).2)) =
    (x k, spatialSlice k t x)
  apply Prod.ext
  · rfl
  · apply (axisSplit k).injective
    rw [MeasurableEquiv.apply_symm_apply]
    apply Prod.ext
    · exact (spatialSlice_same k t x).symm
    · ext j
      exact (spatialSlice_other k (k.succAbove j) (Fin.succAbove_ne k j) t x).symm

theorem timeAxisSwap_involution (k : Fin 3) : Function.Involutive (timeAxisSwap k) := by
  intro p
  rcases p with ⟨t, x⟩
  rw [timeAxisSwap_apply, timeAxisSwap_apply, spatialSlice_same]
  congr 1
  ext j
  by_cases hj : j = k
  · subst j
    simp
  · simp [spatialSlice_other k j hj]

/-- Tonelli after the exact measure-preserving coordinate permutation. -/
theorem lintegral_coordinate_slab (k : Fin 3) {I : Set ℝ} (hI : MeasurableSet I)
    {H : ℝ × V → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p in {p : ℝ × V | p.2 k ∈ I}, H p ∂(volume.prod volume)) =
      ∫⁻ b in I, ∫⁻ y, H (y k, spatialSlice k b y) := by
  have hslab : MeasurableSet {p : ℝ × V | p.2 k ∈ I} := by
    exact hI.preimage (by fun_prop)
  have hpre : (timeAxisSwap k) ⁻¹' {p : ℝ × V | p.2 k ∈ I} = I ×ˢ Set.univ := by
    ext p
    rcases p with ⟨b, y⟩
    simp [timeAxisSwap_apply]
  have hswap : MeasurePreserving (timeAxisSwap k)
      ((volume : Measure ℝ).prod (volume : Measure V))
      ((volume : Measure ℝ).prod (volume : Measure V)) :=
    timeAxisSwap_measurePreserving k
  rw [← hswap.setLIntegral_comp_preimage hslab hH, hpre,
    ← Measure.restrict_prod_eq_prod_univ, lintegral_prod]
  · apply lintegral_congr_ae
    exact Eventually.of_forall (fun b => by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun y => by
        change H (timeAxisSwap k (b, y)) = H (y k, spatialSlice k b y)
        rw [timeAxisSwap_apply]))
  · exact (hH.comp (timeAxisSwap k).measurable).aemeasurable

theorem cylinderMeasure_le_product (T R : ℝ) (z : V) :
    cylinderMeasure T R z ≤ volume.prod volume :=
  Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self

theorem ball_subset_coordinate_slab (k : Fin 3) (R : ℝ) (z : V) :
    Metric.ball z R ⊆ {x : V | x k ∈ Set.Icc (z k - R) (z k + R)} := by
  intro x hx
  have hdist : |x k - z k| < R := by
    calc
      _ = ‖(x - z) k‖ := by simp
      _ ≤ ‖x - z‖ := PiLp.norm_apply_le (x - z) k
      _ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  exact ⟨by linarith [(abs_lt.mp hdist).1], by linarith [(abs_lt.mp hdist).2]⟩


/-- Product-AE transport yields only an almost-every-b trace for freeJoint. -/
theorem integralEvolution_ae_freeJoint_coordinate {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) (has : StronglyMeasurable a) (k : Fin 3) :
    ∀ᵐ b : ℝ, (fun y => integralEvolution a (y k) (spatialSlice k b y)) =ᵐ[volume]
      (fun y => freeJoint (𝓕⁻ (ha2.toLp a)) (y k) (spatialSlice k b y)) := by
  have h := (timeAxisSwap_measurePreserving k).quasiMeasurePreserving.ae_eq_comp
    (integralEvolution_ae_freeJoint ha ha2 has)
  have h' := Measure.ae_ae_eq_curry_of_prod
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure V)) h
  filter_upwards [h'] with b hb
  filter_upwards [hb] with y hy
  change Function.uncurry (integralEvolution a) (timeAxisSwap k (b, y)) =
    Function.uncurry (freeJoint (𝓕⁻ (ha2.toLp a))) (timeAxisSwap k (b, y)) at hy
  rw [timeAxisSwap_apply] at hy
  exact hy

/-- The scalar slab-integration lemma. The square domains are supplied before
converting slice integrals to lintegrals; Tonelli then handles all-time slabs. -/
theorem cylinder_integral_le_of_slices {u : ℝ → V → ℂ}
    (hu : StronglyMeasurable (Function.uncurry u)) (k : Fin 3)
    (T R : ℝ) (hR : 0 ≤ R) (z : V)
    (huc : Integrable (fun p : ℝ × V => ‖u p.1 p.2‖ ^ 2) (cylinderMeasure T R z))
    {A : ℝ} (hA : 0 ≤ A)
    (hus : ∀ b, MemLp (fun y => u (y k) (spatialSlice k b y)) 2)
    (hbound : ∀ b, (∫ y, ‖u (y k) (spatialSlice k b y)‖ ^ 2) ≤ A) :
    (∫ p : ℝ × V, ‖u p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) ≤ (2 * R) * A := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hA)).mp
  rw [ofReal_integral_eq_lintegral_ofReal huc (Eventually.of_forall (fun p => sq_nonneg _))]
  let H : ℝ × V → ℝ≥0∞ := fun p => ENNReal.ofReal (‖u p.1 p.2‖ ^ 2)
  have hH : Measurable H := by
    exact (hu.measurable.norm.pow_const 2).ennreal_ofReal
  have hs : Set.Icc (-T) T ×ˢ Metric.ball z R ⊆
      {p : ℝ × V | p.2 k ∈ Set.Icc (z k - R) (z k + R)} := by
    intro p hp
    exact ball_subset_coordinate_slab k R z hp.2
  change (∫⁻ p, H p ∂cylinderMeasure T R z) ≤ _
  calc
    _ ≤ ∫⁻ p in {p : ℝ × V | p.2 k ∈ Set.Icc (z k - R) (z k + R)},
        H p ∂(volume.prod volume) := by
      rw [cylinderMeasure, Measure.prod_restrict]
      exact lintegral_mono_set hs
    _ = ∫⁻ b in Set.Icc (z k - R) (z k + R),
        ∫⁻ y, ENNReal.ofReal (‖u (y k) (spatialSlice k b y)‖ ^ 2) :=
      lintegral_coordinate_slab k measurableSet_Icc hH
    _ ≤ ∫⁻ _b in Set.Icc (z k - R) (z k + R), ENNReal.ofReal A := by
      apply lintegral_mono
      intro b
      change (∫⁻ y, ENNReal.ofReal (‖u (y k) (spatialSlice k b y)‖ ^ 2)) ≤
        ENNReal.ofReal A
      have hi := (memLp_two_iff_integrable_sq_norm (hus b).aestronglyMeasurable).mp (hus b)
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (fun y => sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hbound b)
    _ = ENNReal.ofReal ((2 * R) * A) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      rw [show z k + R - (z k - R) = 2 * R by ring]
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      ring

/-- Actual datum for one finite annular cone. -/
def coneDatum (c : ConeIndex) (N m : ℝ) {a : V → ℂ} (ha2 : MemLp a 2) : L2 :=
  𝓕⁻ ((truncatedCone_memLp ha2 c N m).toLp ((truncatedCone c N m).indicator a))

/-- One-cone bound for the actual freeJoint, after the explicit-integral
representative has been transported product-a.e. -/
theorem coneDatum_cylinder_bound (c : ConeIndex) {N m : ℝ} (hN : 0 < N)
    {a : V → ℂ} (has : StronglyMeasurable a) (ha2 : MemLp a 2)
    (T R : ℝ) (hR : 0 ≤ R) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint (coneDatum c N m ha2) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) ≤
      (2 * R) * (Real.sqrt 3 / (4 * Real.pi * N)) *
        ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 := by
  let S := truncatedCone c N m
  have hs : MeasurableSet S := truncatedCone_measurable c N m
  have haS : StronglyMeasurable (S.indicator a) := has.indicator hs
  have hiS : Integrable (S.indicator a) := truncatedCone_integrable ha2 c N m
  have h2S : MemLp (S.indicator a) 2 := truncatedCone_memLp ha2 c N m
  have he : Function.uncurry (integralEvolution (S.indicator a)) =ᵐ[cylinderMeasure T R z]
      Function.uncurry (freeJoint (coneDatum c N m ha2)) :=
    (integralEvolution_ae_freeJoint hiS h2S haS).filter_mono
      (ae_mono (cylinderMeasure_le_product T R z))
  have hui : Integrable (fun p : ℝ × V =>
      ‖integralEvolution (S.indicator a) p.1 p.2‖ ^ 2) (cylinderMeasure T R z) :=
    (freeJoint_cylinder_integrable_sq (coneDatum c N m ha2) T R z).congr
      (he.symm.fun_comp (fun w : ℂ => ‖w‖ ^ 2))
  have hum : ∀ b, MemLp (fun y => integralEvolution (S.indicator a)
      (y c.1) (spatialSlice c.1 b y)) 2 := by
    intro b
    exact integralEvolution_truncated_slice_memLp c.1 c.2 hs
      (truncatedCone_subset_halfspace c N m) has
      ((integrable_indicator_iff hs).mp hiS) (ha2.restrict S)
      (by positivity : 0 < N / Real.sqrt (3 : ℝ))
      (fun ξ hξ => truncatedCone_coordinate_lower c hN hξ) b
  calc
    _ = ∫ p : ℝ × V, ‖integralEvolution (S.indicator a) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z :=
      integral_congr_ae (he.symm.fun_comp (fun w : ℂ => ‖w‖ ^ 2))
    _ ≤ (2 * R) * ((Real.sqrt 3 / (4 * Real.pi * N)) *
        ∫ ξ in S, ‖a ξ‖ ^ 2) :=
      cylinder_integral_le_of_slices (integralEvolution_stronglyMeasurable haS)
        c.1 T R hR z hui (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))
        hum (fun b => truncatedCone_slice_bound c hN has ha2 b)
    _ = _ := by ring


theorem truncatedCone_disjoint {c d : ConeIndex} (hcd : c ≠ d) (N m : ℝ) :
    Disjoint (truncatedCone c N m) (truncatedCone d N m) :=
  (dominantCone_disjoint hcd).mono inter_subset_left inter_subset_left

/-- Disjoint cone Fourier inputs are counted once, including all ties. -/
theorem cone_square_sum_le (N m : ℝ) (a : V → ℂ) (ξ : V) :
    (∑ c : ConeIndex, (truncatedCone c N m).indicator (fun ξ => ‖a ξ‖ ^ 2) ξ) ≤
      ‖a ξ‖ ^ 2 := by
  by_cases h : ∃ c : ConeIndex, ξ ∈ truncatedCone c N m
  · obtain ⟨c, hc⟩ := h
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro d _ hdc
      have hd : ξ ∉ truncatedCone d N m := fun hd =>
        Set.disjoint_left.mp (truncatedCone_disjoint hdc N m) hd hc
      simp [hd]
    · simp
  · have hz : ∀ c : ConeIndex, ξ ∉ truncatedCone c N m := by simpa using h
    simp only [Set.indicator_of_notMem (hz _), Finset.sum_const_zero]
    exact sq_nonneg _

theorem cone_square_integral_sum_le {a : V → ℂ} (ha2 : MemLp a 2) (N m : ℝ) :
    (∑ c : ConeIndex, ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2) ≤ ‖ha2.toLp a‖ ^ 2 := by
  have hsq := (memLp_two_iff_integrable_sq_norm ha2.aestronglyMeasurable).mp ha2
  have hsi (c : ConeIndex) :
      Integrable ((truncatedCone c N m).indicator (fun ξ => ‖a ξ‖ ^ 2)) :=
    hsq.indicator (truncatedCone_measurable c N m)
  calc
    _ = ∑ c : ConeIndex, ∫ ξ, (truncatedCone c N m).indicator (fun ξ => ‖a ξ‖ ^ 2) ξ := by
      apply Finset.sum_congr rfl
      intro c _
      exact (integral_indicator (truncatedCone_measurable c N m)).symm
    _ = ∫ ξ, ∑ c : ConeIndex, (truncatedCone c N m).indicator (fun ξ => ‖a ξ‖ ^ 2) ξ := by
      symm
      exact integral_finsetSum Finset.univ (fun c _ => hsi c)
    _ ≤ ∫ ξ, ‖a ξ‖ ^ 2 := integral_mono
      (integrable_finsetSum _ (fun c _ => hsi c)) hsq (cone_square_sum_le N m a)
    _ = _ := integral_sq_norm_toLp ha2

/-- The factor six is explicit; there is no second factor six in the disjoint
Fourier input norm sum. -/
theorem six_sum_norm_sq_le {E : Type*} [NormedAddCommGroup E] (g : ConeIndex → E) :
    ‖∑ c : ConeIndex, g c‖ ^ 2 ≤ 6 * ∑ c : ConeIndex, ‖g c‖ ^ 2 := by
  calc
    _ ≤ (∑ c : ConeIndex, ‖g c‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun c _ => norm_nonneg _))).2
        (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
        show (3 : ℝ) * 2 = 6 by norm_num] using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ConeIndex))
          (f := fun c => ‖g c‖))

def finiteConeDatum (N m : ℝ) {a : V → ℂ} (ha2 : MemLp a 2) : L2 :=
  ∑ c : ConeIndex, coneDatum c N m ha2

/-- The six-cone estimate at a finite upper frequency cutoff. -/
theorem finiteConeDatum_cylinder_bound {N m T R : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hR : 0 ≤ R) {a : V → ℂ} (has : StronglyMeasurable a) (ha2 : MemLp a 2) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint (finiteConeDatum N m ha2) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) ≤
      (3 * Real.sqrt 3 * R / (Real.pi * N)) * ‖ha2.toLp a‖ ^ 2 := by
  let C := (2 * R) * (Real.sqrt 3 / (4 * Real.pi * N))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ = ‖localFreeL2CLM hT R z (finiteConeDatum N m ha2)‖ ^ 2 :=
      (localFreeL2_norm_sq T R z _).symm
    _ = ‖∑ c : ConeIndex, localFreeL2CLM hT R z (coneDatum c N m ha2)‖ ^ 2 := by
      rw [finiteConeDatum, map_sum]
    _ ≤ 6 * ∑ c : ConeIndex, ‖localFreeL2CLM hT R z (coneDatum c N m ha2)‖ ^ 2 :=
      six_sum_norm_sq_le _
    _ = 6 * ∑ c : ConeIndex, ∫ p : ℝ × V,
        ‖freeJoint (coneDatum c N m ha2) p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z := by
      simp only [localFreeL2CLM_apply, localFreeL2_norm_sq]
    _ ≤ 6 * ∑ c : ConeIndex, C * ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro c _
      exact coneDatum_cylinder_bound c hN has ha2 T R hR z
    _ = 6 * C * ∑ c : ConeIndex, ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 6 * C * ‖ha2.toLp a‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (cone_square_integral_sum_le ha2 N m) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Annulus for the independent upper-frequency approximation index. -/
def frequencyAnnulus (N m : ℝ) : Set V := {ξ | N < ‖ξ‖ ∧ ‖ξ‖ ≤ m}

theorem frequencyAnnulus_measurable (N m : ℝ) : MeasurableSet (frequencyAnnulus N m) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet

theorem sum_cone_indicators {N : ℝ} (hN : 0 < N) (m : ℝ) (a : V → ℂ) (ξ : V) :
    (∑ c : ConeIndex, (truncatedCone c N m).indicator a ξ) =
      (frequencyAnnulus N m).indicator a ξ := by
  by_cases hξ : ξ ∈ frequencyAnnulus N m
  · have hn : ξ ≠ 0 := by
      intro hz
      have hh := hξ.1
      rw [hz, norm_zero] at hh
      linarith
    obtain ⟨c, hc⟩ := dominantCone_cover hn
    have hSc : ξ ∈ truncatedCone c N m := ⟨hc, hξ⟩
    rw [Finset.sum_eq_single c]
    · simp [hSc, hξ]
    · intro d _ hdc
      have hd : ξ ∉ truncatedCone d N m := fun hd =>
        Set.disjoint_left.mp (truncatedCone_disjoint hdc N m) hd hSc
      simp [hd]
    · simp
  · have hz (c : ConeIndex) : ξ ∉ truncatedCone c N m := fun hc => hξ hc.2
    simp [hξ, Set.indicator_of_notMem (hz _)]

theorem finiteConeDatum_eq_annulus {N : ℝ} (hN : 0 < N) (m : ℝ)
    {a : V → ℂ} (ha2 : MemLp a 2) :
    finiteConeDatum N m ha2 =
      𝓕⁻ ((ha2.indicator (frequencyAnnulus_measurable N m).nullMeasurableSet).toLp
        ((frequencyAnnulus N m).indicator a)) := by
  unfold finiteConeDatum coneDatum
  change (∑ c : ConeIndex, (fourierInvCLM ℂ L2)
      ((truncatedCone_memLp ha2 c N m).toLp ((truncatedCone c N m).indicator a))) =
    (fourierInvCLM ℂ L2)
      ((ha2.indicator (frequencyAnnulus_measurable N m).nullMeasurableSet).toLp
        ((frequencyAnnulus N m).indicator a))
  rw [← map_sum]
  congr 1
  apply Lp.ext
  have hall : ∀ᵐ ξ, ∀ c : ConeIndex,
      (truncatedCone_memLp ha2 c N m).toLp ((truncatedCone c N m).indicator a) ξ =
        (truncatedCone c N m).indicator a ξ :=
    ae_all_iff.2 (fun c => (truncatedCone_memLp ha2 c N m).coeFn_toLp)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun c : ConeIndex => (truncatedCone_memLp ha2 c N m).toLp
      ((truncatedCone c N m).indicator a)), hall,
    (ha2.indicator (frequencyAnnulus_measurable N m).nullMeasurableSet).coeFn_toLp]
    with ξ hsum hcone hann
  rw [hsum, hann]
  simp only [hcone]
  exact sum_cone_indicators hN m a ξ


/-- Strong L2 convergence removes only the upper Fourier cutoff. The auxiliary
index is independent of the weakly convergent sequence in the consumer. -/
theorem finiteConeDatum_tendsto {N : ℝ} (hN : 0 < N) {a : V → ℂ}
    (ha2 : MemLp a 2) (hzero : ∀ᵐ ξ, ‖ξ‖ ≤ N → a ξ = 0) :
    Tendsto (fun n : ℕ => finiteConeDatum N (n : ℝ) ha2) atTop
      (𝓝 (𝓕⁻ (ha2.toLp a))) := by
  let A : ℕ → V → ℂ := fun n => (frequencyAnnulus N (n : ℝ)).indicator a
  have hA (n : ℕ) : MemLp (A n) 2 :=
    ha2.indicator (frequencyAnnulus_measurable N (n : ℝ)).nullMeasurableSet
  have hsq := (memLp_two_iff_integrable_sq_norm ha2.aestronglyMeasurable).mp ha2
  have hint : Tendsto (fun n : ℕ => ∫ ξ, ‖A n ξ - a ξ‖ ^ 2) atTop (𝓝 0) := by
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure V)) (F := fun n ξ => ‖A n ξ - a ξ‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun ξ => ‖a ξ‖ ^ 2)
      (fun n => ((hA n).aestronglyMeasurable.sub ha2.aestronglyMeasurable).norm.pow 2)
      hsq
      (fun n => Eventually.of_forall (fun ξ => by
        change ‖(‖A n ξ - a ξ‖ ^ 2 : ℝ)‖ ≤ ‖a ξ‖ ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg ‖A n ξ - a ξ‖)]
        by_cases hξ : ξ ∈ frequencyAnnulus N (n : ℝ)
        · simp [A, hξ]
        · simp [A, hξ]))
      (by
        filter_upwards [hzero] with ξ hξ
        by_cases hNξ : N < ‖ξ‖
        · apply tendsto_const_nhds.congr'
          have hn : ∀ᶠ n : ℕ in atTop, ‖ξ‖ ≤ (n : ℝ) :=
            tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ‖)
          filter_upwards [hn] with n hn
          simp [A, frequencyAnnulus, hNξ, hn]
        · have hz := hξ (le_of_not_gt hNξ)
          apply tendsto_const_nhds.congr'
          exact Eventually.of_forall (fun n => by
            simp [A, frequencyAnnulus, hNξ, hz]))
    simpa only [integral_zero] using hdom
  have hinv (f : L2) : ‖(𝓕⁻ f : L2)‖ = ‖f‖ := by
    simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ f)).symm
  have hnorm (n : ℕ) :
      ‖finiteConeDatum N (n : ℝ) ha2 - 𝓕⁻ (ha2.toLp a)‖ ^ 2 =
        ∫ ξ, ‖A n ξ - a ξ‖ ^ 2 := by
    rw [finiteConeDatum_eq_annulus hN]
    change ‖(fourierInvCLM ℂ L2) ((hA n).toLp (A n)) -
      (fourierInvCLM ℂ L2) (ha2.toLp a)‖ ^ 2 = _
    rw [← map_sub]
    change ‖𝓕⁻ ((hA n).toLp (A n) - ha2.toLp a)‖ ^ 2 = _
    rw [hinv, ← MemLp.toLp_sub, ← integral_sq_norm_toLp]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have ht : Tendsto (fun n : ℕ =>
      ‖finiteConeDatum N (n : ℝ) ha2 - 𝓕⁻ (ha2.toLp a)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using hint
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp ht

/-- All L2 data supported above a positive cycles radius obey the local bound.
The limit uses only the already proved finite-window unitarity operator. -/
theorem highSupport_cylinder_bound (f : L2) {N T R : ℝ} (hN : 0 < N)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (z : V)
    (hsupport : ∀ᵐ ξ, ‖ξ‖ ≤ N → (𝓕 f : L2) ξ = 0) :
    (∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) ≤
      (3 * Real.sqrt 3 * R / (Real.pi * N)) * ‖f‖ ^ 2 := by
  let a : V → ℂ := (Lp.aestronglyMeasurable (𝓕 f : L2)).mk (fun ξ => (𝓕 f : L2) ξ)
  have has : StronglyMeasurable a :=
    (Lp.aestronglyMeasurable (𝓕 f : L2)).stronglyMeasurable_mk
  have hae : (fun ξ => (𝓕 f : L2) ξ) =ᵐ[volume] a :=
    (Lp.aestronglyMeasurable (𝓕 f : L2)).ae_eq_mk
  have ha2 : MemLp a 2 := (Lp.memLp (𝓕 f : L2)).ae_eq hae
  have hclass : ha2.toLp a = (𝓕 f : L2) := by
    apply Lp.ext
    exact ha2.coeFn_toLp.trans hae.symm
  have hz : ∀ᵐ ξ, ‖ξ‖ ≤ N → a ξ = 0 := by
    filter_upwards [hsupport, hae] with ξ hξ he
    intro hNξ
    rw [← he]
    exact hξ hNξ
  have hlim : Tendsto (fun n : ℕ => finiteConeDatum N (n : ℝ) ha2) atTop (𝓝 f) := by
    simpa only [hclass, fourierInv_fourier_eq] using finiteConeDatum_tendsto hN ha2 hz
  apply le_of_tendsto' (freeJoint_cylinder_integral_tendsto_of_L2 hlim hT z)
  intro n
  simpa only [hclass, Lp.norm_fourier_eq] using
    finiteConeDatum_cylinder_bound (m := (n : ℝ)) hN hT hR has ha2 z

/-- Fourier representative of the actual complementary smooth multiplier.
This is not an idempotence claim about the cutoff. -/
theorem actualHighL2_fourier_ae (q : Cutoff) (L : ℝ) (f : L2) :
    ((𝓕 (highL2 q L f) : L2) : V → ℂ) =ᵐ[volume]
      (fun ξ => (1 - lowSymbol q L ξ) * (𝓕 f : L2) ξ) := by
  have he : 𝓕 (highL2 q L f) = 𝓕 f - lowMultiply q L (𝓕 f) := by
    change (fourierCLM ℂ L2) (f - lowL2 q L f) = _
    rw [map_sub]
    change 𝓕 f - 𝓕 (lowL2 q L f) = _
    rw [lowL2_fourier]
  rw [he]
  filter_upwards [Lp.coeFn_sub (𝓕 f) (lowMultiply q L (𝓕 f)),
    lowMultiply_coe q L (𝓕 f)] with ξ h₁ h₂
  rw [h₁]
  simp only [Pi.sub_apply]
  rw [h₂]
  ring

theorem actualHighL2_fourier_support (q : Cutoff) (f : L2) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ ξ, ‖ξ‖ ≤ L / (2 * Real.pi) → (𝓕 (highL2 q L f) : L2) ξ = 0 := by
  filter_upwards [actualHighL2_fourier_ae q L f] with ξ hξ
  intro hNξ
  have ha : 2 * Real.pi * ‖ξ‖ ≤ L := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp hNξ
    nlinarith
  rw [hξ, lowSymbol_one q hL ξ ha, sub_self, zero_mul]

/-- Uniform high-frequency local tail of the ACTUAL freeJoint. Angular cutoff
L is converted to cycles radius L/(2*pi). The safe norm factor two gives the
constant 24; no cutoff idempotence, Strichartz premise, or compactness premise
is used. -/
theorem highL2_local_bound (q : Cutoff) (f : L2) {T R L : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hL : 0 < L) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint (highL2 q L f) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) ≤ (24 * Real.sqrt 3 * R / L) * ‖f‖ ^ 2 := by
  have hN : 0 < L / (2 * Real.pi) := by positivity
  have hC : 0 ≤ 3 * Real.sqrt 3 * R / (Real.pi * (L / (2 * Real.pi))) := by positivity
  calc
    _ ≤ (3 * Real.sqrt 3 * R / (Real.pi * (L / (2 * Real.pi)))) * ‖highL2 q L f‖ ^ 2 :=
      highSupport_cylinder_bound (highL2 q L f) hN hT.le hR.le z
        (actualHighL2_fourier_support q f hL)
    _ ≤ (3 * Real.sqrt 3 * R / (Real.pi * (L / (2 * Real.pi)))) * (2 * ‖f‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (highL2_norm q L f)) hC
    _ = _ := by field_simp [Real.pi_ne_zero, hL.ne']; ring

end HartreeF.FreeLocalCompactness
