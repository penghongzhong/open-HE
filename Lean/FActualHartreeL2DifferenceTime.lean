import FActualHartreeL2Difference
import FHartreeL2Time

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2Difference
open ForcingDomain GradientMajorants DerivativeMajorization TimeHolder

/-- The two positive L10 powers consume exactly time L2. -/
theorem time_two_ten_powers {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=5)
    (S D : T → ℝ) (hS : AEStronglyMeasurable S mu) (hD : AEStronglyMeasurable D mu) :
    eLpNorm (fun t => ‖S t‖^a * ‖D t‖^b) 2 mu ≤
      eLpNorm S 10 mu ^ a * eLpNorm D 10 mu ^ b := by
  let : ENNReal.HolderTriple (lpFromReciprocal (a/10)) (lpFromReciprocal (b/10)) 2 := by
    convert holder_from_real_reciprocals (show 0 < a/10 by positivity)
      (show 0 < b/10 by positivity) (by norm_num : (0 : ℝ) < 1/2) (by linarith : a/10+b/10=1/2) using 1
    norm_num [lpFromReciprocal]
  have hh := temporal_real_product_norm mu (p := lpFromReciprocal (a/10))
    (q := lpFromReciprocal (b/10)) (r := 2) (fun t => ‖S t‖^a) (fun t => ‖D t‖^b)
    (hS.norm.aemeasurable.pow_const a).aestronglyMeasurable
    (hD.norm.aemeasurable.pow_const b).aestronglyMeasurable
  simpa only [temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10) ha S hS,
    temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10) hb D hD,
    ENNReal.ofReal_ofNat] using hh

/-- Ordinary time Holder applied to the first and second spatial difference
allocations. All norms remain extended-valued in this statement. -/
theorem time_difference_holder {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {α : ℝ} (ha : 0 < α) (ha3 : α < 3)
    (E S DE DS : T → ℝ) (hE : AEStronglyMeasurable E mu)
    (hS : AEStronglyMeasurable S mu) (hDE : AEStronglyMeasurable DE mu)
    (hDS : AEStronglyMeasurable DS mu) :
    eLpNorm (fun t => ‖E t‖^(2*α) * ‖S t‖^(4 : ℝ) * ‖DS t‖ +
      ‖E t‖^(5*α/3) * ‖S t‖^(4+α/3) * ‖DE t‖^(α/3) * ‖DS t‖^(1-α/3)) 2 mu ≤
      eLpNorm E ∞ mu^(2*α) * eLpNorm S 10 mu^(4 : ℝ) * eLpNorm DS 10 mu +
      eLpNorm E ∞ mu^(5*α/3) * eLpNorm S 10 mu^(4+α/3) *
        eLpNorm DE ∞ mu^(α/3) * eLpNorm DS 10 mu^(1-α/3) := by
  have mE (a : ℝ) := (hE.norm.aemeasurable.pow_const a).aestronglyMeasurable
  have mS (a : ℝ) := (hS.norm.aemeasurable.pow_const a).aestronglyMeasurable
  have mDE (a : ℝ) := (hDE.norm.aemeasurable.pow_const a).aestronglyMeasurable
  have mDS (a : ℝ) := (hDS.norm.aemeasurable.pow_const a).aestronglyMeasurable
  have hfirst : eLpNorm (fun t => ‖E t‖^(2*α) * ‖S t‖^(4 : ℝ) * ‖DS t‖) 2 mu ≤
      eLpNorm E ∞ mu^(2*α) * eLpNorm S 10 mu^(4 : ℝ) * eLpNorm DS 10 mu := by
    have hs := time_two_ten_powers mu (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num) S DS hS hDS
    simp only [Real.rpow_one, ENNReal.rpow_one] at hs
    have hh := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
      (fun t => ‖E t‖^(2*α)) (fun t => ‖S t‖^(4 : ℝ)*‖DS t‖)
      (mE _) ((mS _).mul hDS.norm)
    rw [temporal_native_infinity_power_norm mu (by positivity : 0 < 2*α) E hE] at hh
    simpa only [mul_assoc] using hh.trans (mul_le_mul' le_rfl hs)
  have hsecond : eLpNorm (fun t => ‖E t‖^(5*α/3) * ‖S t‖^(4+α/3) * ‖DE t‖^(α/3) * ‖DS t‖^(1-α/3)) 2 mu ≤
      eLpNorm E ∞ mu^(5*α/3) * eLpNorm S 10 mu^(4+α/3) *
        eLpNorm DE ∞ mu^(α/3) * eLpNorm DS 10 mu^(1-α/3) := by
    have hs := time_two_ten_powers mu (by linarith : 0 < 4+α/3)
      (by linarith : 0 < 1-α/3) (by ring) S DS hS hDS
    have hi := temporal_real_product_norm mu (p := ∞) (q := ∞) (r := ∞)
      (fun t => ‖E t‖^(5*α/3)) (fun t => ‖DE t‖^(α/3)) (mE _) (mDE _)
    rw [temporal_native_infinity_power_norm mu (by positivity : 0 < 5*α/3) E hE,
      temporal_native_infinity_power_norm mu (by positivity : 0 < α/3) DE hDE] at hi
    have hh := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
      (fun t => ‖E t‖^(5*α/3)*‖DE t‖^(α/3))
      (fun t => ‖S t‖^(4+α/3)*‖DS t‖^(1-α/3))
      ((mE _).mul (mDE _)) ((mS _).mul (mDS _))
    have he : (fun t => ‖E t‖^(5*α/3) * ‖S t‖^(4+α/3) * ‖DE t‖^(α/3) * ‖DS t‖^(1-α/3)) =
        (fun t => (‖E t‖^(5*α/3)*‖DE t‖^(α/3))*(‖S t‖^(4+α/3)*‖DS t‖^(1-α/3))) := by funext t; ring
    rw [he]
    convert hh.trans (mul_le_mul' hi hs) using 1
    ring
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hfirst hsecond)

/-- The actual complex Hartree difference has the full-range mixed L2 estimate.
Only L6 and L10 slice membership is assumed. The amplitude and difference
mixed norms are extended-valued; infinite inputs are not silently truncated. -/
theorem actual_forcing_difference_mixed_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
      (u v : T → Space → ℂ),
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume) →
      (∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume) →
      (∀ᵐ t ∂mu, MemLp (v t) 6 volume ∧ MemLp (v t) 10 volume) →
      mixedNorm mu volume 2 2 (fun t => forcing α c (u t)-forcing α c (v t)) ≤
        (C : ℝ≥0∞) *
        (mixedNorm mu volume ∞ 6 (fun t => sumAmplitude (u t) (v t)) ^ (2*α) *
          mixedNorm mu volume 10 10 (fun t => sumAmplitude (u t) (v t)) ^ (4 : ℝ) *
          mixedNorm mu volume 10 10 (fun t => differenceAmplitude (u t) (v t)) +
        mixedNorm mu volume ∞ 6 (fun t => sumAmplitude (u t) (v t)) ^ (5*α/3) *
          mixedNorm mu volume 10 10 (fun t => sumAmplitude (u t) (v t)) ^ (4+α/3) *
          mixedNorm mu volume ∞ 6 (fun t => differenceAmplitude (u t) (v t)) ^ (α/3) *
          mixedNorm mu volume 10 10 (fun t => differenceAmplitude (u t) (v t)) ^ (1-α/3)) := by
  obtain ⟨C,hC⟩ := actual_forcing_difference_bound hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u v hu hv hsu hsv
  let V : T → Space → ℝ := fun t => sumAmplitude (u t) (v t)
  let D : T → Space → ℝ := fun t => differenceAmplitude (u t) (v t)
  let E : T → ℝ := fun t => (eLpNorm (V t) 6 volume).toReal
  let S : T → ℝ := fun t => (eLpNorm (V t) 10 volume).toReal
  let DE : T → ℝ := fun t => (eLpNorm (D t) 6 volume).toReal
  let DS : T → ℝ := fun t => (eLpNorm (D t) 10 volume).toReal
  let a : T → ℝ≥0∞ := fun t => eLpNorm (forcing α c (u t)-forcing α c (v t)) 2 volume
  have hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume) :=
    hu.norm.add hv.norm
  have hD : AEStronglyMeasurable (fun z : T × Space => D z.1 z.2) (mu.prod volume) :=
    (hu.sub hv).norm
  have hVs : ∀ᵐ t ∂mu, MemLp (V t) 6 volume ∧ MemLp (V t) 10 volume := by
    filter_upwards [hsu,hsv] with t hut hvt
    exact ⟨hut.1.norm.add hvt.1.norm,hut.2.norm.add hvt.2.norm⟩
  have hDs : ∀ᵐ t ∂mu, MemLp (D t) 6 volume ∧ MemLp (D t) 10 volume := by
    filter_upwards [hsu,hsv] with t hut hvt
    exact ⟨(hut.1.sub hvt.1).norm,(hut.2.sub hvt.2).norm⟩
  have hEm := spatial_lp_time_measurable mu volume 6 (by norm_num) (by norm_num) V hV
  have hSm := spatial_lp_time_measurable mu volume 10 (by norm_num) (by norm_num) V hV
  have hDEm := spatial_lp_time_measurable mu volume 6 (by norm_num) (by norm_num) D hD
  have hDSm := spatial_lp_time_measurable mu volume 10 (by norm_num) (by norm_num) D hD
  have hE : AEStronglyMeasurable E mu := hEm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hS : AEStronglyMeasurable S mu := hSm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hDE : AEStronglyMeasurable DE mu := hDEm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hDS : AEStronglyMeasurable DS mu := hDSm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hNm := (ForcingL2.joint_forcing_measurable mu α c u hu).sub
    (ForcingL2.joint_forcing_measurable mu α c v hv)
  have ham : AEStronglyMeasurable a mu := spatial_lp_time_measurable mu volume 2
    (by norm_num) (by norm_num) _ hNm
  have haf : ∀ᵐ t ∂mu, a t ≠ ∞ := by
    filter_upwards [hsu,hsv] with t hut hvt
    exact (hC (u t) (v t) hut.1 hvt.1 hut.2 hvt.2).1.eLpNorm_ne_top
  have hmono : eLpNorm (fun t => (a t).toReal) 2 mu ≤
      eLpNorm ((C : ℝ) • (fun t => ‖E t‖^(2*α) * ‖S t‖^(4 : ℝ) * ‖DS t‖ +
        ‖E t‖^(5*α/3) * ‖S t‖^(4+α/3) * ‖DE t‖^(α/3) * ‖DS t‖^(1-α/3))) 2 mu := by
    apply eLpNorm_mono_ae ham.aemeasurable.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hsu,hsv] with t hut hvt
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hb := (hC (u t) (v t) hut.1 hvt.1 hut.2 hvt.2).2
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [a,E,S,DE,DS,V,D,spatialNorm,ENNReal.ofReal_ofNat,
      Real.norm_of_nonneg ENNReal.toReal_nonneg] using hb
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal C.coe_nonneg, ENNReal.ofReal_coe_nnreal] at hmono
  have hb := hmono.trans (mul_le_mul' le_rfl
    (time_difference_holder mu hH.order_pos hH.order_lt_three E S DE DS hE hS hDE hDS))
  have hEf : mixedNorm mu volume ∞ 6 V = eLpNorm E ∞ mu :=
    finite_extended_norm_bridge mu ∞ _ hEm (hVs.mono fun _ ht => ht.1.eLpNorm_ne_top)
  have hSf : mixedNorm mu volume 10 10 V = eLpNorm S 10 mu :=
    finite_extended_norm_bridge mu 10 _ hSm (hVs.mono fun _ ht => ht.2.eLpNorm_ne_top)
  have hDEf : mixedNorm mu volume ∞ 6 D = eLpNorm DE ∞ mu :=
    finite_extended_norm_bridge mu ∞ _ hDEm (hDs.mono fun _ ht => ht.1.eLpNorm_ne_top)
  have hDSf : mixedNorm mu volume 10 10 D = eLpNorm DS 10 mu :=
    finite_extended_norm_bridge mu 10 _ hDSm (hDs.mono fun _ ht => ht.2.eLpNorm_ne_top)
  change eLpNorm a 2 mu ≤ (C : ℝ≥0∞) *
    (mixedNorm mu volume ∞ 6 V^(2*α) * mixedNorm mu volume 10 10 V^(4 : ℝ) * mixedNorm mu volume 10 10 D +
    mixedNorm mu volume ∞ 6 V^(5*α/3) * mixedNorm mu volume 10 10 V^(4+α/3) *
      mixedNorm mu volume ∞ 6 D^(α/3) * mixedNorm mu volume 10 10 D^(1-α/3))
  rw [finite_extended_norm_bridge mu 2 a ham haf,hEf,hSf,hDEf,hDSf]
  exact hb

#print axioms time_two_ten_powers
#print axioms time_difference_holder
#print axioms actual_forcing_difference_mixed_bound
end HartreeF.ForcingL2Difference
