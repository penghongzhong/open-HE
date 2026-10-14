import FOrdinaryLinearProfileInterface
import FOrdinaryHomogeneousStrichartz
import FFreeGlobalValueS
import FGeneralMixedDomains
import FCoordinateGradientPack

/-! Actual homogeneous free-value domains and quantitative bounds.
Static source candidate, UNCOMPILED. The value is profileFreeJoint of an
EnergyState; freeJoint is used only on its genuine L2 gradient coordinates.
The equal-exponent adapter is an extended ENNReal identity, including infinity. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.ActualFreeValue
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy ActualStrichartz
  CriticalTimeSobolev TimeHolder GeneralProfileCross ProfileApproximation

/-- Equal-exponent Tonelli, before any finiteness or real-norm conversion. -/
theorem mixedNorm_ten_ten_eq_product (f : ℝ → Space → ℂ)
    (hf : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume)) :
    mixedNorm volume volume 10 10 f =
      eLpNorm (Function.uncurry f) 10 (volume.prod volume) := by
  have hm := spatial_lp_time_measurable (volume : Measure ℝ) volume 10
    (by norm_num) (by norm_num) f hf
  unfold mixedNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  congr 1
  calc
    (∫⁻ t : ℝ, ‖eLpNorm (f t) 10 volume‖ₑ ^ (10 : ℝ≥0∞).toReal) =
        ∫⁻ t : ℝ, ∫⁻ x : Space, ‖f t x‖ₑ ^ (10 : ℝ≥0∞).toReal := by
      apply lintegral_congr_ae
      filter_upwards [hf.prodMk_left] with t ht
      change AEStronglyMeasurable (f t) volume at ht
      rw [enorm_eq_self,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht,
        ← ENNReal.rpow_mul]
      norm_num
    _ = ∫⁻ z : ℝ × Space, ‖Function.uncurry f z‖ₑ ^ (10 : ℝ≥0∞).toReal :=
      (lintegral_prod _ (hf.enorm.pow_const _)).symm

/-- The extraction's product L10 is exactly the actual mixed S norm. -/
theorem profileFreeJoint_S_eq_profileFreeSize (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (v : EnergyState) :
    mixedNorm volume volume 10 10 (profileFreeJoint hDensity hSob v) =
      profileFreeSize hDensity hSob v :=
  mixedNorm_ten_ten_eq_product _
    (profileFreeJoint_measurable hDensity hSob v).aestronglyMeasurable

/-- A new record using the actual freeJoint coordinates. It is not an alias
for energyJointFields, whose gradient representatives use a different choice. -/
def freeValueFields (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v : EnergyState) :
    EnergyJointFields volume (fun t => freeEnergyState hDensity hSob t v) where
  u := profileFreeJoint hDensity hSob v
  U := jointProjection Complex.reCLM (fun k => freeJoint (energyGradient k v))
  V := jointProjection Complex.imCLM (fun k => freeJoint (energyGradient k v))
  joint_u := profileFreeJoint_measurable hDensity hSob v
  joint_U := jointProjection_stronglyMeasurable _ _
    (fun k => freeJoint_stronglyMeasurable (energyGradient k v))
  joint_V := jointProjection_stronglyMeasurable _ _
    (fun k => freeJoint_stronglyMeasurable (energyGradient k v))
  slice_eq := by
    filter_upwards [profileFreeJoint_slice hDensity hSob v,
      jointProjection_energy_ae Complex.reCLM _ _
        (freeJoint_energyGradient hDensity hSob v),
      jointProjection_energy_ae Complex.imCLM _ _
        (freeJoint_energyGradient hDensity hSob v)] with t hu hU hV
    exact ⟨hu, hU, hV⟩

/-- Actual spatial weak-gradient compatibility with the same homogeneous orbit. -/
theorem profileFreeJoint_inDotH1 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v : EnergyState) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      InDotH1 (profileFreeJoint hDensity hSob v t)
        (jointProjection Complex.reCLM (fun k => freeJoint (energyGradient k v)) t)
        (jointProjection Complex.imCLM (fun k => freeJoint (energyGradient k v)) t) :=
  (freeValueFields hDensity hSob v).inDotH1

/-- Countably many sequence indices may use one common conull time set. -/
theorem profileFreeJoint_sequence_inDotH1 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v : ℕ → EnergyState) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ,
      InDotH1 (profileFreeJoint hDensity hSob (v n) t)
        (jointProjection Complex.reCLM (fun k => freeJoint (energyGradient k (v n))) t)
        (jointProjection Complex.imCLM (fun k => freeJoint (energyGradient k (v n))) t) :=
  ae_all_iff.mpr (fun n => profileFreeJoint_inDotH1 hDensity hSob (v n))

/-- The energy-size bound uses the value L6 class and free kinetic conservation. -/
theorem profileFreeJoint_E_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v : EnergyState) :
    mixedNorm volume volume ∞ 6 (profileFreeJoint hDensity hSob v) ≤
      ENNReal.ofReal (K ^ (1/6 : ℝ) * pureGradientNorm v) := by
  have hm := spatial_lp_time_measurable (volume : Measure ℝ) volume 6
    (by norm_num) (by norm_num) (profileFreeJoint hDensity hSob v)
    (profileFreeJoint_measurable hDensity hSob v).aestronglyMeasurable
  unfold mixedNorm
  rw [eLpNorm_exponent_top hm]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [profileFreeJoint_slice hDensity hSob v] with t ht
  rw [enorm_eq_self, eLpNorm_congr_ae ht, ← Lp.enorm_def, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hb := energyValue_le_pureGradient hSob (freeEnergyState hDensity hSob t v)
  rw [freeEnergyState_pureGradientNorm hDensity hSob] at hb
  simpa only [one_div] using hb

theorem profileFreeJoint_E_finite (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v : EnergyState) :
    mixedNorm volume volume ∞ 6 (profileFreeJoint hDensity hSob v) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (profileFreeJoint_E_bound hDensity hSob v)

/-- Each coordinate has the original homogeneous Strichartz constant C. -/
theorem freeGradient_W_bound {C : ℝ} (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) (k : Fin 3) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (freeJoint (energyGradient k v)) ≤ ENNReal.ofReal (C * pureGradientNorm v) :=
  (hStr.2 _).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (energyGradient_le_pureGradient v k) hStr.1))

private theorem sum_three_ofReal (a : ℝ) (ha : 0 ≤ a) :
    (∑ _k : Fin 3, ENNReal.ofReal a) = ENNReal.ofReal (3*a) := by
  rw [Fin.sum_univ_three, ← ENNReal.ofReal_add ha ha,
    ← ENNReal.ofReal_add (add_nonneg ha ha) ha]
  congr 1
  ring

/-- Both real projected fields have the safe three-coordinate bound. -/
theorem freeProjected_W_bound {C : ℝ} (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (jointProjection L (fun k => freeJoint (energyGradient k v))) ≤
      ENNReal.ofReal (3*C*pureGradientNorm v) := by
  calc
    _ ≤ ∑ k : Fin 3, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (freeJoint (energyGradient k v)) :=
      jointProjection_mixedNorm_le L hL _
        (fun k => freeJoint_stronglyMeasurable (energyGradient k v)) _
        (by norm_num) ENNReal.ofReal_ne_top
    _ ≤ ∑ _k : Fin 3, ENNReal.ofReal (C*pureGradientNorm v) :=
      Finset.sum_le_sum (fun k _ => freeGradient_W_bound hStr v k)
    _ = _ := by rw [sum_three_ofReal _ (mul_nonneg hStr.1 (pureGradientNorm_nonneg v)), mul_assoc]

/-- The complex coordinate reconstructed from the two actual projections is
literally the same freeJoint coordinate. This identity is pointwise. -/
theorem freeProjection_complexGradient_coordinate (v : EnergyState)
    (t : ℝ) (x : Space) (k : Fin 3) :
    complexGradient
      (jointProjection Complex.reCLM (fun j => freeJoint (energyGradient j v)) t)
      (jointProjection Complex.imCLM (fun j => freeJoint (energyGradient j v)) t) x k =
        freeJoint (energyGradient k v) t x := by
  fin_cases k <;> apply Complex.ext <;>
    simp [complexGradient, jointProjection, Fin.sum_univ_three, coordinate]

/-- The actual complex Euclidean field, never the Pi maximum norm. -/
def freePackedGradient (v : EnergyState) (t : ℝ) (x : Space) :
    EuclideanSpace ℂ (Fin 3) :=
  packGradient (freeJoint (energyGradient 0 v) t x)
    (freeJoint (energyGradient 1 v) t x) (freeJoint (energyGradient 2 v) t x)

theorem freePackedGradient_coordinate (v : EnergyState) (t : ℝ) (x : Space) (k : Fin 3) :
    freePackedGradient v t x k = freeJoint (energyGradient k v) t x := by
  rw [freePackedGradient, packGradient_coordinate]
  fin_cases k <;> rfl

theorem freePackedGradient_eq_complexGradient (v : EnergyState) (t : ℝ) :
    freePackedGradient v t = complexGradient
      (jointProjection Complex.reCLM (fun k => freeJoint (energyGradient k v)) t)
      (jointProjection Complex.imCLM (fun k => freeJoint (energyGradient k v)) t) := by
  funext x
  ext k
  rw [freePackedGradient_coordinate, freeProjection_complexGradient_coordinate]

theorem freePackedGradient_stronglyMeasurable (v : EnergyState) :
    StronglyMeasurable (fun z : ℝ × Space => freePackedGradient v z.1 z.2) :=
  (((freeJoint_stronglyMeasurable (energyGradient 0 v)).smul_const
    (EuclideanSpace.basisFun (Fin 3) ℂ 0)).add
    ((freeJoint_stronglyMeasurable (energyGradient 1 v)).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℂ 1))).add
    ((freeJoint_stronglyMeasurable (energyGradient 2 v)).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℂ 2))

/-- The Euclidean W norm has the same safe three-coordinate envelope. -/
theorem freePackedGradient_W_bound {C : ℝ} (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (freePackedGradient v) ≤
      ENNReal.ofReal (3*C*pureGradientNorm v) := by
  let F (k : Fin 3) : ℝ → Space → EuclideanSpace ℂ (Fin 3) :=
    fun t x => freeJoint (energyGradient k v) t x • EuclideanSpace.basisFun (Fin 3) ℂ k
  have hm (k : Fin 3) : AEStronglyMeasurable (Function.uncurry (F k)) (volume.prod volume) :=
    ((freeJoint_stronglyMeasurable (energyGradient k v)).smul_const _).aestronglyMeasurable
  have he (k : Fin 3) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (F k) =
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (freeJoint (energyGradient k v)) := by
    unfold mixedNorm
    congr 1
    funext t
    exact coordinate_embedding_lp volume _ _
      ((freeJoint_stronglyMeasurable (energyGradient k v)).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable k
  have h01 := mixed_add_le (p := 10) (q := ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top (F 0) (F 1) (hm 0) (hm 1)
  have h012 := mixed_add_le (p := 10) (q := ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
    (fun t x => F 0 t x + F 1 t x) (F 2) ((hm 0).add (hm 1)) (hm 2)
  have hb := h012.trans (add_le_add h01 le_rfl)
  change mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (freePackedGradient v) ≤ _ at hb
  rw [he 0, he 1, he 2] at hb
  calc
    _ ≤ _ := hb
    _ ≤ ENNReal.ofReal (C*pureGradientNorm v) + ENNReal.ofReal (C*pureGradientNorm v) +
        ENNReal.ofReal (C*pureGradientNorm v) :=
      add_le_add (add_le_add (freeGradient_W_bound hStr v 0)
        (freeGradient_W_bound hStr v 1)) (freeGradient_W_bound hStr v 2)
    _ = _ := by
      have hs := sum_three_ofReal (C*pureGradientNorm v)
        (mul_nonneg hStr.1 (pureGradientNorm_nonneg v))
      simpa only [Fin.sum_univ_three, mul_assoc] using hs

theorem freeValueFields_packed_W_bound (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C) (v : EnergyState) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient ((freeValueFields hDensity hSob v).U t)
        ((freeValueFields hDensity hSob v).V t)) ≤
      ENNReal.ofReal (3*C*pureGradientNorm v) := by
  have he : (fun t => complexGradient ((freeValueFields hDensity hSob v).U t)
      ((freeValueFields hDensity hSob v).V t)) = freePackedGradient v := by
    funext t
    exact (freePackedGradient_eq_complexGradient v t).symm
  rw [he]
  exact freePackedGradient_W_bound hStr v

/-- This is also the bound on the canonical projected state gradient, via AE transport. -/
theorem freeEnergyState_projected_pureGradient_bound (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient L (freeEnergyState hDensity hSob t v)) ≤
      ENNReal.ofReal (3*C*pureGradientNorm v) := by
  rw [energyProjected_mixedNorm_eq L _ _ (freeJoint_energyGradient hDensity hSob v)]
  exact freeProjected_W_bound hStr v L hL

/-- The actual joint S domain and quantitative 10 K^(1/6) C bound.
Finiteness is supplied by the real critical Sobolev/Strichartz producer before
its real-valued estimate is consumed. All zero constants remain admissible. -/
theorem profileFreeJoint_S_finite_and_bound (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) :
    (∀ᵐ t ∂(volume : Measure ℝ), MemLp (profileFreeJoint hDensity hSob v t) 10 volume) ∧
    mixedNorm volume volume 10 10 (profileFreeJoint hDensity hSob v) ≠ ∞ ∧
    MemLp (fun t => eLpNorm (profileFreeJoint hDensity hSob v t) 10 volume) 10 volume ∧
    mixedNorm volume volume 10 10 (profileFreeJoint hDensity hSob v) ≤
      ENNReal.ofReal (10*K^(1/6 : ℝ)*C*pureGradientNorm v) := by
  have hK0 := hSob.nonneg
  have hC0 := hStr.1
  have hv0 := pureGradientNorm_nonneg v
  let g : ℝ → EnergyState := fun t => freeEnergyState hDensity hSob t v
  have : SecondCountableTopologyEither ℝ EnergyState :=
    secondCountableTopologyEither_of_left ℝ EnergyState
  have hg : AEStronglyMeasurable g volume :=
    (freeEnergyState_time_continuous hDensity hSob v).stronglyMeasurable.aestronglyMeasurable
  have hfin (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => energyProjectedGradient L (g t)) ≠ ∞ :=
    freeEnergyState_projected_finite hDensity hSob hStr v L hL
  have hmem (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
      ∀ᵐ t ∂(volume : Measure ℝ), MemLp (energyProjectedGradient L (g t))
        (ENNReal.ofReal (30/13 : ℝ)) volume :=
    finite_mixedNorm_ae_slice_memLp volume volume 10 _ (by norm_num) (by norm_num)
      _ (hfin L hL)
  have hre : ∀ z : ℂ, ‖Complex.reCLM z‖ ≤ ‖z‖ := Complex.abs_re_le_norm
  have him : ∀ z : ℂ, ‖Complex.imCLM z‖ ≤ ‖z‖ := Complex.abs_im_le_norm
  have hout := energyJointFields_critical_finite_and_bound hDensity hSob volume g hg
    (hmem Complex.reCLM hre) (hmem Complex.imCLM him)
    (hfin Complex.reCLM hre) (hfin Complex.imCLM him)
  have hsfin : mixedNorm volume volume 10 10 (profileFreeJoint hDensity hSob v) ≠ ∞ :=
    hout.2.2.1
  have hb (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
      (mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => energyProjectedGradient L (g t))).toReal ≤ 3*C*pureGradientNorm v :=
    (ENNReal.le_ofReal_iff_toReal_le (hfin L hL)
      (by positivity)).mp
      (freeEnergyState_projected_pureGradient_bound hDensity hSob hStr v L hL)
  refine ⟨hout.2.1, hsfin, hout.2.2.2.1, ?_⟩
  apply (ENNReal.le_ofReal_iff_toReal_le hsfin (by positivity)).mpr
  calc
    _ ≤ ((5/3)*K^(1/6 : ℝ)) *
        ((mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
          (fun t => energyProjectedGradient Complex.reCLM (g t))).toReal +
         (mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
          (fun t => energyProjectedGradient Complex.imCLM (g t))).toReal) := hout.2.2.2.2
    _ ≤ ((5/3)*K^(1/6 : ℝ)) * (3*C*pureGradientNorm v + 3*C*pureGradientNorm v) :=
      mul_le_mul_of_nonneg_left (add_le_add (hb Complex.reCLM hre) (hb Complex.imCLM him))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hSob.nonneg _))
    _ = 10*K^(1/6 : ℝ)*C*pureGradientNorm v := by ring

/-- The true real scalar time-L10 domain is transported from the established
canonical global-S theorem along the actual value slice identity. -/
theorem profileFreeJoint_real_time_memLp (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) :
    MemLp (fun t : ℝ => (eLpNorm (profileFreeJoint hDensity hSob v t) 10 volume).toReal)
      10 volume := by
  have hc := FreeTimeDecay.freeEnergyState_global_value_ten hDensity hSob hStr v
  apply (memLp_congr_ae ?_).mpr hc.2
  filter_upwards [profileFreeJoint_slice hDensity hSob v] with t ht
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae ht)

/-- One actual scalar coordinate packet, with no scalar L2 requirement. -/
theorem profileFreeJoint_scalarProfile (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) (k : Fin 3) :
    ScalarProfile (profileFreeJoint hDensity hSob v) (freeJoint (energyGradient k v)) :=
  ⟨profileFreeJoint_measurable hDensity hSob v, freeJoint_stronglyMeasurable _,
    profileFreeJoint_E_finite hDensity hSob v,
    (profileFreeJoint_S_finite_and_bound hDensity hSob hStr v).2.1,
    freeJoint_mixedNorm_finite hStr _⟩

/-- All three requested real bounds are converted only after finite extended domains. -/
theorem profileFreeJoint_real_bounds (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (v : EnergyState) (k : Fin 3) :
    (mixedNorm volume volume ∞ 6 (profileFreeJoint hDensity hSob v)).toReal ≤
        K^(1/6 : ℝ)*pureGradientNorm v ∧
    (mixedNorm volume volume 10 10 (profileFreeJoint hDensity hSob v)).toReal ≤
        10*K^(1/6 : ℝ)*C*pureGradientNorm v ∧
    (mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (freeJoint (energyGradient k v))).toReal ≤ C*pureGradientNorm v := by
  have hs := profileFreeJoint_S_finite_and_bound hDensity hSob hStr v
  have hK0 := hSob.nonneg
  have hC0 := hStr.1
  have hv0 := pureGradientNorm_nonneg v
  refine ⟨?_, ?_, ?_⟩
  · exact (ENNReal.le_ofReal_iff_toReal_le (profileFreeJoint_E_finite hDensity hSob v)
      (mul_nonneg (Real.rpow_nonneg hSob.nonneg _) (pureGradientNorm_nonneg v))).mp
      (profileFreeJoint_E_bound hDensity hSob v)
  · exact (ENNReal.le_ofReal_iff_toReal_le hs.2.1 (by positivity)).mp hs.2.2.2
  · exact (ENNReal.le_ofReal_iff_toReal_le (freeJoint_mixedNorm_finite hStr _)
      (mul_nonneg hStr.1 (pureGradientNorm_nonneg v))).mp (freeGradient_W_bound hStr v k)

end HartreeF.ActualFreeValue
