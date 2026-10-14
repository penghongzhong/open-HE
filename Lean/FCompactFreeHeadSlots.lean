import FFiniteProfileRieszMixed
import FFiniteProfileCrossDomains
import FCompactCrossSeeds
import FLpTopInterpolation

/-!
Compact value coefficients against an unchanged, measurable free direction.
All new declarations in this file are author-source drafts, UNCOMPILED.
The only analytic leaf used for the nonlocal terms is the existing OrdinaryHLS.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeHeadSlots
open TimeHolder ProfileApproximation GeneralProfileCross CompactCross
  LocalProfileProducts FiniteProfileMixedDefects FiniteProfileRieszMixed
  ForcingDomain WeakHartreeChain DerivativeMajorization CrossContinuity

/-- A literal zero extension, with no quotient representative chosen. -/
def localize (I : Set ℝ) (S : Set Space) (h : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => (I.prod S).indicator (Function.uncurry h) (t,x)

/-- The small quantity is the genuine nested local L2 norm. -/
def cylinderL2 (T R : ℝ) (z : Space) (h : ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm (volume.restrict (Icc (-T) T)) (volume.restrict (Metric.ball z R)) 2 2 h

theorem localize_joint {I : Set ℝ} {S : Set Space} (hI : MeasurableSet I)
    (hS : MeasurableSet S) {h : ℝ → Space → ℂ}
    (hh : StronglyMeasurable (Function.uncurry h)) :
    StronglyMeasurable (Function.uncurry (localize I S h)) :=
  hh.indicator (hI.prod hS)

theorem localize_norm_le (I : Set ℝ) (S : Set Space) (h : ℝ → Space → ℂ)
    (t : ℝ) (x : Space) : ‖localize I S h t x‖ ≤ ‖h t x‖ := by
  exact norm_indicator_le_norm_self _ _

theorem localize_spatial_support (I : Set ℝ) (S : Set Space) (h : ℝ → Space → ℂ)
    (t : ℝ) : Function.support (localize I S h t) ⊆ S := by
  intro x hx
  by_contra hxs
  exact hx (by simp [localize, hxs])

theorem localize_mixedNorm_eq (I : Set ℝ) (S : Set Space)
    (hI : MeasurableSet I) (hS : MeasurableSet S) (p q : ℝ≥0∞)
    (h : ℝ → Space → ℂ) :
    mixedNorm volume volume p q (localize I S h) =
      mixedNorm (volume.restrict I) (volume.restrict S) p q h := by
  unfold mixedNorm
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hI.nullMeasurableSet]
  congr 1
  funext t
  by_cases ht : t ∈ I
  · simp only [indicator_of_mem ht]
    have he : localize I S h t = S.indicator (h t) := by
      funext x
      simp [localize, ht]
    rw [he, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
  · have he : localize I S h t = 0 := by funext x; simp [localize, ht]
    simp [he, ht]

/-- A finite spatial support lowers the exponent without losing the true domain. -/
theorem supported_spatial_embedding {E : Type*} [NormedAddCommGroup E]
    {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) {S : Set Space}
    {f : Space → E} (hf : AEStronglyMeasurable f volume)
    (hs : Function.support f ⊆ S) :
    eLpNorm f (ENNReal.ofReal q) volume ≤
      volume S ^ (1/q-1/2 : ℝ) * eLpNorm f 2 volume := by
  have hpq : ENNReal.ofReal q ≤ (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq2
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S) hpq hf.restrict
  rw [eLpNorm_restrict_eq_of_support_subset hf hs,
    eLpNorm_restrict_eq_of_support_subset hf hs,
    Measure.restrict_apply_univ, ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofNat, mul_comm] at he
  exact he

/-- Transfer a genuine a.e. spatial norm inequality through any time exponent.
The finite coefficient is converted explicitly to NNReal; zero is permitted. -/
theorem mixed_of_slice_bound {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] {p q r : ℝ≥0∞} (hq : q ≠ 0) (hqT : q ≠ ∞)
    {f : ℝ → Space → E} {g : ℝ → Space → F}
    (hf : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hs : ∀ᵐ t ∂volume, eLpNorm (f t) q volume ≤ C * eLpNorm (g t) r volume) :
    mixedNorm volume volume p q f ≤ C * mixedNorm volume volume p r g := by
  let K : ℝ≥0 := C.toNNReal
  have hK : (K : ℝ≥0∞) = C := ENNReal.coe_toNNReal hC
  have hm := spatial_lp_time_measurable volume volume q hq hqT f hf
  have he := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (c := K) hm
    (by simpa only [enorm_eq_self, hK] using hs) p
  simpa only [mixedNorm, ENNReal.smul_def, hK] using he

theorem supported_mixed_embedding {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2)
    {S : Set Space} (hSf : volume S ≠ ∞) {h : ℝ → Space → ℂ}
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume))
    (hs : ∀ t, Function.support (h t) ⊆ S) (p : ℝ≥0∞) :
    mixedNorm volume volume p (ENNReal.ofReal q) h ≤
      volume S ^ (1/q-1/2 : ℝ) * mixedNorm volume volume p 2 h := by
  have hd : 0 ≤ 1/q-1/2 := by
    have hi := one_div_le_one_div_of_le hq hq2
    linarith
  apply mixed_of_slice_bound (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hh
    (ENNReal.rpow_ne_top_of_nonneg hd hSf)
  filter_upwards [hh.prodMk_left] with t ht
  exact supported_spatial_embedding hq hq2 ht (hs t)

/-- Spatial finite-support bounds are held in time L-infinity. -/
theorem bounded_support_mixed_top {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M) {S : Set Space}
    (hS : MeasurableSet S) (hSf : volume S ≠ ∞) {f : ℝ → Space → E}
    (hf : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume))
    (hbound : ∀ t x, ‖f t x‖ ≤ M) (hsupport : ∀ t x, x ∉ S → f t x = 0) :
    mixedNorm volume volume ∞ (ENNReal.ofReal q) f ≤
      ENNReal.ofReal M * volume S ^ (1/q) := by
  have hm := spatial_lp_time_measurable volume volume (ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top f hf
  unfold mixedNorm
  rw [eLpNorm_exponent_top hm]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [hf.prodMk_left] with t ht
  simpa only [enorm_eq_self] using
    (finite_support_lp_bound volume hq hM hS hSf ht (hbound t) (hsupport t)).2

/-- L-infinity_t L2_x and local L2_t L2_x interpolate on the SAME localized field. -/
theorem mixed_five_two_interpolate {h : ℝ → Space → ℂ}
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume))
    (hfin : mixedNorm volume volume 2 2 h ≠ ∞) :
    mixedNorm volume volume 5 2 h ≤
      mixedNorm volume volume ∞ 2 h ^ (3/5 : ℝ) *
        mixedNorm volume volume 2 2 h ^ (2/5 : ℝ) := by
  have hm := spatial_lp_time_toReal_measurable volume volume 2 (by norm_num) (by norm_num) h hh
  have hs := mixed_ae_slice (by norm_num : (2 : ℝ≥0∞) ≠ 0) h hfin
  have he := BoundedHartreeGradient.eLpNorm_interpolate_top (p := (2 : ℝ)) (q := (5 : ℝ))
    (by norm_num) (by norm_num) hm
  simpa only [ENNReal.ofReal_ofNat, show (1-2/5 : ℝ)=3/5 by norm_num,
    real_slice_mixed_eq volume 5 2 (by norm_num) (by norm_num) h hh hs,
    real_slice_mixed_eq volume ∞ 2 (by norm_num) (by norm_num) h hh hs,
    real_slice_mixed_eq volume 2 2 (by norm_num) (by norm_num) h hh hs] using he

/-- Quantitative compact Q estimate. No global S(h), W-smallness, or division by
M, the spatial volume, or the energy cap is used. -/
theorem compact_Q_bound {I : Set ℝ} {S : Set Space} (hI : MeasurableSet I)
    (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    {A h : ℝ → Space → ℂ} (hA : StronglyMeasurable (Function.uncurry A))
    (hh : StronglyMeasurable (Function.uncurry h)) {M : ℝ} (hM : 0 ≤ M)
    (hAB : ∀ t x, ‖A t x‖ ≤ M)
    (hAS : ∀ t x, (t,x) ∉ I.prod S → A t x = 0)
    (hfin : mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h ≠ ∞) :
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) A h ≤
      ENNReal.ofReal M * volume S ^ (1/30 : ℝ) *
        mixedNorm volume volume ∞ 2 h ^ (3/5 : ℝ) *
        mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h ^ (2/5 : ℝ) := by
  let H := localize I S h
  have hH := localize_joint hI hS hh
  have he : mixedNorm volume volume 2 2 H =
      mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h :=
    localize_mixedNorm_eq I S hI hS 2 2 h
  have hHfin : mixedNorm volume volume 2 2 H ≠ ∞ := by rwa [he]
  have hE : mixedNorm volume volume ∞ 2 H ≤ mixedNorm volume volume ∞ 2 h :=
    mixed_mono (by norm_num) (by norm_num) hH.aestronglyMeasurable (localize_norm_le I S h)
  have hb := mixed_le_const_mul (p := 5) (q := ENNReal.ofReal (15/8 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top hM (normProduct A h) H
    (hA.aestronglyMeasurable.norm.mul hh.aestronglyMeasurable.norm) (by
      intro t x
      by_cases hx : (t,x) ∈ I.prod S
      · simp only [H, localize, indicator_of_mem hx, Function.uncurry_apply_pair,
          normProduct, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hAB t x) (norm_nonneg _)
      · simp [normProduct, hAS t x hx, H, localize, hx])
  have hs := supported_mixed_embedding (q := (15/8 : ℝ)) (by norm_num) (by norm_num)
    hSf hH.aestronglyMeasurable (localize_spatial_support I S h) 5
  norm_num only [show (1/(15/8)-1/2 : ℝ)=1/30 by norm_num] at hs
  have ht := (mixed_five_two_interpolate hH.aestronglyMeasurable hHfin).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hE (by norm_num)) le_rfl)
  change mixedNorm volume volume 5 (ENNReal.ofReal (15/8 : ℝ)) (normProduct A h) ≤ _
  calc
    _ ≤ ENNReal.ofReal M * (volume S ^ (1/30 : ℝ) *
        (mixedNorm volume volume ∞ 2 h ^ (3/5 : ℝ) * mixedNorm volume volume 2 2 H ^ (2/5 : ℝ))) :=
      hb.trans (mul_le_mul' le_rfl (hs.trans (mul_le_mul' le_rfl ht)))
    _ = _ := by rw [he]; ring

/-- Actual mixed Q membership, obtained before using the limiting estimate. -/
theorem compact_Q_finite {I : Set ℝ} {S : Set Space} (hI : MeasurableSet I)
    (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    {A h : ℝ → Space → ℂ} (hA : StronglyMeasurable (Function.uncurry A))
    (hh : StronglyMeasurable (Function.uncurry h)) {M : ℝ} (hM : 0 ≤ M)
    (hAB : ∀ t x, ‖A t x‖ ≤ M)
    (hAS : ∀ t x, (t,x) ∉ I.prod S → A t x = 0)
    (hE : mixedNorm volume volume ∞ 2 h ≠ ∞)
    (hfin : mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h ≠ ∞) :
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) A h ≠ ∞ := by
  exact ne_top_of_le_ne_top (by finiteness)
    (compact_Q_bound hI hS hSf hA hh hM hAB hAS hfin)

/-- The two actual signed fibre integrals required by literal affine transport. -/
structure SignedFibreDomains (α c : ℝ) (u h : ℝ → Space → ℂ) : Prop where
  inner : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
    Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α (u t) (h t) y) volume
  outer : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
    Integrable (fun y => rieszKernel α c (x-y) * powerDensity α (u t) y) volume

private theorem compact_coefficient_product {M β γ δ ε : ℝ} {m C D : ℝ≥0∞}
    (hM : 0 ≤ M) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (C * ENNReal.ofReal (M^β) * m^δ) * (D * ENNReal.ofReal (M^γ) * m^ε) =
      C * D * ENNReal.ofReal (M^(β+γ)) * m^(δ+ε) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg hM hβ,
    ← ENNReal.ofReal_rpow_of_nonneg hM hγ,
    ← ENNReal.ofReal_rpow_of_nonneg hM (add_nonneg hβ hγ),
    ENNReal.rpow_add_of_nonneg β γ hβ hγ,
    ENNReal.rpow_add_of_nonneg δ ε hδ hε]
  ring

/-- Full-alpha compact estimates for the TWO literal placements. Time exponents
are (2,infinity) for inner and (infinity,2) for outer. The fixed HLS constants are
chosen before the direction field, and the signed absolute fibre domains are
retained independently of the N estimates. -/
theorem compact_slots_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ Ci Co : ℝ≥0, ∀ (I : Set ℝ) (S : Set Space),
      MeasurableSet I → MeasurableSet S → volume S ≠ ∞ →
      ∀ (A h : ℝ → Space → ℂ), StronglyMeasurable (Function.uncurry A) →
      StronglyMeasurable (Function.uncurry h) →
      ∀ M : ℝ, 0 ≤ M → (∀ t x, ‖A t x‖ ≤ M) →
      (∀ t x, (t,x) ∉ I.prod S → A t x = 0) →
      mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h ≠ ∞ →
      SignedFibreDomains α c A h ∧
      forcingNorm (innerCross α c A h A) ≠ ∞ ∧
      forcingNorm (outerCross α c A A h) ≠ ∞ ∧
      forcingNorm (innerCross α c A h A) ≤
        (Ci : ℝ≥0∞) * ENNReal.ofReal ((3+α)*M^(4+2*α)) *
          volume S ^ ((1+α)/3) * mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h ∧
      forcingNorm (outerCross α c A A h) ≤
        (Co : ℝ≥0∞) * ENNReal.ofReal ((2+α)*M^(4+2*α)) *
          volume S ^ ((1+α)/3) * mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h := by
  have ha := hHLS.order_pos
  have ha3 := hHLS.order_lt_three
  obtain ⟨hi1,hiα,hir,hirel,hiH⟩ := inner_ranges ha ha3
  obtain ⟨ho1,hoα,hor,horel,hoH⟩ := outer_ranges ha ha3
  have hiq : 0 < 12/(9+α) := by positivity
  have hiq2 : 12/(9+α) ≤ 2 := (div_le_iff₀ (by linarith : 0 < 9+α)).2 (by linarith)
  have hoq : 0 < 4/(1+α) := by positivity
  have hov : 0 < 12/(7+α) := by positivity
  have hov2 : 12/(7+α) ≤ 2 := (div_le_iff₀ (by linarith : 0 < 7+α)).2 (by linarith)
  have hid : 0 ≤ 1/(12/(9+α))-1/2 := by
    have := one_div_le_one_div_of_le hiq hiq2
    linarith
  have hod : 0 ≤ 1/(12/(7+α))-1/2 := by
    have := one_div_le_one_div_of_le hov hov2
    linarith
  letI : ENNReal.HolderTriple (ENNReal.ofReal (4/(3-α)))
      (ENNReal.ofReal (12/(1+3*α))) (ENNReal.ofReal (6/5 : ℝ)) := hiH.ennrealOfReal
  letI : ENNReal.HolderTriple (ENNReal.ofReal (12/(3-α)))
      (ENNReal.ofReal (12/(7+α))) (ENNReal.ofReal (6/5 : ℝ)) := hoH.ennrealOfReal
  obtain ⟨Ci,hCi⟩ := riesz_product_estimate (p₁ := 2) (p₂ := ∞)
    hHLS hi1 hiα hir hiH.symm.pos hirel (by norm_num) (by norm_num)
  obtain ⟨Co,hCo⟩ := riesz_product_estimate (p₁ := ∞) (p₂ := 2)
    hHLS ho1 hoα hor hov horel (by norm_num) (by norm_num)
  obtain ⟨Di,hDi⟩ := mixed_riesz_bound hHLS hi1 hiα hir hirel
  obtain ⟨Do,hDo⟩ := mixed_riesz_bound hHLS ho1 hoα hor horel
  refine ⟨Ci,Co,?_⟩
  intro I S hI hS hSf A h hA hh M hM hAB hAS hfin
  let H := localize I S h
  let ell := mixedNorm (volume.restrict I) (volume.restrict S) 2 2 h
  let fi := fun t => directionalDensity α (A t) (h t)
  let gi := fun t x => WeakHartreeChain.localFactor (1+α) (A t x)
  let fo := fun t => powerDensity α (A t)
  let go := fun t x => localFactorDerivative (1+α) (A t x) (h t x)
  have hH := localize_joint hI hS hh
  have hlocal : mixedNorm volume volume 2 2 H = ell :=
    localize_mixedNorm_eq I S hI hS 2 2 h
  have hfi : AEStronglyMeasurable (Function.uncurry fi) (volume.prod volume) :=
    density_action_measurable _ (3+α) hA.aestronglyMeasurable hh.aestronglyMeasurable
  have hgi : AEStronglyMeasurable (Function.uncurry gi) (volume.prod volume) :=
    (localFactor_contDiff_one (by linarith : 1 < 1+α)).continuous.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hfo : AEStronglyMeasurable (Function.uncurry fo) (volume.prod volume) :=
    (hA.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  have hgo : AEStronglyMeasurable (Function.uncurry go) (volume.prod volume) :=
    local_factor_action_measurable _ (1+α) hA.aestronglyMeasurable hh.aestronglyMeasurable
  have hzero (t : ℝ) (x : Space) (hx : x ∉ S) : A t x = 0 :=
    hAS t x (fun htx => hx htx.2)
  have hfiB : mixedNorm volume volume 2 (ENNReal.ofReal (12/(9+α))) fi ≤
      (ENNReal.ofReal ((3+α)*M^(2+α)) * volume S ^ (1/(12/(9+α))-1/2)) * ell := by
    have hpoint : ∀ t x, ‖fi t x‖ ≤ ((3+α)*M^(2+α)) * ‖H t x‖ := by
      intro t x
      by_cases hx : (t,x) ∈ I.prod S
      · simpa only [H, localize, indicator_of_mem hx, Function.uncurry_apply_pair] using
          (density_action_amplitude ha hM (norm_nonneg (h t x)) (hAB t x) le_rfl)
      · simp [fi, directionalDensity, hAS t x hx, densityDerivative_zero, H, localize, hx]
    have hb := mixed_le_const_mul (p := 2)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hiq)) ENNReal.ofReal_ne_top (by positivity) fi H hfi hpoint
    have he := supported_mixed_embedding hiq hiq2 hSf hH.aestronglyMeasurable
      (localize_spatial_support I S h) 2
    exact (hb.trans (mul_le_mul' le_rfl he)).trans_eq (by rw [hlocal]; ring)
  have hgiB : mixedNorm volume volume ∞ (ENNReal.ofReal (12/(1+3*α))) gi ≤
      ENNReal.ofReal (M^(2+α)) * volume S ^ (1/(12/(1+3*α))) := by
    apply bounded_support_mixed_top hiH.symm.pos (by positivity) hS hSf hgi
    · intro t x
      rw [show gi t x = WeakHartreeChain.localFactor (1+α) (A t x) from rfl,
        localFactor_norm (by linarith : 0 < 1+α), show 1+α+1=2+α by ring]
      exact Real.rpow_le_rpow (norm_nonneg _) (hAB t x) (by linarith)
    · intro t x hx
      simp [gi, WeakHartreeChain.localFactor, hzero t x hx]
  have hfoB : mixedNorm volume volume ∞ (ENNReal.ofReal (4/(1+α))) fo ≤
      ENNReal.ofReal (M^(3+α)) * volume S ^ (1/(4/(1+α))) := by
    apply bounded_support_mixed_top hoq (by positivity) hS hSf hfo
    · intro t x
      change ‖‖A t x‖^(3+α)‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hAB t x) (by linarith)
    · intro t x hx
      simp [fo, powerDensity, hzero t x hx, Real.zero_rpow (by linarith : 3+α ≠ 0)]
  have hgoB : mixedNorm volume volume 2 (ENNReal.ofReal (12/(7+α))) go ≤
      (ENNReal.ofReal ((2+α)*M^(1+α)) * volume S ^ (1/(12/(7+α))-1/2)) * ell := by
    have hpoint : ∀ t x, ‖go t x‖ ≤ ((2+α)*M^(1+α)) * ‖H t x‖ := by
      intro t x
      by_cases hx : (t,x) ∈ I.prod S
      · simpa only [H, localize, indicator_of_mem hx, Function.uncurry_apply_pair] using
          (local_action_amplitude ha hM (norm_nonneg (h t x)) (hAB t x) le_rfl)
      · simp [go, hAS t x hx, localFactorDerivative_zero (by linarith : 0 < 1+α), H, localize, hx]
    have hb := mixed_le_const_mul (p := 2)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hov)) ENNReal.ofReal_ne_top (by positivity) go H hgo hpoint
    have he := supported_mixed_embedding hov hov2 hSf hH.aestronglyMeasurable
      (localize_spatial_support I S h) 2
    exact (hb.trans (mul_le_mul' le_rfl he)).trans_eq (by rw [hlocal]; ring)
  have hell : ell ≠ ∞ := hfin
  have hif : mixedNorm volume volume 2 (ENNReal.ofReal (12/(9+α))) fi ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hid hSf)) hell) hfiB
  have hig : mixedNorm volume volume ∞ (ENNReal.ofReal (12/(1+3*α))) gi ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hiH.symm.pos)) hSf)) hgiB
  have hof : mixedNorm volume volume ∞ (ENNReal.ofReal (4/(1+α))) fo ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hoq)) hSf)) hfoB
  have hog : mixedNorm volume volume 2 (ENNReal.ofReal (12/(7+α))) go ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hod hSf)) hell) hgoB
  have hi := hCi fi gi hfi hgi hif hig
  have ho := hCo fo go hfo hgo hof hog
  have hdi := (hDi 2 (by norm_num) fi hfi hif).1
  have hdo := (hDo ∞ (by norm_num) fo hfo hof).1
  refine ⟨⟨hdi,hdo⟩,hi.1,ho.1,?_,?_⟩
  · have he : (1/(12/(9+α))-1/2)+(1/(12/(1+3*α))) = (1+α)/3 := by
      simp only [one_div, inv_div]; ring
    have hp := compact_coefficient_product (m := volume S)
      (C := ENNReal.ofReal (3+α)) (D := 1) hM
      (show 0 ≤ 2+α by linarith) (show 0 ≤ 2+α by linarith)
      hid (le_of_lt (one_div_pos.mpr hiH.symm.pos))
    simp only [one_mul, mul_one] at hp
    rw [show (2+α)+(2+α)=4+2*α by ring, he] at hp
    have hb := hi.2.trans (mul_le_mul' (mul_le_mul' le_rfl hfiB) hgiB)
    calc
      _ ≤ (Ci : ℝ≥0∞) *
          ((ENNReal.ofReal ((3+α)*M^(2+α)) * volume S ^ (1/(12/(9+α))-1/2)) * ell) *
          (ENNReal.ofReal (M^(2+α)) * volume S ^ (1/(12/(1+3*α)))) := hb
      _ = _ := by
        rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 3+α),
          ENNReal.ofReal_mul (by linarith : 0 ≤ 3+α)]
        calc
          _ = (Ci : ℝ≥0∞) *
              ((ENNReal.ofReal (3+α) * ENNReal.ofReal (M^(2+α)) * volume S ^ (1/(12/(9+α))-1/2)) *
                (ENNReal.ofReal (M^(2+α)) * volume S ^ (1/(12/(1+3*α))))) * ell := by ring
          _ = _ := by rw [hp]; ring
  · have he : (1/(4/(1+α)))+(1/(12/(7+α))-1/2) = (1+α)/3 := by
      simp only [one_div, inv_div]; ring
    have hp := compact_coefficient_product (m := volume S)
      (C := 1) (D := ENNReal.ofReal (2+α)) hM
      (show 0 ≤ 3+α by linarith) (show 0 ≤ 1+α by linarith)
      (le_of_lt (one_div_pos.mpr hoq)) hod
    simp only [one_mul, mul_one] at hp
    rw [show (3+α)+(1+α)=4+2*α by ring, he] at hp
    have hb := ho.2.trans (mul_le_mul' (mul_le_mul' le_rfl hfoB) hgoB)
    calc
      _ ≤ (Co : ℝ≥0∞) *
          (ENNReal.ofReal (M^(3+α)) * volume S ^ (1/(4/(1+α)))) *
          ((ENNReal.ofReal ((2+α)*M^(1+α)) * volume S ^ (1/(12/(7+α))-1/2)) * ell) := hb
      _ = _ := by
        rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 2+α),
          ENNReal.ofReal_mul (by linarith : 0 ≤ 2+α)]
        calc
          _ = (Co : ℝ≥0∞) *
              ((ENNReal.ofReal (M^(3+α)) * volume S ^ (1/(4/(1+α)))) *
                (ENNReal.ofReal (2+α) * ENNReal.ofReal (M^(1+α)) * volume S ^ (1/(12/(7+α))-1/2))) * ell := by ring
          _ = _ := by rw [hp]; ring

/-- A continuous compact coefficient has one positive finite cylinder. -/
theorem compact_seed_cylinder {A : ℝ → Space → ℂ}
    (hA : HasCompactSupport (Function.uncurry A)) :
    ∃ T R : ℝ, 0 < T ∧ 0 < R ∧
      ∀ t x, (t,x) ∉ (Icc (-T) T).prod (Metric.ball (0 : Space) R) → A t x = 0 := by
  have hk : IsCompact (tsupport (Function.uncurry A)) := hA
  obtain ⟨T,hT,hTI⟩ := (hk.image continuous_fst).isBounded.subset_ball_lt 0 (0 : ℝ)
  obtain ⟨R,hR,hRS⟩ := (hk.image continuous_snd).isBounded.subset_ball_lt 0 (0 : Space)
  refine ⟨T,R,hT,hR,?_⟩
  intro t x htx
  by_contra hz
  have hz' : (t,x) ∈ tsupport (Function.uncurry A) := subset_tsupport _ hz
  have ht : |t| < T := by simpa [Metric.mem_ball, Real.dist_eq] using hTI ⟨(t,x),hz',rfl⟩
  have hx : x ∈ Metric.ball (0 : Space) R := hRS ⟨(t,x),hz',rfl⟩
  exact htx ⟨⟨(abs_lt.mp ht).1.le,(abs_lt.mp ht).2.le⟩,hx⟩

/-- A reusable comparison with a finite constant and a strictly positive power.
This includes zero constants and zero norm values. -/
theorem tendsto_zero_of_power_bound {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ≥0∞} {C : ℝ≥0∞} {p : ℝ} (hC : C ≠ ∞) (hp : 0 < p)
    (ha : Tendsto a l (𝓝 0)) (hb : ∀ n, b n ≤ C * a n ^ p) :
    Tendsto b l (𝓝 0) := by
  have ht := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hp).comp ha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

/-- The compact conclusion consumes only the actual finite-cylinder domains,
their original-sequence limit, joint measurability, and an all-index E cap. -/
theorem compact_free_head_zero {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {A : ℝ → Space → ℂ} (hA : Continuous (Function.uncurry A))
    (hAC : HasCompactSupport (Function.uncurry A))
    {h : ℕ → ℝ → Space → ℂ}
    (hh : ∀ n, StronglyMeasurable (Function.uncurry (h n)))
    (bE : ℝ≥0) (hE : ∀ n, mixedNorm volume volume ∞ 2 (h n) ≤ bE)
    (hlf : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R → ∀ n, cylinderL2 T R z (h n) ≠ ∞)
    (hl0 : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R →
      Tendsto (fun n => cylinderL2 T R z (h n)) atTop (𝓝 0)) :
    (∀ n, SignedFibreDomains α c A (h n) ∧
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) A (h n) ≠ ∞ ∧
      forcingNorm (innerCross α c A (h n) A) ≠ ∞ ∧
      forcingNorm (outerCross α c A A (h n)) ≠ ∞) ∧
    Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) A (h n)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (innerCross α c A (h n) A)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (outerCross α c A A (h n))) atTop (𝓝 0) := by
  obtain ⟨M,hM,hAB⟩ := compact_seed_amplitude hA hAC
  obtain ⟨T,R,hT,hR,hAS⟩ := compact_seed_cylinder hAC
  let I := Icc (-T) T
  let S := Metric.ball (0 : Space) R
  have hI : MeasurableSet I := measurableSet_Icc
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hSf : volume S ≠ ∞ := (Metric.isBounded_ball.measure_lt_top).ne
  obtain ⟨Ci,Co,hC⟩ := compact_slots_bound hHLS
  have hslots (n : ℕ) := hC I S hI hS hSf A (h n) hA.stronglyMeasurable (hh n)
    M hM hAB hAS (hlf T R 0 hT hR n)
  have hQ (n : ℕ) : localProductNorm (ENNReal.ofReal (15/8 : ℝ)) A (h n) ≤
      (ENNReal.ofReal M * volume S ^ (1/30 : ℝ) * (bE : ℝ≥0∞) ^ (3/5 : ℝ)) *
        cylinderL2 T R 0 (h n) ^ (2/5 : ℝ) := by
    exact (compact_Q_bound hI hS hSf hA.stronglyMeasurable (hh n) hM hAB hAS
      (hlf T R 0 hT hR n)).trans (mul_le_mul'
        (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hE n) (by norm_num))) le_rfl)
  have ha := hHLS.order_pos
  refine ⟨?_,?_,?_,?_⟩
  · intro n
    exact ⟨(hslots n).1,ne_top_of_le_ne_top (by have := hlf T R 0 hT hR n; finiteness) (hQ n),
      (hslots n).2.1,(hslots n).2.2.1⟩
  · exact tendsto_zero_of_power_bound (by finiteness) (by norm_num) (hl0 T R 0 hT hR) hQ
  · apply tendsto_zero_of_power_bound
      (C := (Ci : ℝ≥0∞) * ENNReal.ofReal ((3+α)*M^(4+2*α)) * volume S ^ ((1+α)/3))
      (p := 1) (by have hp : 0 ≤ (1+α)/3 := by positivity; finiteness) (by norm_num)
      (hl0 T R 0 hT hR)
    intro n
    simpa only [ENNReal.rpow_one] using (hslots n).2.2.2.1
  · apply tendsto_zero_of_power_bound
      (C := (Co : ℝ≥0∞) * ENNReal.ofReal ((2+α)*M^(4+2*α)) * volume S ^ ((1+α)/3))
      (p := 1) (by have hp : 0 ≤ (1+α)/3 := by positivity; finiteness) (by norm_num)
      (hl0 T R 0 hT hR)
    intro n
    simpa only [ENNReal.rpow_one] using (hslots n).2.2.2.2

/-- The pure coefficient ledger supplies absolute signed fibres at EACH index.
N-finiteness or an asymptotic statement is never used as a fibre witness. -/
theorem scalar_signed_fibre_domains {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h) : SignedFibreDomains α c u h := by
  have ha := hHLS.order_pos
  have ha3 := hHLS.order_lt_three
  have hr0 : 0 < 10/(3-α) := div_pos (by norm_num) (by linarith)
  have hr1 : 0 < 90/(19*(3-α)) := div_pos (by norm_num)
    (mul_pos (by norm_num) (by linarith))
  obtain ⟨hq01,hq0α,hq11,hq1α,_⟩ := ledger_hls_interior ha ha3
  have hrel0 : 1/(10/(3-α)) = 1/(30/(9+7*α))-α/3 := by
    simp only [one_div, inv_div]; ring
  have hrel1 : 1/(90/(19*(3-α))) = 1/(90/(57+11*α))-α/3 := by
    simp only [one_div, inv_div]; ring
  have hx0 : x0 α = ENNReal.ofReal (30/(9+7*α)) := by
    rw [x0, reciprocal_eq (by linarith : 0 < (9+7*α)/30)]
    simp only [inv_div]
  have hx1 : x1 α = ENNReal.ofReal (90/(57+11*α)) := by
    rw [x1, reciprocal_eq (by linarith : 0 < (57+11*α)/90)]
    simp only [inv_div]
  have hm := pure_coefficients_joint ha hu
  have hf := pure_coefficients_finite ha ha3 hu
  obtain ⟨C0,hC0⟩ := mixed_riesz_bound hHLS hq01 hq0α hr0 hrel0
  obtain ⟨C1,hC1⟩ := mixed_riesz_bound hHLS hq11 hq1α hr1 hrel1
  have h0 := (hC0 (t0 α) (reciprocal_ne_zero _) (pureDensity α u)
    hm.1.aestronglyMeasurable (by simpa only [hx0] using hf.1)).1
  have h1 := (hC1 (t1 α) (reciprocal_ne_zero _) (pureDensityDerivative α u h)
    hm.2.1.aestronglyMeasurable (by simpa only [hx1] using hf.2.1)).1
  refine ⟨?_,?_⟩
  · simpa only [pureDensityDerivative, directionalDensity] using h1
  · simpa only [pureDensity, density, powerDensity] using h0

/-- Genuine mixed domains, with actual target fields and both norm layers. -/
structure HeadMixedDomains (α c : ℝ) (u h : ℝ → Space → ℂ) : Prop where
  Q_joint : AEStronglyMeasurable (Function.uncurry (normProduct u h)) (volume.prod volume)
  Q_slices : ∀ᵐ t ∂volume, MemLp (normProduct u h t) (ENNReal.ofReal (15/8 : ℝ)) volume
  Q_time : MemLp (fun t => eLpNorm (normProduct u h t) (ENNReal.ofReal (15/8 : ℝ)) volume) 5 volume
  inner_joint : AEStronglyMeasurable (Function.uncurry (innerCross α c u h u)) (volume.prod volume)
  inner_slices : ∀ᵐ t ∂volume, MemLp (innerCross α c u h u t) (ENNReal.ofReal (6/5 : ℝ)) volume
  inner_time : MemLp (fun t => eLpNorm (innerCross α c u h u t) (ENNReal.ofReal (6/5 : ℝ)) volume) 2 volume
  outer_joint : AEStronglyMeasurable (Function.uncurry (outerCross α c u u h)) (volume.prod volume)
  outer_slices : ∀ᵐ t ∂volume, MemLp (outerCross α c u u h t) (ENNReal.ofReal (6/5 : ℝ)) volume
  outer_time : MemLp (fun t => eLpNorm (outerCross α c u u h t) (ENNReal.ofReal (6/5 : ℝ)) volume) 2 volume

/-- Extended-norm finiteness gives the genuine memberships of the SAME fields;
this conversion is performed independently at every original index. -/
theorem head_mixed_domains_of_finite {α c : ℝ} {u h : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume))
    (hQ : localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u h ≠ ∞)
    (hi : forcingNorm (innerCross α c u h u) ≠ ∞)
    (ho : forcingNorm (outerCross α c u u h) ≠ ∞) : HeadMixedDomains α c u h := by
  exact ⟨hu.norm.mul hh.norm,
    mixed_ae_slice (by norm_num : (5 : ℝ≥0∞) ≠ 0) (normProduct u h) hQ,
    lt_top_iff_ne_top.mpr hQ,
    inner_joint_measurable α c hu hh hu,
    mixed_ae_slice (by norm_num : (2 : ℝ≥0∞) ≠ 0) (innerCross α c u h u) hi,
    lt_top_iff_ne_top.mpr hi,
    outer_joint_measurable α c hu hu hh,
    mixed_ae_slice (by norm_num : (2 : ℝ≥0∞) ≠ 0) (outerCross α c u u h) ho,
    lt_top_iff_ne_top.mpr ho⟩

end HartreeF.FreeHeadSlots
