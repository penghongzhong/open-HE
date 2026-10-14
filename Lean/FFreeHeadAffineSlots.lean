import FCriticalAffineEnergy
import FFiniteProfileRieszMixed
import FGeneralRepresentativeTransport
import FLocalProductRepresentatives

/-! Literal common-frame covariance for the two independent derivative slots.
Every power scalar is positive. Signed fibre domains are transported separately
from the totalized integral identities. Static candidate, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FreeHeadFrames
open EnergySpace SobolevStretch CriticalAffine AffineMixed CompactCross
  ForcingDomain WeakHartreeChain DerivativeMajorization TimeHolder
  GeneralProfileCross LocalProfileProducts

theorem densityDerivative_power_smul {a : ℝ} (ha : 0 < a)
    (p β γ : ℝ) (z w : ℂ) :
    densityDerivative p (a^β • z) (a^γ • w) =
      a^(β*(p-1)+γ) * densityDerivative p z w := by
  by_cases hz : z = 0
  · simp only [hz, smul_zero, densityDerivative_zero, zero_apply, mul_zero]
  simp only [densityDerivative, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha β),
    real_inner_smul_left, real_inner_smul_right]
  rw [Real.mul_rpow (Real.rpow_nonneg ha.le β) (norm_nonneg z),
    ← Real.rpow_mul ha.le]
  calc
    _ = (a^(β*(p-2)) * a^β * a^γ) *
        (p * ‖z‖^(p-2) * inner ℝ z w) := by ring
    _ = _ := by
      rw [← Real.rpow_add ha, ← Real.rpow_add ha]
      congr 1
      congr 1
      ring

theorem localFactor_power_smul {a : ℝ} (ha : 0 < a)
    (p β : ℝ) (z : ℂ) :
    localFactor p (a^β • z) = a^(β*(p+1)) • localFactor p z := by
  simp only [localFactor, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ha β)]
  rw [Real.mul_rpow (Real.rpow_nonneg ha.le β) (norm_nonneg z),
    ← Real.rpow_mul ha.le]
  simp only [smul_smul]
  have he : (a^(β*p) * ‖z‖^p) * a^β = a^(β*(p+1)) * ‖z‖^p := by
    calc
      _ = (a^(β*p) * a^β) * ‖z‖^p := by ring
      _ = _ := by rw [← Real.rpow_add ha]; congr 1; congr 1; ring
  rw [he]

theorem localFactorDerivative_power_smul {a : ℝ} (ha : 0 < a)
    {p : ℝ} (hp : 0 < p) (β γ : ℝ) (z w : ℂ) :
    localFactorDerivative p (a^β • z) (a^γ • w) =
      a^(β*p+γ) • localFactorDerivative p z w := by
  by_cases hz : z = 0
  · simp only [hz, smul_zero, localFactorDerivative_zero hp, zero_apply]
  have he : a^(β*(p-1)+γ) * a^β = a^(β*p+γ) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have hn : ‖a^β • z‖^p = a^(β*p) * ‖z‖^p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha β),
      Real.mul_rpow (Real.rpow_nonneg ha.le β) (norm_nonneg z),
      ← Real.rpow_mul ha.le]
  change ‖a^β • z‖^p • (a^γ • w) +
      densityDerivative p (a^β • z) (a^γ • w) • (a^β • z) =
    a^(β*p+γ) • (‖z‖^p • w + densityDerivative p z w • z)
  rw [hn, densityDerivative_power_smul ha]
  simp only [smul_add, smul_smul]
  have he₁ : (a^(β*p) * ‖z‖^p) * a^γ = a^(β*p+γ) * ‖z‖^p := by
    calc
      _ = (a^(β*p) * a^γ) * ‖z‖^p := by ring
      _ = _ := by rw [Real.rpow_add ha]
  have he₂ : (a^(β*(p-1)+γ) * densityDerivative p z w) * a^β =
      a^(β*p+γ) * densityDerivative p z w := by
    calc
      _ = (a^(β*(p-1)+γ) * a^β) * densityDerivative p z w := by ring
      _ = _ := by rw [he]
  rw [he₁, he₂]

theorem powerDensity_power_smul {a : ℝ} (ha : 0 < a)
    (α β : ℝ) (u : Space → ℂ) (x : Space) :
    powerDensity α (fun y => a^β • u y) x = a^(β*(3+α)) * powerDensity α u x := by
  simp only [powerDensity, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ha β)]
  rw [Real.mul_rpow (Real.rpow_nonneg ha.le β) (norm_nonneg _),
    ← Real.rpow_mul ha.le]

theorem inverse_kernel_scale (α c : ℝ) {a : ℝ} (ha : 0 < a) (b x y : Space) :
    rieszKernel α c (x-y) = a^(3-α) * rieszKernel α c (affine a b x-affine a b y) := by
  have he : a^(3-α) * a^(α-3) = 1 := by
    rw [← Real.rpow_add ha]
    norm_num [show (3-α)+(α-3)=0 by ring]
  rw [rieszKernel_affine_sub α c ha b, ← mul_assoc, he, one_mul]

theorem scaled_riesz_integrand (α c β : ℝ) {a : ℝ} (ha : 0 < a)
    (b x y : Space) (f : Space → ℝ) :
    rieszKernel α c (x-y) * (a^β * f (affine a b y)) =
      a^(3+β-α) * (rieszKernel α c (affine a b x-affine a b y) * f (affine a b y)) := by
  rw [inverse_kernel_scale α c ha b]
  have he : a^(3-α) * a^β = a^(3+β-α) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = (a^(3-α) * a^β) *
        (rieszKernel α c (affine a b x-affine a b y) * f (affine a b y)) := by ring
    _ = _ := by rw [he]

/-- Actual signed fibre transport is established before using the integral identity. -/
theorem scaled_riesz_fibre_integrable (α c β : ℝ) {a : ℝ} (ha : 0 < a)
    (b x : Space) (f : Space → ℝ)
    (hf : Integrable (fun y => rieszKernel α c (affine a b x-y) * f y) volume) :
    Integrable (fun y => rieszKernel α c (x-y) * (a^β * f (affine a b y))) volume := by
  have hi := (affine_integrable ha.ne' b hf).const_mul (a^(3+β-α))
  exact hi.congr (Eventually.of_forall (fun y =>
    (scaled_riesz_integrand α c β ha b x y f).symm))

theorem rieszConvolution_power_pullback (α c β : ℝ) {a : ℝ} (ha : 0 < a)
    (b : Space) (f : Space → ℝ) (x : Space) :
    rieszConvolution α c (fun y => a^β * f (affine a b y)) x =
      a^(β-α) * rieszConvolution α c f (affine a b x) := by
  have hj : a^(3+β-α) * (a^3)⁻¹ = a^(β-α) := by
    have hp : (a^3)⁻¹ = a^(-(3:ℝ)) := by
      rw [Real.rpow_neg ha.le]
      norm_num
    rw [hp, ← Real.rpow_add ha]
    congr 1
    ring
  unfold rieszConvolution
  calc
    _ = a^(3+β-α) * ∫ y,
        rieszKernel α c (affine a b x-affine a b y) * f (affine a b y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => scaled_riesz_integrand α c β ha b x y f)
    _ = _ := by
      rw [affine_integral ha b
        (fun y => rieszKernel α c (affine a b x-y) * f y), smul_eq_mul,
        ← mul_assoc, hj]

theorem directionalDensity_parabolic {a : ℝ} (ha : 0 < a) (α : ℝ)
    (b : Space) (s : ℝ) (u h : ℝ → Space → ℂ) (t : ℝ) (x : Space) :
    directionalDensity α (parabolicField a b s (1/2) u t)
        (parabolicField a b s (3/2) h t) x =
      a^((5+α)/2) * directionalDensity α
        (u (timeAffine a s t)) (h (timeAffine a s t)) (affine a b x) := by
  simp only [directionalDensity, parabolicField, densityDerivative_power_smul ha]
  congr 2
  ring


theorem density_parabolic {a : ℝ} (ha : 0 < a) (α : ℝ)
    (b : Space) (s : ℝ) (u : ℝ → Space → ℂ) (t : ℝ) (x : Space) :
    powerDensity α (parabolicField a b s (1/2) u t) x =
      a^((3+α)/2) * powerDensity α (u (timeAffine a s t)) (affine a b x) := by
  change powerDensity α (fun y => a^(1/2:ℝ) •
      u (timeAffine a s t) (affine a b y)) x = _
  rw [powerDensity_power_smul ha]
  congr 2
  ring

theorem directional_potential_parabolic {a : ℝ} (ha : 0 < a) (α c : ℝ)
    (b : Space) (s : ℝ) (u h : ℝ → Space → ℂ) (t : ℝ) (x : Space) :
    rieszConvolution α c (directionalDensity α (parabolicField a b s (1/2) u t)
      (parabolicField a b s (3/2) h t)) x =
      a^((5-α)/2) * rieszConvolution α c
        (directionalDensity α (u (timeAffine a s t)) (h (timeAffine a s t)))
        (affine a b x) := by
  have hf : directionalDensity α (parabolicField a b s (1/2) u t)
      (parabolicField a b s (3/2) h t) =
      (fun y => a^((5+α)/2) * directionalDensity α
        (u (timeAffine a s t)) (h (timeAffine a s t)) (affine a b y)) := by
    funext y
    exact directionalDensity_parabolic ha α b s u h t y
  rw [hf, rieszConvolution_power_pullback α c _ ha]
  congr 2
  ring

theorem potential_parabolic {a : ℝ} (ha : 0 < a) (α c : ℝ)
    (b : Space) (s : ℝ) (u : ℝ → Space → ℂ) (t : ℝ) (x : Space) :
    potential α c (parabolicField a b s (1/2) u t) x =
      a^((3-α)/2) * potential α c (u (timeAffine a s t)) (affine a b x) := by
  have hf : powerDensity α (parabolicField a b s (1/2) u t) =
      (fun y => a^((3+α)/2) * powerDensity α (u (timeAffine a s t)) (affine a b y)) := by
    funext y
    exact density_parabolic ha α b s u t y
  change rieszConvolution α c (powerDensity α (parabolicField a b s (1/2) u t)) x = _
  rw [hf, rieszConvolution_power_pullback α c _ ha]
  change a^((3+α)/2-α) * potential α c (u (timeAffine a s t)) (affine a b x) = _
  congr 2
  ring

theorem innerCross_parabolic {a : ℝ} (ha : 0 < a) (α c : ℝ)
    (b : Space) (s : ℝ) (u h v : ℝ → Space → ℂ) :
    innerCross α c (parabolicField a b s (1/2) u)
      (parabolicField a b s (3/2) h) (parabolicField a b s (1/2) v) =
      parabolicField a b s (7/2) (innerCross α c u h v) := by
  funext t x
  change rieszConvolution α c (directionalDensity α
      (parabolicField a b s (1/2) u t) (parabolicField a b s (3/2) h t)) x •
      localFactor (1+α) (a^(1/2:ℝ) • v (timeAffine a s t) (affine a b x)) = _
  rw [directional_potential_parabolic ha α c, localFactor_power_smul ha]
  change (a^((5-α)/2) * rieszConvolution α c
      (directionalDensity α (u (timeAffine a s t)) (h (timeAffine a s t)))
      (affine a b x)) • (a^((1/2:ℝ)*((1+α)+1)) •
      localFactor (1+α) (v (timeAffine a s t) (affine a b x))) =
    a^(7/2:ℝ) • (rieszConvolution α c
      (directionalDensity α (u (timeAffine a s t)) (h (timeAffine a s t)))
      (affine a b x) • localFactor (1+α) (v (timeAffine a s t) (affine a b x)))
  simp only [smul_smul]
  have hp : a^((5-α)/2) * a^((1/2:ℝ)*((1+α)+1)) = a^(7/2:ℝ) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  congr 1
  calc
    _ = (a^((5-α)/2) * a^((1/2:ℝ)*((1+α)+1))) *
        rieszConvolution α c (directionalDensity α (u (timeAffine a s t))
          (h (timeAffine a s t))) (affine a b x) := by ring
    _ = _ := by rw [hp]

theorem outerCross_parabolic {a α : ℝ} (ha : 0 < a) (hα : 0 < α) (c : ℝ)
    (b : Space) (s : ℝ) (u v h : ℝ → Space → ℂ) :
    outerCross α c (parabolicField a b s (1/2) u)
      (parabolicField a b s (1/2) v) (parabolicField a b s (3/2) h) =
      parabolicField a b s (7/2) (outerCross α c u v h) := by
  funext t x
  change potential α c (parabolicField a b s (1/2) u t) x •
      localFactorDerivative (1+α) (a^(1/2:ℝ) • v (timeAffine a s t) (affine a b x))
        (a^(3/2:ℝ) • h (timeAffine a s t) (affine a b x)) = _
  rw [potential_parabolic ha α c,
    localFactorDerivative_power_smul ha (by linarith : 0 < 1+α)]
  change (a^((3-α)/2) * potential α c (u (timeAffine a s t)) (affine a b x)) •
      (a^((1/2:ℝ)*(1+α)+3/2) •
        localFactorDerivative (1+α) (v (timeAffine a s t) (affine a b x))
          (h (timeAffine a s t) (affine a b x))) =
    a^(7/2:ℝ) • (potential α c (u (timeAffine a s t)) (affine a b x) •
      localFactorDerivative (1+α) (v (timeAffine a s t) (affine a b x))
        (h (timeAffine a s t) (affine a b x)))
  simp only [smul_smul]
  have hp : a^((3-α)/2) * a^((1/2:ℝ)*(1+α)+3/2) = a^(7/2:ℝ) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  congr 1
  calc
    _ = (a^((3-α)/2) * a^((1/2:ℝ)*(1+α)+3/2)) *
        potential α c (u (timeAffine a s t)) (affine a b x) := by ring
    _ = _ := by rw [hp]

theorem innerCross_joint (α c : ℝ) {u h v : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume))
    (hv : AEStronglyMeasurable (Function.uncurry v) (volume.prod volume)) :
    AEStronglyMeasurable (Function.uncurry (innerCross α c u h v)) (volume.prod volume) := by
  exact (joint_riesz_measurable volume α c (fun t => directionalDensity α (u t) (h t))
    (density_action_measurable (volume.prod volume) (3+α) hu hh)).smul
      ((hv.norm.aemeasurable.pow_const (1+α)).aestronglyMeasurable.smul hv)

theorem outerCross_joint (α c : ℝ) {u v h : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hv : AEStronglyMeasurable (Function.uncurry v) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume)) :
    AEStronglyMeasurable (Function.uncurry (outerCross α c u v h)) (volume.prod volume) := by
  exact (joint_riesz_measurable volume α c (fun t x => powerDensity α (u t) x)
    (hu.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable).smul
      (local_factor_action_measurable (volume.prod volume) (1+α) hv hh)

theorem seedFrame_inner_N (α c : ℝ) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) (u h v : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume))
    (hv : AEStronglyMeasurable (Function.uncurry v) (volume.prod volume)) :
    forcingNorm (innerCross α c (seedFrame a y s (1/2) u)
      (seedFrame a y s (3/2) h) (seedFrame a y s (1/2) v)) =
      forcingNorm (innerCross α c u h v) := by
  change forcingNorm (innerCross α c (parabolicField a⁻¹ (-(a⁻¹ • y)) s (1/2) u)
    (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) h)
    (parabolicField a⁻¹ (-(a⁻¹ • y)) s (1/2) v)) = _
  rw [innerCross_parabolic (inv_pos.mpr ha)]
  have hscale := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (7/2)
    Set.univ 2 (ENNReal.ofReal (6/5:ℝ)) (by norm_num) ENNReal.ofReal_ne_top
    (innerCross α c u h v) (by simpa using innerCross_joint α c hu hh hv)
  norm_num [reciprocalExponent] at hscale
  exact hscale

theorem seedFrame_outer_N {α : ℝ} (hα : 0 < α) (c : ℝ) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) (u v h : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hv : AEStronglyMeasurable (Function.uncurry v) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume)) :
    forcingNorm (outerCross α c (seedFrame a y s (1/2) u)
      (seedFrame a y s (1/2) v) (seedFrame a y s (3/2) h)) =
      forcingNorm (outerCross α c u v h) := by
  change forcingNorm (outerCross α c (parabolicField a⁻¹ (-(a⁻¹ • y)) s (1/2) u)
    (parabolicField a⁻¹ (-(a⁻¹ • y)) s (1/2) v)
    (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) h)) = _
  rw [outerCross_parabolic (inv_pos.mpr ha) hα]
  have hscale := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (7/2)
    Set.univ 2 (ENNReal.ofReal (6/5:ℝ)) (by norm_num) ENNReal.ofReal_ne_top
    (outerCross α c u v h) (by simpa using outerCross_joint α c hu hv hh)
  norm_num [reciprocalExponent] at hscale
  exact hscale

theorem normProduct_parabolic {a : ℝ} (ha : 0 < a) (b : Space) (s : ℝ)
    (u h : ℝ → Space → ℂ) :
    normProduct (parabolicField a b s (1/2) u) (parabolicField a b s (3/2) h) =
      parabolicField a b s 2 (normProduct u h) := by
  funext t x
  simp only [normProduct, parabolicField, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ha (1/2:ℝ)),
    abs_of_pos (Real.rpow_pos_of_pos ha (3/2:ℝ)), smul_eq_mul]
  have hp : a^(1/2:ℝ) * a^(3/2:ℝ) = a^(2:ℝ) := by
    rw [← Real.rpow_add ha]
    norm_num
  calc
    _ = (a^(1/2:ℝ) * a^(3/2:ℝ)) *
      (‖u (timeAffine a s t) (affine a b x)‖ * ‖h (timeAffine a s t) (affine a b x)‖) := by ring
    _ = _ := by rw [hp]

theorem seedFrame_Q {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ)
    (u h : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (Function.uncurry u) (volume.prod volume))
    (hh : AEStronglyMeasurable (Function.uncurry h) (volume.prod volume)) :
    localProductNorm (ENNReal.ofReal (15/8:ℝ)) (seedFrame a y s (1/2) u)
      (seedFrame a y s (3/2) h) = localProductNorm (ENNReal.ofReal (15/8:ℝ)) u h := by
  change mixedNorm volume volume 5 (ENNReal.ofReal (15/8:ℝ))
    (normProduct (parabolicField a⁻¹ (-(a⁻¹ • y)) s (1/2) u)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) h)) = _
  rw [normProduct_parabolic (inv_pos.mpr ha)]
  have hscale := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s 2
    Set.univ 5 (ENNReal.ofReal (15/8:ℝ)) (by norm_num) ENNReal.ofReal_ne_top
    (normProduct u h) (by simpa using hu.norm.mul hh.norm)
  norm_num [reciprocalExponent] at hscale
  exact hscale


/-- The directional-density fibre domain survives the same time and space frame. -/
theorem directional_fibre_parabolic (α c : ℝ) {a : ℝ} (ha : 0 < a)
    (b : Space) (s : ℝ) (u h : ℝ → Space → ℂ)
    (hf : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel α c (x-y) * directionalDensity α (u t) (h t) y) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel α c (x-y) * directionalDensity α
        (parabolicField a b s (1/2) u t) (parabolicField a b s (3/2) h t) y) volume := by
  filter_upwards [timeAffine_ae_pullback ha s hf] with t ht
  filter_upwards [affine_ae_pullback ha b ht] with x hx
  have hi := scaled_riesz_fibre_integrable α c ((5+α)/2) ha b x
    (directionalDensity α (u (timeAffine a s t)) (h (timeAffine a s t))) hx
  have he : (fun y => rieszKernel α c (x-y) * directionalDensity α
      (parabolicField a b s (1/2) u t) (parabolicField a b s (3/2) h t) y) =
      (fun y => rieszKernel α c (x-y) * (a^((5+α)/2) *
        directionalDensity α (u (timeAffine a s t)) (h (timeAffine a s t))
          (affine a b y))) := by
    funext y
    rw [directionalDensity_parabolic ha]
  rw [he]
  exact hi

/-- The undifferentiated-density fibre has its own independent domain. -/
theorem density_fibre_parabolic (α c : ℝ) {a : ℝ} (ha : 0 < a)
    (b : Space) (s : ℝ) (u : ℝ → Space → ℂ)
    (hf : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel α c (x-y) * powerDensity α (u t) y) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel α c (x-y) * powerDensity α
        (parabolicField a b s (1/2) u t) y) volume := by
  filter_upwards [timeAffine_ae_pullback ha s hf] with t ht
  filter_upwards [affine_ae_pullback ha b ht] with x hx
  have hi := scaled_riesz_fibre_integrable α c ((3+α)/2) ha b x
    (powerDensity α (u (timeAffine a s t))) hx
  have he : (fun y => rieszKernel α c (x-y) * powerDensity α
      (parabolicField a b s (1/2) u t) y) =
      (fun y => rieszKernel α c (x-y) * (a^((3+α)/2) *
        powerDensity α (u (timeAffine a s t)) (affine a b y))) := by
    funext y
    rw [density_parabolic ha]
  rw [he]
  exact hi

end HartreeF.FreeHeadFrames
