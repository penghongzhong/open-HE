import CriticalSobolevBridge
import FTimeFiniteNormBridge

/-! Time integration of the reviewed critical spatial bridge on F's actual space.
The extended mixed norm is used throughout; neither value L10 membership nor
finiteness of the target time10/space10 norm is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.CriticalTimeSobolev
open MeasureTheory Filter SobolevStretch StationarySelfTest TimeHolder CriticalSobolevBridge
open scoped ENNReal NNReal

/-- The spatial bridge supplies the missing L10 membership for almost every time. -/
theorem ae_critical_dotH1_memLp_ten (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u : T → Space → ℂ) (U V : T → Space → Space)
    (hDot : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t))
    (hU : ∀ᵐ t ∂mu, MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ᵐ t ∂mu, MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    ∀ᵐ t ∂mu, MemLp (u t) 10 volume := by
  filter_upwards [hDot, hU, hV] with t hd hUt hVt
  exact (critical_dotH1_memLp_ten_and_bound hDensity hSob hd hUt hVt).1

/-- Exact time10/space10 estimate from the genuine spatial weak gradients.
All three joint measurability assumptions are used in the finite-slice bridges. -/
theorem critical_mixedNorm_ten_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u : T → Space → ℂ) (U V : T → Space → Space)
    (huJoint : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hUJoint : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hVJoint : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hDot : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t))
    (hU : ∀ᵐ t ∂mu, MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ᵐ t ∂mu, MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    mixedNorm mu volume 10 10 u ≤
      ENNReal.ofReal ((5/3) * K^(1/6 : ℝ)) *
        (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) U +
         mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) V) := by
  have hu10 := ae_critical_dotH1_memLp_ten hDensity hSob mu u U V hDot hU hV
  have hum := spatial_lp_time_measurable mu volume 10 (by norm_num) (by norm_num) u huJoint
  have hUm := spatial_lp_time_measurable mu volume (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) U hUJoint
  have hVm := spatial_lp_time_measurable mu volume (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) V hVJoint
  have hur := hum.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hpoint : ∀ᵐ t ∂mu,
      ‖(eLpNorm (u t) 10 volume).toReal‖ ≤ ((5/3)*K^(1/6 : ℝ)) *
        ‖(eLpNorm (U t) (ENNReal.ofReal (30/13 : ℝ)) volume).toReal +
          (eLpNorm (V t) (ENNReal.ofReal (30/13 : ℝ)) volume).toReal‖ := by
    filter_upwards [hDot, hU, hV] with t hd hUt hVt
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] using
      (critical_dotH1_memLp_ten_and_bound hDensity hSob hd hUt hVt).2
  unfold mixedNorm
  rw [finite_extended_norm_bridge mu 10 _ hum (hu10.mono fun _ h => h.eLpNorm_ne_top),
    finite_extended_norm_bridge mu 10 _ hUm (hU.mono fun _ h => h.eLpNorm_ne_top),
    finite_extended_norm_bridge mu 10 _ hVm (hV.mono fun _ h => h.eLpNorm_ne_top)]
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hur hpoint 10).trans
    (mul_le_mul' le_rfl (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 10)))

/-- Finite critical gradient mixed norms produce the target finite mixed norm,
its real-valued exact estimate, and genuine L10 time membership of the slice norm. -/
theorem critical_mixedNorm_ten_finite_and_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u : T → Space → ℂ) (U V : T → Space → Space)
    (huJoint : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hUJoint : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hVJoint : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hDot : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t))
    (hU : ∀ᵐ t ∂mu, MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ᵐ t ∂mu, MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hUFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) U ≠ ∞)
    (hVFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) V ≠ ∞) :
    (∀ᵐ t ∂mu, MemLp (u t) 10 volume) ∧
    mixedNorm mu volume 10 10 u ≠ ∞ ∧
    MemLp (fun t => eLpNorm (u t) 10 volume) 10 mu ∧
    (mixedNorm mu volume 10 10 u).toReal ≤ ((5/3)*K^(1/6 : ℝ)) *
      ((mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) U).toReal +
       (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) V).toReal) := by
  have hbound := critical_mixedNorm_ten_bound hDensity hSob mu u U V
    huJoint hUJoint hVJoint hDot hU hV
  have hB : ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) *
      (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) U +
       mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) V) ≠ ∞ := by
    finiteness
  have hfinite := ne_top_of_le_ne_top hB hbound
  refine ⟨ae_critical_dotH1_memLp_ten hDensity hSob mu u U V hDot hU hV,
    hfinite, lt_top_iff_ne_top.mpr hfinite, ?_⟩
  have hreal := ENNReal.toReal_mono hB hbound
  have hK := hSob.nonneg
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_add hUFinite hVFinite,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ))] using hreal

end HartreeF.CriticalTimeSobolev
