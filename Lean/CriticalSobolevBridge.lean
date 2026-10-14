import CriticalHolder
import CriticalSobolevNormAlgebra

/-!
The genuine critical spatial Sobolev bridge on F's Euclidean space.
Only the existing ordinary H1 density and ordinary 2-to-6 Sobolev interfaces
are retained. The target L10 membership is produced by saturated powers,
critical Holder, cancellation, and native Lp Fatou. No global L2 datum or
new 30/13-to-10 Sobolev assumption occurs.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CriticalSobolevBridge
open SobolevStretch StationarySelfTest WeakHartreeChain

/-- The exact uniform estimate for each finite saturation. -/
theorem critical_saturation_uniform_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {ε : ℝ} (hε : 0 < ε)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    (eLpNorm (fun x => saturatedDensity (5/3) ε (u x)) 6 volume).toReal^(3/5 : ℝ) ≤
      ((5/3)*K^(1/6:ℝ))*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal) := by
  have hd := critical_saturation_domains hε hu
  exact CriticalSobolevNormAlgebra.critical_saturation_norm_bound hSob hd.1 hd.2
    (saturatedDensity_hasWeakGradient hDensity (by norm_num : (1:ℝ)<5/3) hε hu)
    (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (critical_saturation_gradient_norm_bound hε hu hU hV)

/-- Recovering the original modulus pointwise from the saturated five-thirds power. -/
theorem critical_saturation_root_tendsto (z : ℂ) :
    Tendsto (fun n => ‖saturatedDensity (5/3) (saturationParameter n) z‖^(3/5:ℝ))
      atTop (𝓝 ‖z‖) := by
  have hh := (saturatedDensity_tendsto (5/3) z).norm.rpow_const
    (Or.inr (by norm_num : (0:ℝ)≤3/5))
  convert hh using 1
  rw [Real.norm_eq_abs,abs_of_nonneg (density_nonneg _ _)]
  unfold WeakHartreeChain.density
  rw [← Real.rpow_mul (norm_nonneg z)]
  norm_num

/-- Native Fatou produces the missing L10 bound; it is not assumed. -/
theorem critical_dotH1_eLpNorm_ten_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    eLpNorm u 10 volume ≤ ENNReal.ofReal (
      ((5/3)*K^(1/6:ℝ))*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal)) := by
  let f : ℕ → Space → ℝ := fun n x => saturatedDensity (5/3) (saturationParameter n) (u x)
  let g : ℕ → Space → ℝ := fun n x => ‖f n x‖^(3/5:ℝ)
  let B : ℝ := ((5/3)*K^(1/6:ℝ))*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal)
  have hK := hSob.nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf (n : ℕ) : MemLp (f n) 6 volume :=
    (critical_saturation_domains (saturationParameter_pos n) hu).1
  have hgm (n : ℕ) : AEStronglyMeasurable (g n) volume :=
    ((hf n).aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have heq (n : ℕ) : eLpNorm (g n) 10 volume = eLpNorm (f n) 6 volume ^ (3/5:ℝ) := by
    change eLpNorm (fun x => ‖f n x‖^(3/5:ℝ)) 10 volume = _
    rw [eLpNorm_norm_rpow (f n) (hf n).aestronglyMeasurable (by norm_num : (0:ℝ)<3/5)]
    rw [show (10:ℝ≥0∞) = ENNReal.ofReal (10:ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]
    norm_num
  have hb (n : ℕ) : eLpNorm (g n) 10 volume ≤ ENNReal.ofReal B := by
    rw [heq]
    have hfinite : eLpNorm (f n) 6 volume ^ (3/5:ℝ) ≠ ∞ := by finiteness [hf n]
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal hB]
    exact critical_saturation_uniform_bound hDensity hSob (saturationParameter_pos n) hu hU hV
  have ht : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 ‖u x‖) :=
    Eventually.of_forall (fun x => critical_saturation_root_tendsto (u x))
  have hfatou := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hb) hgm
    hu.function_L6.aestronglyMeasurable.norm ht
  rw [eLpNorm_norm u hu.function_L6.aestronglyMeasurable] at hfatou
  exact hfatou

/-- The complete critical spatial bridge, with produced L10 membership and exact constant. -/
theorem critical_dotH1_memLp_ten_and_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp u 10 volume ∧
    (eLpNorm u 10 volume).toReal ≤
      ((5/3)*K^(1/6:ℝ))*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal) := by
  have hK := hSob.nonneg
  have hb := critical_dotH1_eLpNorm_ten_bound hDensity hSob hu hU hV
  refine ⟨hb.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

#print axioms critical_saturation_uniform_bound
#print axioms critical_saturation_root_tendsto
#print axioms critical_dotH1_eLpNorm_ten_bound
#print axioms critical_dotH1_memLp_ten_and_bound
end HartreeF.CriticalSobolevBridge
