import FEnergyBanach
import ForcingLpMap
import FTimeFiniteNormBridge
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.LocalScalarSource
open EnergySpace ForcingDomain ForcingContinuity

abbrev SourceSpace := Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space)
instance sourceExponentFact : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩

variable {T : Type*} [TopologicalSpace T]

/-- The literal Hartree nonlinearity along an actual continuous energy path. -/
def forcingPath {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) : C(T, SourceSpace) :=
  ⟨fun t => forcingLp hH (energyValue (u t)),
    (forcingLp_continuous hH).comp (energyValue.continuous.comp u.continuous)⟩

theorem forcingPath_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) (t : T) :
    forcingPath hH u t =ᵐ[volume] forcing alpha c (energyValue (u t)) := by
  exact (forcing_memLp hH (Lp.memLp (energyValue (u t)))).coeFn_toLp

variable [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    [SecondCountableTopology T] (mu : Measure T) [IsFiniteMeasure mu]

/-- Finite time measure and genuine continuous energy path produce the source domain. -/
theorem forcingPath_memLp {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) : MemLp (forcingPath hH u) 2 mu :=
  ContinuousMap.memLp (p := 2) mu ℂ (forcingPath hH u)

/-- Actual iterated Bochner source; no endpoint-norm premise is required. -/
def scalarSource {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) : Lp SourceSpace 2 mu :=
  ContinuousMap.toLp 2 mu ℂ (forcingPath hH u)

theorem scalarSource_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      scalarSource mu hH u t x = forcing alpha c (energyValue (u t)) x := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) mu (𝕜 := ℂ) (forcingPath hH u)]
    with t ht
  change ∀ᵐ x ∂(volume : Measure Space),
    (ContinuousMap.toLp 2 mu ℂ (forcingPath hH u)) t x = _
  rw [ht]
  exact forcingPath_coeFn hH u t

theorem scalarSource_norm_le {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) :
    ‖scalarSource mu hH u‖ ≤
      (measureUnivNNReal mu ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ) * ‖forcingPath hH u‖ := by
  have hmap : ‖(ContinuousMap.toLp (E := SourceSpace) 2 mu ℂ :
      C(T, SourceSpace) →L[ℂ] Lp SourceSpace 2 mu)‖ ≤
      (measureUnivNNReal mu ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ) :=
    ContinuousMap.toLp_norm_le (p := 2) (𝕜 := ℂ) mu
  exact ((ContinuousMap.toLp (E := SourceSpace) 2 mu ℂ).le_opNorm
    (forcingPath hH u)).trans (mul_le_mul_of_nonneg_right hmap (norm_nonneg _))

theorem scalarDifferenceSource_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      (scalarSource mu hH u - scalarSource mu hH v) t x =
        forcing alpha c (energyValue (u t)) x -
          forcing alpha c (energyValue (v t)) x := by
  filter_upwards [Lp.coeFn_sub (scalarSource mu hH u) (scalarSource mu hH v),
    scalarSource_coeFn mu hH u, scalarSource_coeFn mu hH v] with t ht hu hv
  rw [ht]
  filter_upwards [Lp.coeFn_sub (scalarSource mu hH u t) (scalarSource mu hH v t), hu, hv]
    with x hx hux hvx
  change ((scalarSource mu hH u) t - (scalarSource mu hH v) t) x = _
  simpa only [Pi.sub_apply, hux, hvx] using hx

/-- The actual canonical forcing field has exactly the constructed endpoint norm. -/
theorem forcing_mixedNorm_eq {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) :
    TimeHolder.mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (energyValue (u t)) x) = ‖scalarSource mu hH u‖ₑ := by
  calc
    _ = eLpNorm (fun t => ‖scalarSource mu hH u t‖ₑ) 2 mu := by
      apply eLpNorm_congr_ae
      filter_upwards [scalarSource_coeFn mu hH u] with t ht
      exact (eLpNorm_congr_ae ht).symm.trans (Lp.enorm_def _).symm
    _ = eLpNorm (scalarSource mu hH u) 2 mu :=
      eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = _ := (Lp.enorm_def _).symm

theorem forcing_mixedNorm_ne_top {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) :
    TimeHolder.mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (energyValue (u t)) x) ≠ ∞ := by
  rw [forcing_mixedNorm_eq mu hH u]
  exact enorm_ne_top

theorem forcingDifference_mixedNorm_eq {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) :
    TimeHolder.mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (energyValue (u t)) x -
        forcing alpha c (energyValue (v t)) x) =
      ‖scalarSource mu hH u - scalarSource mu hH v‖ₑ := by
  calc
    _ = eLpNorm (fun t => ‖(scalarSource mu hH u - scalarSource mu hH v) t‖ₑ) 2 mu := by
      apply eLpNorm_congr_ae
      filter_upwards [scalarDifferenceSource_coeFn mu hH u v] with t ht
      exact (eLpNorm_congr_ae ht).symm.trans (Lp.enorm_def _).symm
    _ = eLpNorm (scalarSource mu hH u - scalarSource mu hH v) 2 mu :=
      eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = _ := (Lp.enorm_def _).symm

theorem forcingDifference_mixedNorm_ne_top {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) :
    TimeHolder.mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (energyValue (u t)) x -
        forcing alpha c (energyValue (v t)) x) ≠ ∞ := by
  rw [forcingDifference_mixedNorm_eq mu hH u v]
  exact enorm_ne_top

end HartreeF.LocalScalarSource
