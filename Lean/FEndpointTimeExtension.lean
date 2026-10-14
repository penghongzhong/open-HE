import FRetardedScalarL2
import FEnergyBanach
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Isometric extension by zero of local Bochner endpoint sources. Spatial
distributional derivatives commute with this extension in the time variable. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.Retarded
open FreeFlow

/-- Extension by zero of a Bochner L2 class on a measurable time set. -/
def extendTimeLp {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : MeasurableSet I)
    (F : Lp E 2 (volume.restrict I)) : Lp E 2 (volume : Measure ℝ) :=
  ((memLp_indicator_iff_restrict hI.nullMeasurableSet).2 (Lp.memLp F)).toLp
    (I.indicator F)

theorem extendTimeLp_coeFn {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : MeasurableSet I) (F : Lp E 2 (volume.restrict I)) :
    (extendTimeLp I hI F : ℝ → E) =ᵐ[volume] I.indicator F :=
  ((memLp_indicator_iff_restrict hI.nullMeasurableSet).2 (Lp.memLp F)).coeFn_toLp

theorem extendTimeLp_restrict_coeFn {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : MeasurableSet I) (F : Lp E 2 (volume.restrict I)) :
    (extendTimeLp I hI F : ℝ → E) =ᵐ[volume.restrict I] F := by
  filter_upwards [ae_restrict_of_ae (extendTimeLp_coeFn I hI F), ae_restrict_mem hI]
    with t ht hm
  simpa only [Set.indicator_of_mem hm] using ht

theorem extendTimeLp_zero_compl {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : MeasurableSet I) (F : Lp E 2 (volume.restrict I)) :
    (extendTimeLp I hI F : ℝ → E) =ᵐ[volume.restrict Iᶜ] 0 := by
  filter_upwards [ae_restrict_of_ae (extendTimeLp_coeFn I hI F), ae_restrict_mem hI.compl]
    with t ht hm
  simpa only [Set.mem_compl_iff, Set.indicator_of_notMem hm, Pi.zero_apply] using ht

theorem extendTimeLp_norm {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (hI : MeasurableSet I) (F : Lp E 2 (volume.restrict I)) :
    ‖extendTimeLp I hI F‖ = ‖F‖ := by
  rw [extendTimeLp, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hI.nullMeasurableSet,
    Lp.norm_def]

abbrev LocalEndpointSource (I : Set ℝ) := Lp SourceSpace 2 (volume.restrict I)

def extendEndpointSource (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) : EndpointSource := extendTimeLp I hI F

theorem extendEndpointSource_coeFn (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) :
    (extendEndpointSource I hI F : ℝ → SourceSpace) =ᵐ[volume] I.indicator F :=
  extendTimeLp_coeFn I hI F

theorem extendEndpointSource_restrict_coeFn (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) :
    (extendEndpointSource I hI F : ℝ → SourceSpace) =ᵐ[volume.restrict I] F :=
  extendTimeLp_restrict_coeFn I hI F

theorem extendEndpointSource_zero_compl (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) :
    (extendEndpointSource I hI F : ℝ → SourceSpace) =ᵐ[volume.restrict Iᶜ] 0 :=
  extendTimeLp_zero_compl I hI F

theorem extendEndpointSource_norm (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) : ‖extendEndpointSource I hI F‖ = ‖F‖ :=
  extendTimeLp_norm I hI F

/-- Time extension preserves a spatial derivative identity of the actual
local source classes. There is no hypothesis concerning an output state. -/
theorem extendEndpointSource_derivative (I : Set ℝ) (hI : MeasurableSet I)
    (F G : LocalEndpointSource I) (v : V)
    (hFG : ∀ᵐ s ∂volume.restrict I,
      ∂_{v} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G s)) :
    ∀ᵐ s ∂volume,
      ∂_{v} (Lp.toTemperedDistribution (extendEndpointSource I hI F s)) =
        Lp.toTemperedDistribution (extendEndpointSource I hI G s) := by
  have hlocal := (ae_restrict_iff' hI).mp hFG
  filter_upwards [extendEndpointSource_coeFn I hI F,
    extendEndpointSource_coeFn I hI G, hlocal] with s hF hG hs
  rw [hF, hG]
  by_cases hm : s ∈ I
  · simpa only [Set.indicator_of_mem hm] using hs hm
  · simp only [Set.indicator_of_notMem hm]
    have hz : Lp.toTemperedDistribution (0 : SourceSpace) = (0 : TD) :=
      map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure V)
        (ENNReal.ofReal (6/5 : ℝ)))
    rw [hz]
    exact map_zero (lineDerivOpCLM ℂ TD v)

theorem extendEndpointSource_coordinate_derivatives (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) (G : Fin 3 → LocalEndpointSource I)
    (hFG : ∀ᵐ s ∂volume.restrict I, ∀ j : Fin 3,
      ∂_{EnergySpace.coordinate j} (Lp.toTemperedDistribution (F s)) =
        Lp.toTemperedDistribution (G j s)) :
    ∀ᵐ s ∂volume, ∀ j : Fin 3,
      ∂_{EnergySpace.coordinate j} (Lp.toTemperedDistribution (extendEndpointSource I hI F s)) =
        Lp.toTemperedDistribution (extendEndpointSource I hI (G j) s) := by
  apply (ae_all_iff).mpr
  intro j
  exact extendEndpointSource_derivative I hI F (G j) (EnergySpace.coordinate j)
    (hFG.mono (fun _ hs => hs j))

end HartreeF.Retarded
