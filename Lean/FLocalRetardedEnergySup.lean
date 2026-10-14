import FRetardedEnergySup
import FEndpointTimeExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.Retarded
open FreeFlow EnergySpace SobolevStretch StationarySelfTest

theorem extendEndpointSource_sub (I : Set ℝ) (hI : MeasurableSet I)
    (F G : LocalEndpointSource I) :
    extendEndpointSource I hI (F - G) =
      extendEndpointSource I hI F - extendEndpointSource I hI G := by
  apply Lp.ext
  filter_upwards [extendEndpointSource_coeFn I hI (F-G),
    extendEndpointSource_coeFn I hI F, extendEndpointSource_coeFn I hI G,
    Lp.coeFn_sub (extendEndpointSource I hI F) (extendEndpointSource I hI G),
    (ae_restrict_iff' hI).mp (Lp.coeFn_sub F G)] with s hFG hF hG hsub hs
  rw [hFG, hsub, Pi.sub_apply, hF, hG]
  by_cases hm : s ∈ I
  · simpa only [Set.indicator_of_mem hm, Pi.sub_apply] using hs hm
  · simp only [Set.indicator_of_notMem hm, sub_self]

theorem extendEndpointSource_family_norm (I : Set ℝ) (hI : MeasurableSet I)
    (G : Fin 3 → LocalEndpointSource I) :
    ‖fun j => extendEndpointSource I hI (G j)‖ = ‖G‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg G)).mpr
    intro j
    rw [extendEndpointSource_norm]
    exact norm_le_pi_norm G j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => extendEndpointSource I hI (G j)))).mpr
    intro j
    rw [← extendEndpointSource_norm I hI (G j)]
    exact norm_le_pi_norm (fun j => extendEndpointSource I hI (G j)) j

theorem extendEndpointSource_family_sub_norm (I : Set ℝ) (hI : MeasurableSet I)
    (G H : Fin 3 → LocalEndpointSource I) :
    ‖(fun j => extendEndpointSource I hI (G j)) -
      (fun j => extendEndpointSource I hI (H j))‖ = ‖G-H‖ := by
  have heq : (fun j => extendEndpointSource I hI (G j)) -
      (fun j => extendEndpointSource I hI (H j)) =
      (fun j => extendEndpointSource I hI ((G-H) j)) := by
    funext j
    exact (extendEndpointSource_sub I hI (G j) (H j)).symm
  rw [heq, extendEndpointSource_family_norm]

variable {T : Type*} [TopologicalSpace T]
    (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (I : Set ℝ) (hI : MeasurableSet I)
    (F : LocalEndpointSource I) (G : Fin 3 → LocalEndpointSource I)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume.restrict I,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))

/-- Local source classes are extended isometrically; compatibility is produced internally. -/
def localRetardedEnergyCurve (τ : C(T, ℝ)) : C(T, EnergyState) :=
  retardedEnergyCurve hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j)) τ

def localForwardEnergyCurve (a : ℝ) (τ : C(T, ℝ)) : C(T, EnergyState) :=
  forwardEnergyCurve hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j)) a τ

variable [CompactSpace T]

theorem localRetardedEnergyCurve_norm (τ : C(T, ℝ)) :
    ‖localRetardedEnergyCurve hDensity hSob h I hI F G hFG τ‖ ≤
      energyEndpointConstant K C * ‖G‖ := by
  have hb := retardedEnergyCurve_norm hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j)) τ
  rwa [extendEndpointSource_family_norm] at hb

theorem localForwardEnergyCurve_norm (a : ℝ) (τ : C(T, ℝ)) :
    ‖localForwardEnergyCurve hDensity hSob h I hI F G hFG a τ‖ ≤
      energyEndpointConstant K C * ‖G‖ := by
  have hb := forwardEnergyCurve_norm hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j)) a τ
  rwa [extendEndpointSource_family_norm] at hb

variable (F' : LocalEndpointSource I) (G' : Fin 3 → LocalEndpointSource I)
    (hFG' : ∀ j : Fin 3, ∀ᵐ s ∂volume.restrict I,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F' s)) = Lp.toTemperedDistribution (G' j s))

theorem localRetardedEnergyCurve_sub_norm (τ : C(T, ℝ)) :
    ‖localRetardedEnergyCurve hDensity hSob h I hI F G hFG τ -
      localRetardedEnergyCurve hDensity hSob h I hI F' G' hFG' τ‖ ≤
      energyEndpointConstant K C * ‖G-G'‖ := by
  have hb := retardedEnergyCurve_sub_norm hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j))
    (extendEndpointSource I hI F') (fun j => extendEndpointSource I hI (G' j))
    (fun j => extendEndpointSource_derivative I hI F' (G' j) (coordinate j) (hFG' j)) τ
  rwa [extendEndpointSource_family_sub_norm] at hb

theorem localForwardEnergyCurve_sub_norm (a : ℝ) (τ : C(T, ℝ)) :
    ‖localForwardEnergyCurve hDensity hSob h I hI F G hFG a τ -
      localForwardEnergyCurve hDensity hSob h I hI F' G' hFG' a τ‖ ≤
      energyEndpointConstant K C * ‖G-G'‖ := by
  have hb := forwardEnergyCurve_sub_norm hDensity hSob h (extendEndpointSource I hI F)
    (fun j => extendEndpointSource I hI (G j))
    (fun j => extendEndpointSource_derivative I hI F (G j) (coordinate j) (hFG j))
    (extendEndpointSource I hI F') (fun j => extendEndpointSource I hI (G' j))
    (fun j => extendEndpointSource_derivative I hI F' (G' j) (coordinate j) (hFG' j)) a τ
  rwa [extendEndpointSource_family_sub_norm] at hb

end HartreeF.Retarded
