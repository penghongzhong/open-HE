import FRetardedEnergyState
import FEndpointTimeExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv
open scoped ENNReal SchwartzMap
namespace HartreeF.Retarded
open FreeFlow EnergySpace TimeHolder SobolevStretch StationarySelfTest
open ForcingDomain GradientMajorants WeakHartreeProduct

theorem restrictedL2_extend_scalar {C : ℝ} (h : OrdinaryEndpointBound C)
    (I : Set ℝ) (hI : MeasurableSet I) (F : LocalEndpointSource I)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (φ : FreeFlow.Test) :
    Lp.toTemperedDistribution (restrictedL2 h J hJ t (extendEndpointSource I hI F)) φ =
      ∫ s in I ∩ J, Lp.toTemperedDistribution (F s) (freeTest (t-s) φ) := by
  rw [restrictedL2_scalar]
  have he : scalarIntegrand t (extendEndpointSource I hI F) φ =ᵐ[volume.restrict J]
      I.indicator (fun s => Lp.toTemperedDistribution (F s) (freeTest (t-s) φ)) := by
    filter_upwards [ae_restrict_of_ae (extendEndpointSource_coeFn I hI F)] with s hs
    unfold scalarIntegrand
    rw [hs]
    by_cases hm : s ∈ I
    · simp only [Set.indicator_of_mem hm]
    · simp only [Set.indicator_of_notMem hm]
      exact congrArg (fun T : FreeFlow.TD => T (freeTest (t-s) φ))
        (map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space)
          (ENNReal.ofReal (6/5 : ℝ))))
  rw [integral_congr_ae he, integral_indicator hI, Measure.restrict_restrict hI]

theorem restrictedL2_extend_norm {C : ℝ} (h : OrdinaryEndpointBound C)
    (I : Set ℝ) (hI : MeasurableSet I) (F : LocalEndpointSource I)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) :
    ‖restrictedL2 h J hJ t (extendEndpointSource I hI F)‖ ≤ C * ‖F‖ := by
  simpa only [extendEndpointSource_norm] using restrictedL2_norm h J hJ t (extendEndpointSource I hI F)

/-- Actual C39/C40 source classes on a local time set feed the same construction.
No global source norm is required; extension by zero is performed internally. -/
theorem exists_actual_local_restrictedEnergyState (hDensity : OrdinaryH1Density)
    {K C alpha c : ℝ} (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (hH : OrdinaryHLS alpha c) (I : Set ℝ) (hI : MeasurableSet I)
    (u v : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hSlices : ∀ᵐ s ∂(volume.restrict I : Measure ℝ),
      InDotH1 (u s) (U s) (V s) ∧ InDotH1 (v s) (P s) (Q s) ∧
      MemLp (u s) 10 volume ∧ MemLp (v s) 10 volume ∧
      MemLp (U s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q s) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (F : LocalEndpointSource I)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 (volume.restrict I : Measure ℝ))
    (hF : ∀ᵐ s ∂(volume.restrict I : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      F s x = forcing alpha c (u s) x - forcing alpha c (v s) x)
    (hG : ∀ᵐ s ∂(volume.restrict I : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      G s x = actualFullGradient alpha c (u s) (U s) (V s) x -
        actualFullGradient alpha c (v s) (P s) (Q s) x)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) :
    ∃ w : EnergyState,
      (∀ φ : FreeFlow.Test, energyDistribution w φ =
        ∫ s in I ∩ J, Lp.toTemperedDistribution (F s) (freeTest (t-s) φ)) ∧
      (∀ j : Fin 3, energyGradient j w = restrictedL2 h J hJ t
        (extendEndpointSource I hI (endpointGradientCoordinateSource (volume.restrict I) j G))) := by
  have hd := actual_endpointSource_tempered_derivatives hDensity hSob hH
    (volume.restrict I) u v U V P Q hSlices F G hF hG
  have he := extendEndpointSource_coordinate_derivatives I hI F
    (fun j => endpointGradientCoordinateSource (volume.restrict I) j G) hd
  have hcoord := (ae_all_iff).mp he
  let eF := extendEndpointSource I hI F
  let eG := fun j => extendEndpointSource I hI
    (endpointGradientCoordinateSource (volume.restrict I) j G)
  refine ⟨restrictedEnergyState hDensity hSob h eF eG hcoord J hJ t, ?_, ?_⟩
  · intro φ
    rw [restrictedEnergyState, l2EnergyState_distribution]
    exact restrictedL2_extend_scalar h I hI F J hJ t φ
  · exact fun j => restrictedEnergyState_gradient hDensity hSob h eF eG hcoord J hJ t j

end HartreeF.Retarded
