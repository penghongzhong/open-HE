import FRetardedEnergyContinuity
import FLocalRetardedEnergyState

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Retarded
open FreeFlow EnergySpace TimeHolder SobolevStretch StationarySelfTest
open ForcingDomain GradientMajorants WeakHartreeProduct

/-- Actual C39/C40 Hartree representatives produce a strongly continuous trajectory.
The C41 derivative compatibility and target continuity are proved internally. -/
theorem exists_actual_retardedEnergyTrajectory (hDensity : OrdinaryH1Density)
    {K C alpha c : ℝ} (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (hH : OrdinaryHLS alpha c)
    (u v : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hSlices : ∀ᵐ s ∂(volume : Measure ℝ),
      InDotH1 (u s) (U s) (V s) ∧ InDotH1 (v s) (P s) (Q s) ∧
      MemLp (u s) 10 volume ∧ MemLp (v s) 10 volume ∧
      MemLp (U s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q s) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (F : EndpointSource)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 (volume : Measure ℝ))
    (hF : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      F s x = forcing alpha c (u s) x - forcing alpha c (v s) x)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      G s x = actualFullGradient alpha c (u s) (U s) (V s) x -
        actualFullGradient alpha c (v s) (P s) (Q s) x) :
    ∃ w : ℝ → EnergyState, Continuous w ∧
      (∀ (t : ℝ) (φ : FreeFlow.Test), energyDistribution (w t) φ =
        ∫ s in Set.Iio t, scalarIntegrand t F φ s) ∧
      (∀ (t : ℝ) (j : Fin 3), energyGradient j (w t) =
        retardedL2 h (endpointGradientCoordinateSource volume j G) t) ∧
      (∀ t : ℝ, (energyValue (w t) : Space → ℂ) =ᵐ[volume] retardedL2 h F t) := by
  have hd := actual_endpointSource_tempered_derivatives hDensity hSob hH
    volume u v U V P Q hSlices F G hF hG
  have hcoord (j : Fin 3) : ∀ᵐ s ∂(volume : Measure ℝ),
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) =
        Lp.toTemperedDistribution (endpointGradientCoordinateSource volume j G s) := by
    filter_upwards [hd] with s hs
    exact hs j
  refine ⟨retardedEnergyState hDensity hSob h F
    (fun j => endpointGradientCoordinateSource volume j G) hcoord, ?_, ?_, ?_, ?_⟩
  · exact retardedEnergyState_time_continuous hDensity hSob h F _ hcoord
  · exact fun t φ => retardedEnergyState_scalar hDensity hSob h F _ hcoord t φ
  · exact fun t j => retardedEnergyState_gradient hDensity hSob h F _ hcoord t j
  · intro t
    exact l2EnergyState_value_ae hDensity hSob (retardedL2 h F t)
      (fun j => retardedL2 h (endpointGradientCoordinateSource volume j G) t)
      (fun j => retardedL2_derivative h F (endpointGradientCoordinateSource volume j G)
        (coordinate j) (hcoord j) t)

/-- A local actual source needs only its local endpoint norm. Extension by zero and
C41 compatibility produce the continuous forward trajectory and zero initial value. -/
theorem exists_actual_local_forwardEnergyTrajectory (hDensity : OrdinaryH1Density)
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
    (a : ℝ) :
    ∃ w : ℝ → EnergyState, Continuous w ∧ w a = 0 ∧
      (∀ t : ℝ, t ≤ a → w t = 0) ∧
      (∀ (t : ℝ) (φ : FreeFlow.Test), energyDistribution (w t) φ =
        ∫ s in I ∩ Set.Ioc a t, Lp.toTemperedDistribution (F s) (freeTest (t-s) φ)) ∧
      (∀ (t : ℝ) (j : Fin 3), energyGradient j (w t) = forwardL2 h a
        (extendEndpointSource I hI (endpointGradientCoordinateSource (volume.restrict I) j G)) t) := by
  have hd := actual_endpointSource_tempered_derivatives hDensity hSob hH
    (volume.restrict I) u v U V P Q hSlices F G hF hG
  have he := extendEndpointSource_coordinate_derivatives I hI F
    (fun j => endpointGradientCoordinateSource (volume.restrict I) j G) hd
  have hcoord := (ae_all_iff).mp he
  let eF := extendEndpointSource I hI F
  let eG := fun j => extendEndpointSource I hI
    (endpointGradientCoordinateSource (volume.restrict I) j G)
  refine ⟨forwardEnergyState hDensity hSob h a eF eG hcoord, ?_, ?_, ?_, ?_, ?_⟩
  · exact forwardEnergyState_time_continuous hDensity hSob h eF eG hcoord a
  · exact forwardEnergyState_initial hDensity hSob h eF eG hcoord a
  · exact fun t ht => forwardEnergyState_eq_zero_of_le hDensity hSob h eF eG hcoord a t ht
  · intro t φ
    rw [forwardEnergyState, restrictedEnergyState, l2EnergyState_distribution]
    exact restrictedL2_extend_scalar h I hI F _ measurableSet_Ioc t φ
  · exact fun t j => forwardEnergyState_gradient hDensity hSob h eF eG hcoord a t j

end HartreeF.Retarded
