import FRetardedTransport
import FEndpointCutoffContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Retarded
open FreeFlow

/-- Restricting the scalar time integral is exactly cutoff of the Bochner source. -/
theorem restrictedL2_eq_cutoff {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    restrictedL2 h J hJ t F =
      restrictedL2 h Set.univ MeasurableSet.univ t (endpointCutoff J hJ F) := by
  apply l2_distribution_injective
  ext φ
  rw [restrictedL2_scalar, restrictedL2_scalar, Measure.restrict_univ,
    ← integral_indicator hJ]
  apply integral_congr_ae
  filter_upwards [endpointCutoff_coe J hJ F] with s hs
  unfold scalarIntegrand
  rw [hs]
  by_cases hsj : s ∈ J
  · simp only [Set.indicator_of_mem hsj]
  · simp only [Set.indicator_of_notMem hsj]
    change (0 : ℂ) = ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V)
      (ENNReal.ofReal (6/5 : ℝ))) 0) _
    simp

/-- The constructed integral depends only on the time domain up to Lebesgue AE. -/
theorem restrictedL2_congr_set {C : ℝ} (h : OrdinaryEndpointBound C)
    (J K : Set ℝ) (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (hJK : J =ᵐ[volume] K) (t : ℝ) (F : EndpointSource) :
    restrictedL2 h J hJ t F = restrictedL2 h K hK t F := by
  apply l2_distribution_injective
  ext φ
  rw [restrictedL2_scalar, restrictedL2_scalar]
  exact setIntegral_congr_set hJK

/-- Endpoint inclusion does not change the actual Lebesgue retarded integral. -/
theorem retardedL2_eq_Iic {C : ℝ} (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (t : ℝ) :
    retardedL2 h F t = restrictedL2 h (Set.Iic t) measurableSet_Iic t F :=
  restrictedL2_congr_set h _ _ measurableSet_Iio measurableSet_Iic
    (Iio_ae_eq_Iic) t F

/-- Endpoint inclusion does not change the actual forward integral. -/
theorem forwardL2_eq_Ioo {C : ℝ} (h : OrdinaryEndpointBound C)
    (a : ℝ) (F : EndpointSource) (t : ℝ) :
    forwardL2 h a F t = restrictedL2 h (Set.Ioo a t) measurableSet_Ioo t F :=
  restrictedL2_congr_set h _ _ measurableSet_Ioc measurableSet_Ioo
    (Ioo_ae_eq_Ioc).symm t F

/-- Exact transported source-difference identity, valid in either time order. -/
theorem restrictedL2_source_difference {C : ℝ} (h : OrdinaryEndpointBound C)
    (J K : Set ℝ) (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (s t : ℝ) (F : EndpointSource) :
    restrictedL2 h J hJ t F - freeL2 (t-s) (restrictedL2 h K hK s F) =
      restrictedL2 h Set.univ MeasurableSet.univ t
        (endpointCutoff J hJ F - endpointCutoff K hK F) := by
  rw [restrictedL2_transport, sub_add_cancel, restrictedL2_sub,
    ← restrictedL2_eq_cutoff, ← restrictedL2_eq_cutoff]

/-- The same numerical endpoint estimate controls the exact transported increment. -/
theorem restrictedL2_source_difference_bound {C : ℝ} (h : OrdinaryEndpointBound C)
    (J K : Set ℝ) (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (s t : ℝ) (F : EndpointSource) :
    ‖restrictedL2 h J hJ t F - freeL2 (t-s) (restrictedL2 h K hK s F)‖ ≤
      C * ‖endpointCutoff J hJ F - endpointCutoff K hK F‖ := by
  rw [restrictedL2_source_difference]
  exact restrictedL2_norm h _ _ _ _

/-- Strong continuity follows from actual cutoff-source continuity and the Fourier group. -/
theorem restrictedL2_time_continuous_of_cutoff {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : ℝ → Set ℝ) (hJ : ∀ t, MeasurableSet (J t)) (F : EndpointSource)
    (hc : Continuous (fun t => endpointCutoff (J t) (hJ t) F)) :
    Continuous (fun t => restrictedL2 h (J t) (hJ t) t F) := by
  have he (t : ℝ) : restrictedL2 h (J t) (hJ t) t F =
      freeL2 t (restrictedL2CLM h Set.univ MeasurableSet.univ 0
        (endpointCutoff (J t) (hJ t) F)) := by
    rw [restrictedL2_eq_cutoff, restrictedL2_transport_from_zero]
    rfl
  simp_rw [he]
  have hp : Continuous (fun t : ℝ => (t,
      restrictedL2CLM h Set.univ MeasurableSet.univ 0
        (endpointCutoff (J t) (hJ t) F))) :=
    continuous_id.prodMk ((restrictedL2CLM h Set.univ MeasurableSet.univ 0).continuous.comp hc)
  simpa only [Function.comp_def] using freeL2_joint_continuous.comp hp

/-- Actual global-past retarded source realization is strongly continuous in L2. -/
theorem retardedL2_time_continuous {C : ℝ} (h : OrdinaryEndpointBound C)
    (F : EndpointSource) : Continuous (retardedL2 h F) :=
  restrictedL2_time_continuous_of_cutoff h Set.Iio (fun _ => measurableSet_Iio) F
    (endpointCutoff_Iio_continuous F)

/-- Actual forward realization is continuous on all real times, including its zero past. -/
theorem forwardL2_time_continuous {C : ℝ} (h : OrdinaryEndpointBound C)
    (a : ℝ) (F : EndpointSource) : Continuous (forwardL2 h a F) :=
  restrictedL2_time_continuous_of_cutoff h (Set.Ioc a) (fun _ => measurableSet_Ioc) F
    (endpointCutoff_Ioc_continuous a F)

/-- The forward convention is zero at and before its initial time. -/
theorem forwardL2_eq_zero_of_le {C : ℝ} (h : OrdinaryEndpointBound C)
    (a t : ℝ) (F : EndpointSource) (ht : t ≤ a) : forwardL2 h a F t = 0 := by
  apply l2_distribution_injective
  ext φ
  rw [forwardL2_scalar, Set.Ioc_eq_empty_of_le ht]
  simp

/-- Uniform source Lipschitz bound for the actual retarded trajectory. -/
theorem retardedL2_source_difference_bound {C : ℝ} (h : OrdinaryEndpointBound C)
    (F G : EndpointSource) (t : ℝ) :
    ‖retardedL2 h F t - retardedL2 h G t‖ ≤ C * ‖F-G‖ :=
  restrictedL2_difference_bound h _ measurableSet_Iio t F G

theorem forwardL2_source_difference_bound {C : ℝ} (h : OrdinaryEndpointBound C)
    (a : ℝ) (F G : EndpointSource) (t : ℝ) :
    ‖forwardL2 h a F t - forwardL2 h a G t‖ ≤ C * ‖F-G‖ :=
  restrictedL2_difference_bound h _ measurableSet_Ioc t F G

/-- Continuity at the initial time is into the actual zero vector. -/
theorem forwardL2_tendsto_initial {C : ℝ} (h : OrdinaryEndpointBound C)
    (a : ℝ) (F : EndpointSource) : Tendsto (forwardL2 h a F) (𝓝 a) (𝓝 0) := by
  simpa only [forwardL2_initial] using (forwardL2_time_continuous h a F).tendsto a

end HartreeF.Retarded
