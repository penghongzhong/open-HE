import FEndpointProjectedDifference
import FEnergyGradientNorm

/-! Native finite-dimensional assembly of the paper's actual complex Euclidean
gradient. This extension does not modify the sealed endpoint difference node. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open FreeDataDependence
open scoped ENNReal NNReal
attribute [local irreducible] energyPath CriticalJointSources.jointFields
  criticalPathIntervalSource hartreeDuhamelMap

/-- The actual complex Euclidean weak gradient already used by the paper's
kinetic energy, assembled from the actual real and imaginary weak gradients. -/
def energyComplexGradient (u : EnergyState) : Space → EuclideanSpace ℂ (Fin 3) :=
  complexGradient (energyProjectedGradient Complex.reCLM u)
    (energyProjectedGradient Complex.imCLM u)

theorem energyComplexGradient_coordinate (u : EnergyState) (x : Space) (j : Fin 3) :
    energyComplexGradient u x j = energyGradient j u x :=
  state_complexGradient_coordinate u x j

/-- Exact finite-dimensional synthesis, before any norm comparison. -/
theorem energyComplexGradient_eq_sum (u : EnergyState) :
    energyComplexGradient u = fun x => ∑ j : Fin 3,
      energyGradient j u x • (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3)) := by
  funext x
  ext i
  fin_cases i <;> simp [energyComplexGradient_coordinate, Fin.sum_univ_three]

/-- The genuine Euclidean spatial norm is controlled natively by the three
actual complex-coordinate spatial norms. No norm equivalence is assumed. -/
theorem energyComplexGradient_spatial_le_sum (u : EnergyState) :
    eLpNorm (energyComplexGradient u) 6 volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j u) 6 volume := by
  rw [energyComplexGradient_eq_sum]
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => energyGradient j u x •
        (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) 6 volume := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := (volume : Measure Space))
          (f := fun j : Fin 3 => fun x => energyGradient j u x •
            (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3)))
          (by norm_num : (1 : ℝ≥0∞) ≤ 6))
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      apply eLpNorm_mono ((Lp.aestronglyMeasurable _).smul_const _)
      intro x
      simp [norm_smul]

private def complexAssembly (z : Space × Space) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (z.1 j : ℂ) + Complex.I * (z.2 j : ℂ))

private theorem complexAssembly_continuous : Continuous complexAssembly := by
  unfold complexAssembly
  fun_prop

/-- The time-space Euclidean assembly bound holds for every actual graph path.
Its time measurability is produced from the existing actual joint fields. -/
theorem criticalPath_complex_endpoint_le_sum {a b : ℝ}
    (p : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ p t)) ≤
      ∑ j : Fin 3, mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (energyPath _ p t)) := by
  let J := CriticalJointSources.jointFields (intervalMeasure a b) p
  let F : Set.Icc a b → Space → EuclideanSpace ℂ (Fin 3) :=
    fun t => complexGradient (J.U t) (J.V t)
  have hF : AEStronglyMeasurable (fun z : Set.Icc a b × Space => F z.1 z.2)
      ((intervalMeasure a b).prod volume) :=
    (complexAssembly_continuous.comp_stronglyMeasurable
      (J.joint_U.prodMk J.joint_V)).aestronglyMeasurable
  have heq : ∀ᵐ t ∂intervalMeasure a b,
      F t =ᵐ[volume] energyComplexGradient (energyPath _ p t) := by
    filter_upwards [J.slice_eq] with t ht
    filter_upwards [ht.2.1, ht.2.2] with x hR hI
    exact congrArg₂ (fun R I : Space => complexAssembly (R, I)) hR hI
  have hm := spatial_lp_time_measurable (intervalMeasure a b) volume 6
    (by norm_num) (by norm_num) F hF
  have hs : ∀ᵐ t ∂intervalMeasure a b, eLpNorm (F t) 6 volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j (energyPath _ p t)) 6 volume := by
    filter_upwards [heq] with t ht
    exact (eLpNorm_congr_ae ht).le.trans (energyComplexGradient_spatial_le_sum _)
  have he : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ p t)) =
      mixedNorm (intervalMeasure a b) volume 2 6 F := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with t ht
    exact eLpNorm_congr_ae ht.symm
  apply he.le.trans
  unfold mixedNorm
  calc
    _ ≤ eLpNorm (fun t => ∑ j : Fin 3,
        eLpNorm (energyGradient j (energyPath _ p t)) 6 volume) 2 (intervalMeasure a b) :=
      eLpNorm_mono_enorm_ae hm (by simpa only [enorm_eq_self] using hs)
    _ ≤ _ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := intervalMeasure a b)
          (f := fun j : Fin 3 => fun t =>
            eLpNorm (energyGradient j (energyPath _ p t)) 6 volume)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The actual complex vector gradient commutes with subtraction AE in space. -/
theorem energyComplexGradient_sub_ae (f g : EnergyState) :
    energyComplexGradient (f-g) =ᵐ[volume]
      (fun x => energyComplexGradient f x - energyComplexGradient g x) := by
  have hc : ∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      energyGradient j (f-g) x = energyGradient j f x - energyGradient j g x := by
    intro j
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (energyGradient j f) (energyGradient j g)] with x hx
    exact hx
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext j
  simpa only [energyComplexGradient_coordinate, PiLp.sub_apply] using hx j

/-- Literal complex Euclidean gradient differences have exactly the endpoint
mixed norm of the gradient of the literal path difference. -/
theorem actual_complex_difference_mixedNorm_eq {a b : ℝ}
    (u v : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ v t) x) =
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ (u-v) t)) := by
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  have hp : energyPath (intervalMeasure a b) (u-v) t =
      energyPath (intervalMeasure a b) u t - energyPath (intervalMeasure a b) v t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
      ((energyPath (intervalMeasure a b)).map_sub u v)
  exact (eLpNorm_congr_ae (energyComplexGradient_sub_ae _ _).symm).trans
    (congrArg (fun f : EnergyState => eLpNorm (energyComplexGradient f) 6 volume) hp.symm)

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 v0 : EnergyState)
  (u v : CriticalPath (intervalMeasure a b))
  (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
  (hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v = v)
include hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v hu hv

/-- The paper's genuine complex Euclidean gradient difference has the endpoint
bound with the exact actual initial-gradient and compatible source differences. -/
theorem fixedPoint_actual_complex_difference_endpoint_bound :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ v t) x) ≤
      ∑ j : Fin 3, (ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖)) := by
  rw [actual_complex_difference_mixedNorm_eq]
  exact (criticalPath_complex_endpoint_le_sum (u-v)).trans
    (Finset.sum_le_sum fun j _ => fixedPoint_difference_endpoint_bound hDensity hSob h0
      hfree hret hefree heret hH hab u0 v0 u v hu hv j)

/-- B remains an input bound on the actual source, for the native family
consumer to discharge. This theorem does not assume an endpoint output bound. -/
theorem fixedPoint_actual_complex_difference_endpoint_bound_of_source_bound {B : ℝ}
    (hB : ∀ j : Fin 3,
      ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ v t) x) ≤
      3 * (ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B)) := by
  rw [actual_complex_difference_mixedNorm_eq]
  apply (criticalPath_complex_endpoint_le_sum (u-v)).trans
  calc
    _ ≤ ∑ _j : Fin 3,
        (ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B)) :=
      Finset.sum_le_sum fun j _ => fixedPoint_difference_endpoint_bound_of_source_bound
        hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v hu hv hB j
    _ = _ := by simp [mul_add]

end HartreeF.EndpointOutput
