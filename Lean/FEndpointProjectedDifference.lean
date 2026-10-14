import FEndpointSolutionDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open FreeDataDependence
open scoped ENNReal NNReal
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource intervalRetardedCriticalPath freeCriticalPath
  freeEnergyState hartreeDuhamelMap CriticalJointSources.jointFields

/-- Projection of a difference agrees with the literal vector-field difference
AE in space. No pointwise choice of an Lp representative is asserted. -/
theorem energyProjectedGradient_sub_ae (L : ℂ →L[ℝ] ℝ) (f g : EnergyState) :
    energyProjectedGradient L (f-g) =ᵐ[volume]
      (fun x => energyProjectedGradient L f x - energyProjectedGradient L g x) := by
  have hc : ∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      energyGradient j (f-g) x = energyGradient j f x - energyGradient j g x := by
    intro j
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (energyGradient j f) (energyGradient j g)] with x hx
    exact hx
  filter_upwards [ae_all_iff.mpr hc] with x hx
  change (∑ j : Fin 3, L (energyGradient j (f-g) x) • coordinate j) = _
  calc
    _ = ∑ j : Fin 3, L (energyGradient j f x - energyGradient j g x) • coordinate j :=
      Finset.sum_congr rfl fun j _ => congrArg (fun z : ℂ => L z • coordinate j) (hx j)
    _ = _ := by simp only [map_sub, sub_smul, Finset.sum_sub_distrib, energyProjectedGradient]

/-- Quantitative endpoint control transfers to the actual vector gradient,
using the verified joint representative only to justify time measurability. -/
theorem EndpointGradientWitness.projected_actual_bound {a b : ℝ}
    (p : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ p))
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, ‖L w‖ ≤ ‖w‖)
    (F : Set.Icc a b → Space → Space)
    (hF : AEStronglyMeasurable (fun tx : Set.Icc a b × Space => F tx.1 tx.2)
      ((intervalMeasure a b).prod volume))
    (heq : ∀ᵐ t ∂intervalMeasure a b,
      F t =ᵐ[volume] energyProjectedGradient L (energyPath _ p t)) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient L (energyPath _ p t)) ≤
      ∑ j : Fin 3, mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (energyPath _ p t)) := by
  have he : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient L (energyPath _ p t)) =
      mixedNorm (intervalMeasure a b) volume 2 6 F := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with t ht
    exact eLpNorm_congr_ae ht.symm
  rw [he]
  simpa only [W.mixedNorm_eq] using W.projected_joint_bound L hL F hF heq

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

/-- Literal complex-coordinate gradient differences have the same endpoint
bound; subtraction of Lp representatives is used only AE in space. -/
theorem fixedPoint_actual_coordinate_difference_endpoint_bound (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyGradient j (energyPath _ u t) x -
        energyGradient j (energyPath _ v t) x) ≤
      ENNReal.ofReal (Che * ‖energyGradient j u0 - energyGradient j v0‖) +
      ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖) := by
  have he : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyGradient j (energyPath _ u t) x -
        energyGradient j (energyPath _ v t) x) =
      mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (energyPath _ (u-v) t)) := by
    apply eLpNorm_congr_ae
    filter_upwards [] with t
    have hp : energyPath (intervalMeasure a b) (u-v) t =
        energyPath (intervalMeasure a b) u t - energyPath (intervalMeasure a b) v t :=
      congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
        ((energyPath (intervalMeasure a b)).map_sub u v)
    have hg : energyGradient j (energyPath (intervalMeasure a b) (u-v) t) =
        energyGradient j (energyPath (intervalMeasure a b) u t) -
        energyGradient j (energyPath (intervalMeasure a b) v t) :=
      (congrArg (energyGradient j) hp).trans ((energyGradient j).map_sub _ _)
    exact (eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm).trans
      (congrArg (fun f : FreeFlow.L2 => eLpNorm f 6 volume) hg.symm)
  rw [he]
  simpa only [map_sub] using fixedPoint_difference_endpoint_bound hDensity hSob h0
    hfree hret hefree heret hH hab u0 v0 u v hu hv j

/-- The coordinate estimate also holds on Lebesgue measure restricted to the
same closed interval, via the accepted isometric interval transport. -/
theorem fixedPoint_difference_local_endpoint_bound (j : Fin 3) :
    mixedNorm (localMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (u-v) (Set.projIcc a b hab t))) ≤
      ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
      ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖) := by
  rw [(fixedPoint_difference_endpointWitness hDensity hSob h0 hfree hret hefree heret
    hH hab u0 v0 u v hu hv).local_mixedNorm_eq hab j]
  exact fixedPoint_difference_endpoint_bound hDensity hSob h0 hfree hret hefree heret
    hH hab u0 v0 u v hu hv j

/-- The real and imaginary vector gradients in the paper's endpoint term both
have a quantitative bound, with exactly the actual data/source differences. -/
theorem fixedPoint_difference_projected_endpoint_bound :
    let R := ∑ j : Fin 3,
      (ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖))
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.reCLM (energyPath _ (u-v) t)) ≤ R ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.imCLM (energyPath _ (u-v) t)) ≤ R := by
  let W := fixedPoint_difference_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v hu hv
  have hb := fun j => fixedPoint_difference_endpoint_bound hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v hu hv j
  constructor
  · exact (W.projected_actual_bound (u-v) Complex.reCLM Complex.abs_re_le_norm _
      (CriticalJointSources.jointFields _ (u-v)).joint_U.aestronglyMeasurable
      ((CriticalJointSources.jointFields _ (u-v)).slice_eq.mono fun _ ht => ht.2.1)).trans
        (Finset.sum_le_sum fun j _ => hb j)
  · exact (W.projected_actual_bound (u-v) Complex.imCLM Complex.abs_im_le_norm _
      (CriticalJointSources.jointFields _ (u-v)).joint_V.aestronglyMeasurable
      ((CriticalJointSources.jointFields _ (u-v)).slice_eq.mono fun _ ht => ht.2.2)).trans
        (Finset.sum_le_sum fun j _ => hb j)

omit hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v hu hv in
/-- Literal real/imaginary gradient differences have exactly the mixed norms
of the corresponding projected gradient of the literal path difference. -/
theorem actual_projected_difference_mixedNorm_eq {a b : ℝ}
    (u v : CriticalPath (intervalMeasure a b)) (L : ℂ →L[ℝ] ℝ) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyProjectedGradient L (energyPath _ u t) x -
        energyProjectedGradient L (energyPath _ v t) x) =
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient L (energyPath _ (u-v) t)) := by
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  have hp : energyPath (intervalMeasure a b) (u-v) t =
      energyPath (intervalMeasure a b) u t - energyPath (intervalMeasure a b) v t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
      ((energyPath (intervalMeasure a b)).map_sub u v)
  exact (eLpNorm_congr_ae (energyProjectedGradient_sub_ae L _ _).symm).trans
    (congrArg (fun f : EnergyState => eLpNorm (energyProjectedGradient L f) 6 volume) hp.symm)

/-- Direct paper-facing formulation on the literal two solution gradients. -/
theorem fixedPoint_actual_projected_difference_endpoint_bound :
    let R := ∑ j : Fin 3,
      (ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖))
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyProjectedGradient Complex.reCLM (energyPath _ u t) x -
        energyProjectedGradient Complex.reCLM (energyPath _ v t) x) ≤ R ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyProjectedGradient Complex.imCLM (energyPath _ u t) x -
        energyProjectedGradient Complex.imCLM (energyPath _ v t) x) ≤ R := by
  simp only [actual_projected_difference_mixedNorm_eq]
  exact fixedPoint_difference_projected_endpoint_bound hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v hu hv

/-- Native source-cap consumer. Each real/imaginary vector endpoint norm is
bounded by three times the coordinate cap; B remains an input source bound. -/
theorem fixedPoint_actual_projected_difference_endpoint_bound_of_source_bound {B : ℝ}
    (hB : ∀ j : Fin 3,
      ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B) :
    let R := 3 * (ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B))
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyProjectedGradient Complex.reCLM (energyPath _ u t) x -
        energyProjectedGradient Complex.reCLM (energyPath _ v t) x) ≤ R ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyProjectedGradient Complex.imCLM (energyPath _ u t) x -
        energyProjectedGradient Complex.imCLM (energyPath _ v t) x) ≤ R := by
  have hb := fixedPoint_actual_projected_difference_endpoint_bound hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v hu hv
  have hsum : (∑ j : Fin 3,
      (ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖))) ≤
      3 * (ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B)) := by
    calc
      _ ≤ ∑ _j : Fin 3,
          (ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B)) :=
        Finset.sum_le_sum fun j _ => add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (energyState_gradient_norm_le (u0-v0) j) hefree.1))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB j) heret.1))
      _ = _ := by simp [mul_add]
  exact ⟨hb.1.trans hsum, hb.2.trans hsum⟩

end HartreeF.EndpointOutput
