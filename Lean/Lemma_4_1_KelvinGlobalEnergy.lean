import Lemma_4_1_KelvinSobolev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! The exact energy estimates for the actual weak derivative of the global
Kelvin extension. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

theorem circle_measure_zero (c : ℝ) :
    volume {p : Plane | s p.1 p.2 = c} = 0 := by
  have hm : MeasurableSet {p : Plane | s p.1 p.2 = c} := by
    exact isClosed_eq (by unfold s; fun_prop) continuous_const |>.measurableSet
  apply Measure.measure_prod_null_of_ae_null hm
  filter_upwards [] with x
  apply Set.Finite.measure_zero
  apply (Set.toFinite ({Real.sqrt (c-x^2),-Real.sqrt (c-x^2)} : Set ℝ)).subset
  intro y hy
  change x^2+y^2=c at hy
  have hnon : 0 ≤ c-x^2 := by nlinarith [sq_nonneg y]
  have hs := Real.sq_sqrt hnon
  have he : y^2 = (Real.sqrt (c-x^2))^2 := by nlinarith
  simpa only [mem_insert_iff,mem_singleton_iff] using (sq_eq_sq_iff_eq_or_eq_neg.mp he)

theorem ae_plane_regular (R : ℝ) :
    ∀ᵐ p : Plane, 0 < s p.1 p.2 ∧ s p.1 p.2 ≠ R^2 := by
  have h0 : ∀ᵐ p : Plane, s p.1 p.2 ≠ 0 := by
    simpa only [ae_iff,not_not] using circle_measure_zero 0
  have hR : ∀ᵐ p : Plane, s p.1 p.2 ≠ R^2 := by
    simpa only [ae_iff,not_not] using circle_measure_zero (R^2)
  filter_upwards [h0,hR] with p hp hpR
  refine ⟨?_,hpR⟩
  have hn : 0 ≤ s p.1 p.2 := by unfold s; positivity
  exact lt_of_le_of_ne hn hp.symm

theorem plane_integral_split (R : ℝ) {F : Plane → ℝ} (hF : Integrable F) :
    (∫ p, F p) = (∫ p in innerDisk R, F p) + ∫ p in exteriorDisk R, F p := by
  rw [← integral_add_compl (innerDisk_measurable R) hF]
  congr 1
  apply setIntegral_congr_set
  filter_upwards [ae_plane_regular R] with p hp
  simp only [mem_compl_iff,innerDisk,mem_ofPred_eq,exteriorDisk]
  apply propext
  exact ⟨fun h => lt_of_le_of_ne (not_lt.mp (fun hlt => h ⟨hp.1,hlt⟩)) hp.2.symm,
    fun h ⟨_,hlt⟩ => (not_lt_of_ge h.le) hlt⟩

def longitudinalDensity (D : Space → Space →L[ℝ] ℝ) (z : Space) : ℝ :=
  (D z (1,0))^2

def transverseGradient (D : Space → Space →L[ℝ] ℝ) (z : Space) : Plane :=
  (D z (0,(1,0)),D z (0,(0,1)))

def transverseDensity (D : Space → Space →L[ℝ] ℝ) (z : Space) : ℝ :=
  s (transverseGradient D z).1 (transverseGradient D z).2

theorem derivative_eval_memLp {D : Space → Space →L[ℝ] ℝ}
    (hD : MemLp D 2 volume) (e : Space) : MemLp (fun z => D z e) 2 volume := by
  exact (ContinuousLinearMap.apply ℝ ℝ e).comp_memLp' hD

theorem longitudinalDensity_integrable {D : Space → Space →L[ℝ] ℝ}
    (hD : MemLp D 2 volume) : Integrable (longitudinalDensity D) :=
  (derivative_eval_memLp hD (1,0)).integrable_sq

theorem transverseDensity_integrable {D : Space → Space →L[ℝ] ℝ}
    (hD : MemLp D 2 volume) : Integrable (transverseDensity D) :=
  (derivative_eval_memLp hD (0,(1,0))).integrable_sq.add
    (derivative_eval_memLp hD (0,(0,1))).integrable_sq

theorem compact_derivative_memLp {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : MemLp (fderiv ℝ f) 2 volume := by
  exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))


theorem inner_transverseGradient {R : ℝ} {f : Space → ℝ} {z : Space}
    (hf : DifferentiableAt ℝ f (z.1,inversion R z.2)) (hz : radiusSq z ≠ 0) :
    transverseGradient (fderiv ℝ (innerExtension R f)) z =
      jacobian R z.2 (transverseGradient (fderiv ℝ f) (z.1,inversion R z.2)) := by
  unfold transverseGradient
  rw [jacobian_apply]
  apply Prod.ext
  · dsimp only
    rw [innerExtension_transverse (z := z) hf hz (1,0),jacobian_apply]
    simp only [mul_one,mul_zero,add_zero]
    exact linear_apply_plane
      ((fderiv ℝ f (z.1,inversion R z.2)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) _
  · dsimp only
    rw [innerExtension_transverse (z := z) hf hz (0,1),jacobian_apply]
    simp only [mul_one,mul_zero,zero_add]
    exact linear_apply_plane
      ((fderiv ℝ f (z.1,inversion R z.2)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) _

theorem extensionDerivative_inner {R : ℝ} (f : Space → ℝ) {z : Space}
    (hz : radiusSq z < R^2) :
    extensionDerivative R f z = fderiv ℝ (innerExtension R f) z := by
  simp [extensionDerivative,hz]

theorem extensionDerivative_exterior {R : ℝ} (f : Space → ℝ) {z : Space}
    (hz : R^2 ≤ radiusSq z) : extensionDerivative R f z = fderiv ℝ f z := by
  simp [extensionDerivative,not_lt.mpr hz]

theorem transverse_inner_integral {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    (∫ p in innerDisk R, transverseDensity (extensionDerivative R f) (t,p)) =
      ∫ p in exteriorDisk R, transverseDensity (fderiv ℝ f) (t,p) := by
  unfold transverseDensity
  rw [← kelvin_transverse_energy hR (fun p => transverseGradient (fderiv ℝ f) (t,p))]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  have he : transverseGradient (extensionDerivative R f) (t,p) =
      transverseGradient (fderiv ℝ (innerExtension R f)) (t,p) := by
    unfold transverseGradient
    rw [extensionDerivative_inner f hp.2]
  dsimp only
  rw [he,inner_transverseGradient (z := (t,p)) (hf.differentiable (by norm_num) _) hp.1.ne']

theorem transverse_slice_energy {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ)
    (hint : Integrable (fun p => transverseDensity (extensionDerivative R f) (t,p))) :
    (∫ p, transverseDensity (extensionDerivative R f) (t,p)) =
      2 * ∫ p in exteriorDisk R, transverseDensity (fderiv ℝ f) (t,p) := by
  rw [plane_integral_split R hint,transverse_inner_integral hR hf t]
  have he : (∫ p in exteriorDisk R, transverseDensity (extensionDerivative R f) (t,p)) =
      ∫ p in exteriorDisk R, transverseDensity (fderiv ℝ f) (t,p) := by
    apply setIntegral_congr_fun (exteriorDisk_measurable R)
    intro p hp
    dsimp only
    unfold transverseDensity transverseGradient
    rw [extensionDerivative_exterior f hp.le]
  rw [he]; ring

theorem longitudinal_inner_integral {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    (∫ p in innerDisk R, longitudinalDensity (extensionDerivative R f) (t,p)) =
      ∫ p in exteriorDisk R, kelvinWeight R p * longitudinalDensity (fderiv ℝ f) (t,p) := by
  rw [← kelvin_longitudinal_integral hR
    (fun p => longitudinalDensity (fderiv ℝ f) (t,p))]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  dsimp only
  unfold longitudinalDensity
  rw [extensionDerivative_inner f hp.2,
    innerExtension_longitudinal (z := (t,p)) (hf.differentiable (by norm_num) _) hp.1.ne']

theorem longitudinal_slice_bound {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ)
    (hint : Integrable (fun p => longitudinalDensity (extensionDerivative R f) (t,p)))
    (hforig : Integrable (fun p => longitudinalDensity (fderiv ℝ f) (t,p))) :
    (∫ p, longitudinalDensity (extensionDerivative R f) (t,p)) ≤
      2 * ∫ p in exteriorDisk R, longitudinalDensity (fderiv ℝ f) (t,p) := by
  rw [plane_integral_split R hint,longitudinal_inner_integral hR hf t]
  have he : (∫ p in exteriorDisk R, longitudinalDensity (extensionDerivative R f) (t,p)) =
      ∫ p in exteriorDisk R, longitudinalDensity (fderiv ℝ f) (t,p) := by
    apply setIntegral_congr_fun (exteriorDisk_measurable R)
    intro p hp
    dsimp only
    unfold longitudinalDensity
    rw [extensionDerivative_exterior f hp.le]
  rw [he]
  have hl := kelvin_longitudinal_le hR hforig.integrableOn
    (fun p => sq_nonneg (fderiv ℝ f (t,p) (1,0)))
  rw [kelvin_longitudinal_integral hR (fun p => longitudinalDensity (fderiv ℝ f) (t,p))] at hl
  linarith


def exteriorCylinder (R : ℝ) : Set Space := univ ×ˢ exteriorDisk R

theorem integral_exteriorCylinder (R : ℝ) {F : Space → ℝ} (hF : Integrable F) :
    (∫ z in exteriorCylinder R, F z) = ∫ t, ∫ p in exteriorDisk R, F (t,p) := by
  have hi : IntegrableOn F (univ ×ˢ exteriorDisk R)
      ((volume : Measure ℝ).prod (volume : Measure Plane)) := hF.integrableOn
  simpa only [exteriorCylinder,← Measure.volume_eq_prod,setIntegral_univ] using setIntegral_prod F hi

theorem exterior_slice_integrable (R : ℝ) {F : Space → ℝ} (hF : Integrable F) :
    Integrable (fun t => ∫ p in exteriorDisk R, F (t,p)) := by
  have hi : IntegrableOn F (univ ×ˢ exteriorDisk R)
      ((volume : Measure ℝ).prod (volume : Measure Plane)) := hF.integrableOn
  rw [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ] at hi
  exact hi.integral_prod_left

/-- The exact factor two for the genuine global weak transverse gradient. -/
theorem global_transverse_energy (glue : SmoothInterfaceGluing) {R : ℝ}
    (hR : 0 < R) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, transverseDensity (extensionDerivative R f) z) =
      2 * ∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z := by
  have hE := transverseDensity_integrable (extension_inH1 glue hR hf hc).2.1
  have hF := transverseDensity_integrable (compact_derivative_memLp hf hc)
  have heq := integral_prod _ hE
  change (∫ z, transverseDensity (extensionDerivative R f) z) = _ at heq
  rw [heq,integral_exteriorCylinder R hF,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hE.prod_right_ae] with t ht
  exact transverse_slice_energy hR hf t ht

/-- The longitudinal factor two uses the actual inversion weight, bounded
by one on the exterior; no norm or weak derivative is supplied as a premise. -/
theorem global_longitudinal_bound (glue : SmoothInterfaceGluing) {R : ℝ}
    (hR : 0 < R) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, longitudinalDensity (extensionDerivative R f) z) ≤
      2 * ∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z := by
  have hE := longitudinalDensity_integrable (extension_inH1 glue hR hf hc).2.1
  have hF := longitudinalDensity_integrable (compact_derivative_memLp hf hc)
  have heq := integral_prod _ hE
  change (∫ z, longitudinalDensity (extensionDerivative R f) z) = _ at heq
  rw [heq,integral_exteriorCylinder R hF,← integral_const_mul]
  apply integral_mono_ae hE.integral_prod_left ((exterior_slice_integrable R hF).const_mul 2)
  filter_upwards [hE.prod_right_ae,hF.prod_right_ae] with t ht htf
  exact longitudinal_slice_bound hR hf t ht htf


theorem longitudinal_weight_integrable {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    IntegrableOn (fun z => kelvinWeight R z.2 * longitudinalDensity (fderiv ℝ f) z)
      (exteriorCylinder R) := by
  have hF := longitudinalDensity_integrable (compact_derivative_memLp hf hc)
  have hm : MeasurableSet (exteriorCylinder R) :=
    MeasurableSet.univ.prod (exteriorDisk_measurable R)
  have hw : AEStronglyMeasurable (fun z : Space => kelvinWeight R z.2)
      (volume.restrict (exteriorCylinder R)) :=
    ((weight_measurable R).comp measurable_snd).aestronglyMeasurable
  apply hF.integrableOn.mono' (hw.mul hF.integrableOn.aestronglyMeasurable)
  apply ae_restrict_of_forall_mem hm
  intro z hz
  change ‖kelvinWeight R z.2 * longitudinalDensity (fderiv ℝ f) z‖ ≤
    longitudinalDensity (fderiv ℝ f) z
  have hnon : 0 ≤ longitudinalDensity (fderiv ℝ f) z := sq_nonneg _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg R z.2) hnon)]
  exact mul_le_of_le_one_left hnon (weight_le_one_exterior hR hz.2)

/-- The literal weighted equality displayed in the English proof. -/
theorem global_longitudinal_identity (glue : SmoothInterfaceGluing) {R : ℝ}
    (hR : 0 < R) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, longitudinalDensity (extensionDerivative R f) z) =
      ∫ z in exteriorCylinder R,
        (1 + kelvinWeight R z.2) * longitudinalDensity (fderiv ℝ f) z := by
  have hE := longitudinalDensity_integrable (extension_inH1 glue hR hf hc).2.1
  have hF := longitudinalDensity_integrable (compact_derivative_memLp hf hc)
  have hW := longitudinal_weight_integrable hR hf hc
  have hsum : (∫ z in exteriorCylinder R,
      (1 + kelvinWeight R z.2) * longitudinalDensity (fderiv ℝ f) z) =
      (∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z) +
      ∫ z in exteriorCylinder R, kelvinWeight R z.2 * longitudinalDensity (fderiv ℝ f) z := by
    simp_rw [add_mul,one_mul]
    exact integral_add hF.integrableOn hW
  have heq := integral_prod _ hE
  change (∫ z, longitudinalDensity (extensionDerivative R f) z) = _ at heq
  have hwprod := setIntegral_prod _ hW
  change (∫ z in exteriorCylinder R,
    kelvinWeight R z.2 * longitudinalDensity (fderiv ℝ f) z) = _ at hwprod
  simp only [setIntegral_univ] at hwprod
  have hW' : Integrable (fun z => kelvinWeight R z.2 * longitudinalDensity (fderiv ℝ f) z)
      ((volume : Measure ℝ).prod ((volume : Measure Plane).restrict (exteriorDisk R))) := by
    have h := hW
    change IntegrableOn _ (univ ×ˢ exteriorDisk R) (volume.prod volume) at h
    rwa [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ] at h
  rw [heq,hsum,integral_exteriorCylinder R hF,hwprod,
    ← integral_add (exterior_slice_integrable R hF) hW'.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [hE.prod_right_ae] with t ht
  rw [plane_integral_split R ht,longitudinal_inner_integral hR hf t]
  have he : (∫ p in exteriorDisk R, longitudinalDensity (extensionDerivative R f) (t,p)) =
      ∫ p in exteriorDisk R, longitudinalDensity (fderiv ℝ f) (t,p) := by
    apply setIntegral_congr_fun (exteriorDisk_measurable R)
    intro p hp
    dsimp only
    unfold longitudinalDensity
    rw [extensionDerivative_exterior f hp.le]
  rw [he,add_comm]


/-- One checked terminal packages the H1 extension and both energy estimates. -/
theorem kelvin_H1_and_energies (glue : SmoothInterfaceGluing) {R : ℝ}
    (hR : 0 < R) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    InH1 (extension R f) (extensionDerivative R f) ∧
    (∫ z, transverseDensity (extensionDerivative R f) z) =
      2 * ∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z ∧
    (∫ z, longitudinalDensity (extensionDerivative R f) z) ≤
      2 * ∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z :=
  ⟨extension_inH1 glue hR hf hc,global_transverse_energy glue hR hf hc,
    global_longitudinal_bound glue hR hf hc⟩


#print axioms circle_measure_zero
#print axioms ae_plane_regular
#print axioms plane_integral_split
#print axioms derivative_eval_memLp
#print axioms longitudinalDensity_integrable
#print axioms transverseDensity_integrable
#print axioms compact_derivative_memLp
#print axioms inner_transverseGradient
#print axioms extensionDerivative_inner
#print axioms extensionDerivative_exterior
#print axioms transverse_inner_integral
#print axioms transverse_slice_energy
#print axioms longitudinal_inner_integral
#print axioms longitudinal_slice_bound
#print axioms integral_exteriorCylinder
#print axioms exterior_slice_integrable
#print axioms global_transverse_energy
#print axioms global_longitudinal_bound
#print axioms longitudinal_weight_integrable
#print axioms global_longitudinal_identity
#print axioms kelvin_H1_and_energies
end BWork.Kelvin
