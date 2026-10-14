import FSpatialMollifierMixed

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial convolution preserves compact spacetime support with its exact compact support enlargement. -/
theorem spatialMollify_joint_compact (φ : ContDiffBump (0 : Space))
    (f : ℝ → Space → E) (hf : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) :
    HasCompactSupport (fun z : ℝ × Space => spatialMollify φ (f z.1) z.2) := by
  let K := tsupport (fun z : ℝ × Space => f z.1 z.2)
  apply HasCompactSupport.intro ((hf.image continuous_fst).prod
    ((hf.image continuous_snd).add (φ.hasCompactSupport_normed (μ := (volume : Measure Space)))))
  intro z hz
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change φ.normed volume y • f z.1 (z.2 - y) = 0
  by_cases hk : φ.normed volume y = 0
  · simp [hk]
  by_cases hg : f z.1 (z.2 - y) = 0
  · simp [hg]
  have hF : (z.1, z.2 - y) ∈ K := subset_closure hg
  have hK : y ∈ tsupport (φ.normed volume) := subset_closure hk
  exact False.elim (hz ⟨⟨(z.1, z.2-y), hF, rfl⟩,
    Set.mem_add.mpr ⟨z.2-y, ⟨(z.1, z.2-y), hF, rfl⟩, y, hK, sub_add_cancel _ _⟩⟩)

omit [NormedSpace ℝ E] in
/-- Compact support and finite spatial Lp imply the L1 domain used in the convolution identification. -/
theorem integrable_of_memLp_compact {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Space → E}
    (hf : MemLp f p volume) (hc : HasCompactSupport f) : Integrable f volume := by
  have hlocal : IntegrableOn f (tsupport f) volume := by
    let : IsFiniteMeasure (volume.restrict (tsupport f)) :=
      isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
    exact ((hf.restrict (tsupport f)).mono_exponent hp).integrable (by norm_num)
  exact (integrableOn_iff_integrable_of_support_subset subset_closure).mp hlocal

#print axioms spatialMollify_joint_compact
#print axioms integrable_of_memLp_compact
end HartreeF.ProfileSpatialSmoothing
