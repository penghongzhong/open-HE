import FVectorSliceTransfer
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

theorem directional_field_joint_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (U V : T → Space → Space) (e : Space)
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun z : T × Space => directionalField (U z.1) (V z.1) e z.2)
      (mu.prod volume) := by
  have hc : Continuous (fun w : Space × Space =>
      Complex.equivRealProdCLM.symm (⟪w.1, e⟫, ⟪w.2, e⟫)) :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_fst.inner continuous_const).prodMk (continuous_snd.inner continuous_const))
  exact hc.comp_aestronglyMeasurable (hU.prodMk hV)

theorem unit_directional_norm_le (U V : Space → Space) (e : Space) (he : ‖e‖ = 1) (x : Space) :
    ‖directionalField U V e x‖ ≤ ‖U x‖ + ‖V x‖ := by
  have hb := Complex.norm_le_abs_re_add_abs_im (directionalField U V e x)
  simp only [directionalField, Complex.equivRealProdCLM_symm_apply_re,
    Complex.equivRealProdCLM_symm_apply_im] at hb
  apply hb.trans
  simpa only [he, mul_one] using add_le_add
    (abs_real_inner_le_norm (U x) e) (abs_real_inner_le_norm (V x) e)

theorem directional_real_slice_time_memLp {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (U V : T → Space → Space) (e : Space) (he : ‖e‖ = 1)
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hsU : ∀ᵐ t ∂mu, MemLp (U t) q volume) (hsV : ∀ᵐ t ∂mu, MemLp (V t) q volume)
    (htU : MemLp (fun t => (eLpNorm (U t) q volume).toReal) p mu)
    (htV : MemLp (fun t => (eLpNorm (V t) q volume).toReal) p mu) :
    MemLp (fun t => (eLpNorm (directionalField (U t) (V t) e) q volume).toReal) p mu ∧
    MemLp (fun t => (eLpNorm (fun x => ‖directionalField (U t) (V t) e x‖) q volume).toReal) p mu := by
  apply real_slice_time_domination mu p q hq hqtop
    (fun t => directionalField (U t) (V t) e) U V
    (directional_field_joint_measurable mu U V e hU hV) hsU hsV htU htV
  exact Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x =>
    unit_directional_norm_le (U t) (V t) e he x

end HartreeF.TimeHolder
