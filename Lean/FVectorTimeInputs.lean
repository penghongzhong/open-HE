import FDirectionalVectorTransfer
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- Eight extended mixed norms of the original functions and vector gradients.
The separate spatial-slice hypotheses prevent any infinity-to-real truncation. -/
def VectorTimeInputs {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space) : Prop :=
  mixedNorm mu volume ∞ 6 u ≠ ∞ ∧ mixedNorm mu volume ∞ 6 v ≠ ∞ ∧
  mixedNorm mu volume 10 10 u ≠ ∞ ∧ mixedNorm mu volume 10 10 v ≠ ∞ ∧
  mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) U ≠ ∞ ∧
  mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) V ≠ ∞ ∧
  mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P ≠ ∞ ∧
  mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q ≠ ∞

theorem amplitude_real_slice_time_memLp {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (u v : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hsu : ∀ᵐ t ∂mu, MemLp (u t) q volume) (hsv : ∀ᵐ t ∂mu, MemLp (v t) q volume)
    (htu : MemLp (fun t => (eLpNorm (u t) q volume).toReal) p mu)
    (htv : MemLp (fun t => (eLpNorm (v t) q volume).toReal) p mu) :
    MemLp (fun t => (eLpNorm (sumAmplitude (u t) (v t)) q volume).toReal) p mu ∧
    MemLp (fun t => (eLpNorm (differenceAmplitude (u t) (v t)) q volume).toReal) p mu := by
  have hsum := real_slice_time_domination mu p q hq hqtop
    (fun t => sumAmplitude (u t) (v t)) u v (hu.norm.add hv.norm) hsu hsv htu htv
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => by
      dsimp only [sumAmplitude]
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))])
  have hdiff := real_slice_time_domination mu p q hq hqtop
    (fun t x => u t x - v t x) u v (hu.sub hv) hsu hsv htu htv
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => norm_sub_le _ _)
  exact ⟨hsum.1, hdiff.2⟩

theorem vector_time_inputs_directional
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hSlices : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hP : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (mu.prod volume))
    (hQ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume))
    (hInputs : VectorTimeInputs mu u v U V P Q) (e : Space) (he : ‖e‖ = 1) :
    FiniteTimeInputs mu
      (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
      (fun t x => ‖directionalField (P t) (Q t) e x‖)
      (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) := by
  rcases hInputs with ⟨tu6, tv6, tu10, tv10, tU, tV, tP, tQ⟩
  have su6 : ∀ᵐ t ∂mu, MemLp (u t) 6 volume := hSlices.mono fun _ ht => ht.1.function_L6
  have sv6 : ∀ᵐ t ∂mu, MemLp (v t) 6 volume := hSlices.mono fun _ ht => ht.2.1.function_L6
  have su10 := hSlices.mono fun _ ht => ht.2.2.1
  have sv10 := hSlices.mono fun _ ht => ht.2.2.2.1
  have sU := hSlices.mono fun _ ht => ht.2.2.2.2.1
  have sV := hSlices.mono fun _ ht => ht.2.2.2.2.2.1
  have sP := hSlices.mono fun _ ht => ht.2.2.2.2.2.2.1
  have sQ := hSlices.mono fun _ ht => ht.2.2.2.2.2.2.2
  have rtu6 := real_slice_time_memLp_of_mixed mu ∞ 6 (by norm_num) (by norm_num) u hu su6 tu6
  have rtv6 := real_slice_time_memLp_of_mixed mu ∞ 6 (by norm_num) (by norm_num) v hv sv6 tv6
  have rtu10 := real_slice_time_memLp_of_mixed mu 10 10 (by norm_num) (by norm_num) u hu su10 tu10
  have rtv10 := real_slice_time_memLp_of_mixed mu 10 10 (by norm_num) (by norm_num) v hv sv10 tv10
  have rtU := real_slice_time_memLp_of_mixed mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top U hU sU tU
  have rtV := real_slice_time_memLp_of_mixed mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top V hV sV tV
  have rtP := real_slice_time_memLp_of_mixed mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top P hP sP tP
  have rtQ := real_slice_time_memLp_of_mixed mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top Q hQ sQ tQ
  have a6 := amplitude_real_slice_time_memLp mu ∞ 6 (by norm_num) (by norm_num)
    u v hu hv su6 sv6 rtu6 rtv6
  have a10 := amplitude_real_slice_time_memLp mu 10 10 (by norm_num) (by norm_num)
    u v hu hv su10 sv10 rtu10 rtv10
  have rG := directional_real_slice_time_memLp mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top U V e he hU hV sU sV rtU rtV
  have rK := directional_real_slice_time_memLp mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top P Q e he hP hQ sP sQ rtP rtQ
  have jG := directional_field_joint_measurable mu U V e hU hV
  have jK := directional_field_joint_measurable mu P Q e hP hQ
  have sG : ∀ᵐ t ∂mu, MemLp (directionalField (U t) (V t) e) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [sU, sV] with t htU htV
    exact directionalField_memLp htU htV e
  have sK : ∀ᵐ t ∂mu, MemLp (directionalField (P t) (Q t) e) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [sP, sQ] with t htP htQ
    exact directionalField_memLp htP htQ e
  have rZ := real_slice_time_domination mu 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top
    (fun t x => directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x)
    (fun t => directionalField (U t) (V t) e) (fun t => directionalField (P t) (Q t) e)
    (jG.sub jK) sG sK rG.1 rK.1
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => norm_sub_le _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat] using a6.1.eLpNorm_ne_top
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat] using a10.1.eLpNorm_ne_top
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat] using a6.2.eLpNorm_ne_top
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat] using a10.2.eLpNorm_ne_top
  · exact rK.2.eLpNorm_ne_top
  · exact rZ.2.eLpNorm_ne_top

end HartreeF.TimeHolder
