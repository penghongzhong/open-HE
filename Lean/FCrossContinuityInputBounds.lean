import FCrossContinuityTime
import FMixedVectorQuantitative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants TimeHolder CompactCross

def valueSize (p q : ℝ≥0∞) (u U v V : ℝ → Space → ℂ) : ℝ≥0∞ :=
  (mixedNorm volume volume p q u+mixedNorm volume volume p q U)+
    (mixedNorm volume volume p q v+mixedNorm volume volume p q V)

def changeSize (p q : ℝ≥0∞) (u U v V : ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume p q (u-U)+mixedNorm volume volume p q (v-V)

def referenceSize (H K : ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) H+
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) K

theorem mixed_sum_norm_bound {p q : ℝ≥0∞} (hp : 1≤p) (hq : 1≤q) (hqt : q≠∞)
    {f g : ℝ → Space → ℂ}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => ‖f t x‖+‖g t x‖) ≤
      mixedNorm volume volume p q f+mixedNorm volume volume p q g := by
  apply mixed_norm_le_add_of_domination volume p q hp hq hqt _ f g (hf.norm.add hg.norm) hf hg
  filter_upwards [] with t
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem mixed_value_envelope_bound {p q : ℝ≥0∞} (hp : 1≤p) (hq : 1≤q) (hqt : q≠∞)
    {u U h H v V k K : ℝ → Space → ℂ} (hJ : JointInputs u U h H v V k K) :
    mixedNorm volume volume p q (fun t => valueEnvelope (u t) (U t) (v t) (V t)) ≤
      valueSize p q u U v V := by
  have h1 := mixed_sum_norm_bound hp hq hqt hJ.uM hJ.UM
  have h2 := mixed_sum_norm_bound hp hq hqt hJ.vM hJ.VM
  have hsum := mixed_norm_le_add_of_domination volume p q hp hq hqt
    (fun t => valueEnvelope (u t) (U t) (v t) (V t))
    (fun t => sumAmplitude (u t) (U t)) (fun t => sumAmplitude (v t) (V t))
    ((hJ.uM.norm.add hJ.UM.norm).add (hJ.vM.norm.add hJ.VM.norm))
    (hJ.uM.norm.add hJ.UM.norm) (hJ.vM.norm.add hJ.VM.norm) (by
      filter_upwards [] with t
      filter_upwards [] with x
      exact norm_add_le _ _)
  exact hsum.trans (add_le_add h1 h2)

theorem mixed_difference_envelope_bound {p q : ℝ≥0∞} (hp : 1≤p) (hq : 1≤q) (hqt : q≠∞)
    {u U h H v V k K : ℝ → Space → ℂ} (hJ : JointInputs u U h H v V k K) :
    mixedNorm volume volume p q (fun t => differenceEnvelope (u t) (U t) (v t) (V t)) ≤
      changeSize p q u U v V :=
  mixed_sum_norm_bound hp hq hqt (hJ.uM.sub hJ.UM) (hJ.vM.sub hJ.VM)

theorem changeSize_le_valueSize {p q : ℝ≥0∞} (hp : 1≤p) (hq : 1≤q) (hqt : q≠∞)
    {u U h H v V k K : ℝ → Space → ℂ} (hJ : JointInputs u U h H v V k K) :
    changeSize p q u U v V ≤ valueSize p q u U v V := by
  apply add_le_add
  · apply mixed_norm_le_add_of_domination volume p q hp hq hqt (u-U) u U (hJ.uM.sub hJ.UM) hJ.uM hJ.UM
    filter_upwards [] with t
    filter_upwards [] with x
    exact norm_sub_le _ _
  · apply mixed_norm_le_add_of_domination volume p q hp hq hqt (v-V) v V (hJ.vM.sub hJ.VM) hJ.vM hJ.VM
    filter_upwards [] with t
    filter_upwards [] with x
    exact norm_sub_le _ _

/-- All six real time norms in the continuity budget are bounded by actual
extended mixed norms of the original fields and differences. -/
theorem real_envelope_input_bounds
    {u U h H v V k K : ℝ → Space → ℂ} (hJ : JointInputs u U h H v V k K)
    (hs : ∀ᵐ t ∂(volume : Measure ℝ), SliceInputs (u t) (U t) (h t) (H t) (v t) (V t) (k t) (K t)) :
    let A := fun t => valueEnvelope (u t) (U t) (v t) (V t)
    let B := fun t => differenceEnvelope (u t) (U t) (v t) (V t)
    let Y := fun t => referenceEnvelope (H t) (K t)
    let Z := fun t => directionEnvelope (h t) (H t) (k t) (K t)
    eLpNorm (fun t => spatialNorm 6 (A t)) ∞ volume ≤ valueSize ∞ 6 u U v V ∧
    eLpNorm (fun t => spatialNorm 10 (A t)) 10 volume ≤ valueSize 10 10 u U v V ∧
    eLpNorm (fun t => spatialNorm 6 (B t)) ∞ volume ≤ valueSize ∞ 6 u U v V ∧
    eLpNorm (fun t => spatialNorm 10 (B t)) 10 volume ≤ changeSize 10 10 u U v V ∧
    eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 volume ≤ referenceSize H K ∧
    eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 volume ≤
      changeSize 10 (ENNReal.ofReal (30/13 : ℝ)) h H k K := by
  dsimp only
  let A := fun t => valueEnvelope (u t) (U t) (v t) (V t)
  let B := fun t => differenceEnvelope (u t) (U t) (v t) (V t)
  let Y := fun t => referenceEnvelope (H t) (K t)
  let Z := fun t => directionEnvelope (h t) (H t) (k t) (K t)
  have hA := (hJ.uM.norm.add hJ.UM.norm).add (hJ.vM.norm.add hJ.VM.norm)
  have hB := (hJ.uM.sub hJ.UM).norm.add (hJ.vM.sub hJ.VM).norm
  have hY := hJ.HM.norm.add hJ.KM.norm
  have hZ := (hJ.hM.sub hJ.HM).norm.add (hJ.kM.sub hJ.KM).norm
  have hA6 := real_slice_mixed_eq volume ∞ 6 (by norm_num) (by norm_num) A hA
    (hs.mono fun _ ht => (ht.u6.norm.add ht.U6.norm).add (ht.v6.norm.add ht.V6.norm))
  have hA10 := real_slice_mixed_eq volume 10 10 (by norm_num) (by norm_num) A hA
    (hs.mono fun _ ht => (ht.u10.norm.add ht.U10.norm).add (ht.v10.norm.add ht.V10.norm))
  have hB6 := real_slice_mixed_eq volume ∞ 6 (by norm_num) (by norm_num) B hB
    (hs.mono fun _ ht => (ht.u6.sub ht.U6).norm.add (ht.v6.sub ht.V6).norm)
  have hB10 := real_slice_mixed_eq volume 10 10 (by norm_num) (by norm_num) B hB
    (hs.mono fun _ ht => (ht.u10.sub ht.U10).norm.add (ht.v10.sub ht.V10).norm)
  have hYY := real_slice_mixed_eq volume 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top Y hY (hs.mono fun _ ht => ht.HW.norm.add ht.KW.norm)
  have hZZ := real_slice_mixed_eq volume 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top Z hZ
    (hs.mono fun _ ht => (ht.hW.sub ht.HW).norm.add (ht.kW.sub ht.KW).norm)
  have hAb6 := mixed_value_envelope_bound (p := ∞) (q := 6) (by simp) (by norm_num) (by norm_num) hJ
  have hAb10 := mixed_value_envelope_bound (p := 10) (q := 10) (by norm_num) (by norm_num) (by norm_num) hJ
  have hBb6 := (mixed_difference_envelope_bound (p := ∞) (q := 6) (by simp) (by norm_num) (by norm_num) hJ).trans
    (changeSize_le_valueSize (p := ∞) (q := 6) (by simp) (by norm_num) (by norm_num) hJ)
  have hBb10 := mixed_difference_envelope_bound (p := 10) (q := 10) (by norm_num) (by norm_num) (by norm_num) hJ
  have hYb := mixed_sum_norm_bound (p := 10) (q := ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top hJ.HM hJ.KM
  have hZb := mixed_sum_norm_bound (f := h-H) (g := k-K) (p := 10) (q := ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top (hJ.hM.sub hJ.HM) (hJ.kM.sub hJ.KM)
  simpa only [spatialNorm, ENNReal.ofReal_ofNat, A, B, Y, Z, referenceSize, changeSize] using
    And.intro (hA6.le.trans hAb6) (And.intro (hA10.le.trans hAb10)
      (And.intro (hB6.le.trans hBb6) (And.intro (hB10.le.trans hBb10)
        (And.intro (hYY.le.trans hYb) (hZZ.le.trans hZb)))))

#print axioms real_envelope_input_bounds
end HartreeF.CrossContinuity
