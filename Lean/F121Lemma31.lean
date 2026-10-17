import CriticalSobolevBridge
import FFiniteProfileWeakGradient
import FHomogeneousStabilityNorms

/-! A literal terminal wrapper for Lemma 3.1 of the 121-page manuscript.
The spatial target membership is produced, and the path estimate uses the
actual Euclidean complex gradient rather than a coordinate-sum surrogate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.Paper121Lemma31
open SobolevStretch StationarySelfTest CriticalSobolevBridge TimeHolder
open EnergySpace CriticalPathSpace CriticalJointSources CriticalSourceBounds
open HomogeneousStability FiniteProfileWeakGradient EndpointOutput

/-- One explicit admissible constant for the manuscript's critical spatial
Sobolev comparison. -/
def criticalSobolevConstant (K : ℝ) : ℝ :=
  2 * ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ))

/-- Each real gradient projection is pointwise dominated by the packed
Euclidean complex gradient. -/
theorem projected_norm_le_complexGradient (U V : Space → Space) (x : Space) :
    ‖U x‖ ≤ ‖complexGradient U V x‖ ∧
      ‖V x‖ ≤ ‖complexGradient U V x‖ := by
  have h := complexGradient_norm_sq U V x
  constructor <;> nlinarith [norm_nonneg (U x), norm_nonneg (V x),
    norm_nonneg (complexGradient U V x), sq_nonneg ‖U x‖, sq_nonneg ‖V x‖]

/-- Literal spatial part of Lemma 3.1. Membership in L10 is an output, and
the input L30/13 norm is the norm of the actual packed complex gradient. -/
theorem critical_spatial_sobolev_comparison
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hGradient : MemLp (complexGradient U V)
      (ENNReal.ofReal (30 / 13 : ℝ)) volume) :
    MemLp u 10 volume ∧
      (eLpNorm u 10 volume).toReal ≤ criticalSobolevConstant K *
        (eLpNorm (complexGradient U V)
          (ENNReal.ofReal (30 / 13 : ℝ)) volume).toReal := by
  obtain ⟨hU, hV⟩ := packed_memLp_real_imag hGradient
  obtain ⟨hu10, hbase⟩ :=
    critical_dotH1_memLp_ten_and_bound hDensity hSob hu hU hV
  have hUG : eLpNorm U (ENNReal.ofReal (30 / 13 : ℝ)) volume ≤
      eLpNorm (complexGradient U V) (ENNReal.ofReal (30 / 13 : ℝ)) volume :=
    eLpNorm_mono hU.aestronglyMeasurable
      (fun x => (projected_norm_le_complexGradient U V x).1)
  have hVG : eLpNorm V (ENNReal.ofReal (30 / 13 : ℝ)) volume ≤
      eLpNorm (complexGradient U V) (ENNReal.ofReal (30 / 13 : ℝ)) volume :=
    eLpNorm_mono hV.aestronglyMeasurable
      (fun x => (projected_norm_le_complexGradient U V x).2)
  have hUr := ENNReal.toReal_mono hGradient.eLpNorm_ne_top hUG
  have hVr := ENNReal.toReal_mono hGradient.eLpNorm_ne_top hVG
  have hC : 0 ≤ (5 / 3 : ℝ) * K ^ (1 / 6 : ℝ) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hSob.nonneg _)
  refine ⟨hu10, hbase.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left (add_le_add hUr hVr) hC).trans_eq
  unfold criticalSobolevConstant
  ring

/-- Monotonicity of the extended mixed norm under a pointwise norm bound.
Only measurability of the smaller field is needed. -/
theorem mixedNorm_mono_of_norm_le
    {T E F : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure T) [SigmaFinite mu] {p q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    {f : T → Space → E} {g : T → Space → F}
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2)
      (mu.prod volume))
    (hfg : ∀ t x, ‖f t x‖ ≤ ‖g t x‖) :
    mixedNorm mu volume p q f ≤ mixedNorm mu volume p q g := by
  apply eLpNorm_mono_enorm_ae
    (spatial_lp_time_measurable mu volume q hq0 hqTop f hf)
  filter_upwards [hf.prodMk_left] with t ht
  simpa only [enorm_eq_self] using eLpNorm_mono ht (hfg t)

/-- The path consequence in the exact manuscript norms: the left side is the
actual value field and the right side is the actual Euclidean complex gradient. -/
theorem critical_path_sobolev_comparison
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {a b : ℝ} (z : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ z t)) ≤
      (2 * ENNReal.ofReal ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ))) *
        mixedNorm (intervalMeasure a b) volume 10 criticalExponent
          (fun t => energyComplexGradient (energyPath _ z t)) := by
  let r := jointFields (intervalMeasure a b) z
  let G := jointComplexGradient z
  have hU : mixedNorm (intervalMeasure a b) volume 10 criticalExponent r.U ≤
      mixedNorm (intervalMeasure a b) volume 10 criticalExponent G := by
    exact mixedNorm_mono_of_norm_le (intervalMeasure a b)
      (by norm_num [criticalExponent]) (by norm_num [criticalExponent])
      r.joint_U.aestronglyMeasurable
      (fun t x => (projected_norm_le_complexGradient (r.U t) (r.V t) x).1)
  have hV : mixedNorm (intervalMeasure a b) volume 10 criticalExponent r.V ≤
      mixedNorm (intervalMeasure a b) volume 10 criticalExponent G := by
    exact mixedNorm_mono_of_norm_le (intervalMeasure a b)
      (by norm_num [criticalExponent]) (by norm_num [criticalExponent])
      r.joint_V.aestronglyMeasurable
      (fun t x => (projected_norm_le_complexGradient (r.U t) (r.V t) x).2)
  have hgradient : pathGradientSize (intervalMeasure a b) z ≤
      2 * mixedNorm (intervalMeasure a b) volume 10 criticalExponent G := by
    change mixedNorm (intervalMeasure a b) volume 10 criticalExponent r.U +
      mixedNorm (intervalMeasure a b) volume 10 criticalExponent r.V ≤ _
    calc
      _ ≤ mixedNorm (intervalMeasure a b) volume 10 criticalExponent G +
          mixedNorm (intervalMeasure a b) volume 10 criticalExponent G :=
        add_le_add hU hV
      _ = _ := by ring
  have hvalue : mixedNorm (intervalMeasure a b) volume 10 10 r.u =
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ z t)) := by
    exact mixedNorm_congr_slices (intervalMeasure a b) 10 10
      (r.slice_eq.mono fun _ ht => ht.1)
  have hactual : mixedNorm (intervalMeasure a b) volume 10 criticalExponent G =
      mixedNorm (intervalMeasure a b) volume 10 criticalExponent
        (fun t => energyComplexGradient (energyPath _ z t)) := by
    exact mixedNorm_congr_slices (intervalMeasure a b) 10 criticalExponent
      (jointComplexGradient_slice_eq z)
  rw [← hvalue, ← hactual]
  calc
    _ ≤ ENNReal.ofReal ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ)) *
        pathGradientSize (intervalMeasure a b) z :=
      joint_value_critical_bound (intervalMeasure a b) hDensity hSob z
    _ ≤ ENNReal.ofReal ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ)) *
        (2 * mixedNorm (intervalMeasure a b) volume 10 criticalExponent G) :=
      mul_le_mul' le_rfl hgradient
    _ = _ := by ring

/-- Full Lemma 3.1, packaging its spatial assertion and its path-graph
consequence without assuming either target estimate. -/
theorem lemma31_critical_spatial_and_path
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hGradient : MemLp (complexGradient U V)
      (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    {a b : ℝ} (z : CriticalPath (intervalMeasure a b)) :
    (MemLp u 10 volume ∧
      (eLpNorm u 10 volume).toReal ≤ criticalSobolevConstant K *
        (eLpNorm (complexGradient U V)
          (ENNReal.ofReal (30 / 13 : ℝ)) volume).toReal) ∧
    mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ z t)) ≤
      (2 * ENNReal.ofReal ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ))) *
        mixedNorm (intervalMeasure a b) volume 10 criticalExponent
          (fun t => energyComplexGradient (energyPath _ z t)) := by
  exact ⟨critical_spatial_sobolev_comparison hDensity hSob hu hGradient,
    critical_path_sobolev_comparison hDensity hSob z⟩

end HartreeF.Paper121Lemma31
