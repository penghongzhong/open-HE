import FR2ActualProfileFrames
import FFreeValueGradientDefect
import FActualVectorDifferenceBound

/-! One spatial derivative of the actual framed Hartree source. The jointly
measurable candidate, canonical nested AE, and weak tests are obtained before
using the vector numerical estimate. Author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.R2TailForcing
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ForcingDomain
  ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross CriticalTimeSobolev
  R2Global R2Frames FreeValueGradient FiniteProfileWeakGradient WeakHartreeProduct
  FiniteProfileMixedDefects

/-- The same actual full gradient minus the zero-state full gradient. The
subtraction is retained; no pointwise zero claim about totalized derivatives is used. -/
def sourceGradient {g : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume g) : ℝ → Space → CGradient :=
  actualGradient α c 0 r.u 0 0 r.U r.V

def sourceCandidate {g : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume g) : ℝ → Space → CGradient :=
  candidateGradient α c 0 r.u 0 0 r.U r.V

private theorem direction_eq_coordinate (U V : ℝ → Space → Space) (j : Fin 3) :
    directionCoordinate U V j =
      gradientCoordinate j (fun t => complexGradient (U t) (V t)) := by
  funext t x
  apply Complex.ext <;>
    simp [directionCoordinate, directionalField, gradientCoordinate, complexGradient,
      EuclideanSpace.inner_single_right]

private theorem zero_profile (j : Fin 3) :
    ScalarProfile (0 : ℝ → Space → ℂ) (directionCoordinate 0 0 j) := by
  have he : directionCoordinate (0 : ℝ → Space → Space) 0 j = 0 := by
    funext t x
    simp [directionCoordinate, directionalField]
  rw [he]
  exact ⟨stronglyMeasurable_const, stronglyMeasurable_const,
    by simp [mixedNorm], by simp [mixedNorm], by simp [mixedNorm]⟩

private theorem zero_inDot : InDotH1 (0 : Space → ℂ) 0 0 := by
  refine ⟨MemLp.zero, MemLp.zero, MemLp.zero, ?_, ?_⟩
  · change HasWeakGradient (fun _ : Space => (0 : ℝ)) (fun _ => 0)
    exact FiniteProfileWeakGradient.weakGradient_zero
  · change HasWeakGradient (fun _ : Space => (0 : ℝ)) (fun _ => 0)
    exact FiniteProfileWeakGradient.weakGradient_zero

/-- The per-coordinate domains use the true global X of this actual curve. -/
theorem joint_scalar_profiles {K : ℝ} (hSob : OrdinarySobolev K)
    {g : ℝ → EnergyState} (hg : CurveFinite g) (r : EnergyJointFields volume g)
    (j : Fin 3) : ScalarProfile r.u (directionCoordinate r.U r.V j) := by
  rw [direction_eq_coordinate]
  have hG := packedGradient_joint_stronglyMeasurable r.joint_U r.joint_V
  refine ⟨r.joint_u, gradientCoordinate_joint_stronglyMeasurable j _ hG, ?_, ?_, ?_⟩
  · exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.energy)
      (jointFields_value_sobolev_bound hSob g r)
  · rw [R2Global.joint_value_norm]
    exact hg.value
  · exact ne_top_of_le_ne_top hg.gradient
      ((gradientCoordinate_mixed_le (by norm_num) ENNReal.ofReal_ne_top j _
        hG.aestronglyMeasurable).trans_eq
          (R2Global.joint_gradient_norm g r 10 (ENNReal.ofReal (30/13 : ℝ))))

/-- Every spatial, temporal, representative and weak-gradient field is real
output of the earlier two-state producer, used here at zero and this profile. -/
theorem source_domains (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    {g : ℝ → EnergyState} (hg : CurveFinite g) (r : EnergyJointFields volume g) :
    ActualDefectDomains α c 0 r.u 0 0 r.U r.V :=
  actual_free_value_gradient_domains hDensity hSob hH 0 r.u 0 0 r.U r.V
    zero_profile (joint_scalar_profiles hSob hg r) (ae_of_all _ fun _ => zero_inDot) r.inDotH1

/-- The literal scalar source is F(u); this requires no assertion about the
pointwise value of the raw derivative at the zero state. -/
theorem literal_source_eq {g : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume g) : literalForcing α c 0 r.u =
      (fun t => forcing α c (r.u t)) := by
  funext t x
  simp only [literalForcing, zero_add, forcing_apply, Pi.zero_apply, norm_zero,
    mul_zero, sub_zero]

/-- The scalar represented by the source packet is the canonical forcing of
this same EnergyState curve, on the already supplied nested conull set. -/
theorem source_scalar_canonical_ae {g : ℝ → EnergyState} (α c : ℝ)
    (r : EnergyJointFields volume g) :
    ∀ᵐ t ∂volume, literalForcing α c 0 r.u t =ᵐ[volume]
      forcing α c (energyValue (g t)) := by
  rw [literal_source_eq]
  filter_upwards [r.slice_eq] with t ht
  have hp : potential α c (r.u t) = potential α c (energyValue (g t)) := by
    funext x
    apply integral_congr_ae
    filter_upwards [ht.1] with y hy
    simp only [powerDensity, hy]
  filter_upwards [ht.1] with x hx
  simp only [forcing_apply, hp, hx]

private theorem projected_norm_le_packed (U V : Space → Space) (x : Space) :
    ‖U x‖ ≤ ‖complexGradient U V x‖ ∧ ‖V x‖ ≤ ‖complexGradient U V x‖ := by
  have h := complexGradient_norm_sq U V x
  constructor <;> nlinarith [norm_nonneg (U x), norm_nonneg (V x),
    norm_nonneg (complexGradient U V x), sq_nonneg ‖U x‖, sq_nonneg ‖V x‖]

private theorem joint_projected_W_le {g : ℝ → EnergyState}
    (r : EnergyJointFields volume g) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U ≤ curveW g ∧
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V ≤ curveW g := by
  have hm := R2Global.joint_gradient_norm g r 10 (ENNReal.ofReal (30/13 : ℝ))
  constructor
  · exact (ProfileApproximation.mixed_mono (by norm_num) ENNReal.ofReal_ne_top
      r.joint_U.aestronglyMeasurable
      (fun t x => (projected_norm_le_packed (r.U t) (r.V t) x).1)).trans_eq hm
  · exact (ProfileApproximation.mixed_mono (by norm_num) ENNReal.ofReal_ne_top
      r.joint_V.aestronglyMeasurable
      (fun t x => (projected_norm_le_packed (r.U t) (r.V t) x).2)).trans_eq hm

private theorem zero_reference_budget {α : ℝ} (_hα : 0 < α)
    {g : ℝ → EnergyState} (r : EnergyJointFields volume g) :
    vectorDifferenceBudget α volume r.u 0 r.U r.V 0 0 =
      mixedNorm volume volume ∞ 6 r.u ^ (2*α) *
      mixedNorm volume volume 10 10 r.u ^ (4 : ℝ) *
      (mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U +
       mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V) := by
  simp [vectorDifferenceBudget, criticalBudget, mixedNorm,
    zero_mul, mul_zero, add_zero, sub_zero]

/-- A fixed coefficient precedes the curve, its frame, and its numerical cap.
This is an estimate for one genuine first spatial derivative. -/
theorem exists_source_gradient_power_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (g : ℝ → EnergyState) (_hg : CurveFinite g)
      (r : EnergyJointFields volume g) (D : ℝ), 0 ≤ D → xNorm g ≤ D →
      ActualDefectDomains α c 0 r.u 0 0 r.U r.V ∧
      vectorForcingNorm (sourceGradient α c r) ≤
        ENNReal.ofReal ((C : ℝ) * D ^ (5+2*α)) := by
  have hα := hH.order_pos
  obtain ⟨C, hC⟩ := actual_full_gradient_vector_difference_bound hH
  let A : ℝ := K ^ ((6 : ℝ)⁻¹)
  have hA : 0 ≤ A := Real.rpow_nonneg hSob.nonneg _
  let C' : ℝ≥0 := ⟨2 * (C : ℝ) * A ^ (2*α), by positivity⟩
  refine ⟨C', fun g hg r D hD hcap => ?_⟩
  have hd : ActualDefectDomains α c 0 r.u 0 0 r.U r.V :=
    source_domains hDensity hSob hH hg r
  have hs : ∀ᵐ t ∂volume,
      InDotH1 (r.u t) (r.U t) (r.V t) ∧ InDotH1 (0 : Space → ℂ) 0 0 ∧
      MemLp (r.u t) 10 volume ∧ MemLp (0 : Space → ℂ) 10 volume ∧
      MemLp (r.U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (r.V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (0 : Space → Space) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (0 : Space → Space) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    simpa only [TruePairSlices, Pi.zero_apply, zero_add] using hd.source_slices
  have hn := hC volume r.u 0 r.U r.V 0 0 hs
    r.joint_u.aestronglyMeasurable aestronglyMeasurable_const
    r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
  have hx : curveX g ≤ ENNReal.ofReal D := by
    rw [← ofReal_xNorm hg]
    exact ENNReal.ofReal_le_ofReal hcap
  have he := (curveEnergy_le_curveX g).trans hx
  have hv : mixedNorm volume volume ∞ 6 r.u ≤ ENNReal.ofReal (A*D) := by
    exact (jointFields_value_sobolev_bound hSob g r).trans
      ((mul_le_mul' le_rfl he).trans_eq (ENNReal.ofReal_mul hA).symm)
  have hS : mixedNorm volume volume 10 10 r.u ≤ ENNReal.ofReal D := by
    rw [R2Global.joint_value_norm]
    exact (curveS_le_curveX g).trans hx
  have hW := joint_projected_W_le r
  have hZ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U +
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V ≤
        ENNReal.ofReal (2*D) := by
    calc
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal D :=
        add_le_add (hW.1.trans ((curveW_le_curveX g).trans hx))
          (hW.2.trans ((curveW_le_curveX g).trans hx))
      _ = _ := by rw [← ENNReal.ofReal_add hD hD]; congr 1; ring
  have hb := mul_le_mul' (mul_le_mul'
    (ENNReal.rpow_le_rpow hv (by positivity : 0 ≤ 2*α))
    (ENNReal.rpow_le_rpow hS (by norm_num : (0 : ℝ) ≤ 4))) hZ
  have hnum : (C : ℝ≥0∞) *
      (ENNReal.ofReal (A*D) ^ (2*α) * ENNReal.ofReal D ^ (4 : ℝ) *
        ENNReal.ofReal (2*D)) = ENNReal.ofReal ((C' : ℝ)*D^(5+2*α)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hA hD) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hD (by norm_num)]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hA hD]
    have hp : D^(2*α) * D^(4 : ℝ) * D = D^(5+2*α) := by
      conv_lhs => arg 2; rw [← Real.rpow_one D]
      rw [← Real.rpow_add_of_nonneg hD (by positivity) (by norm_num),
        ← Real.rpow_add_of_nonneg hD (by positivity) (by norm_num)]
      congr 1
      ring
    change _ = (2 * (C : ℝ) * A ^ (2*α)) * D ^ (5+2*α)
    calc
      _ = (2*(C : ℝ)*A^(2*α)) * (D^(2*α)*D^(4 : ℝ)*D) := by ring
      _ = _ := by rw [hp]
  refine ⟨hd, ?_⟩
  change vectorForcingNorm (actualGradient α c 0 r.u 0 0 r.U r.V) ≤ _
  have hn' : vectorForcingNorm (actualGradient α c 0 r.u 0 0 r.U r.V) ≤
      (C : ℝ≥0∞) * vectorDifferenceBudget α volume r.u 0 r.U r.V 0 0 := by
    have heq : (fun t => actualFullGradient α c (r.u t) (r.U t) (r.V t) -
        actualFullGradient α c ((0 : ℝ → Space → ℂ) t)
          ((0 : ℝ → Space → Space) t) ((0 : ℝ → Space → Space) t)) =
        actualGradient α c 0 r.u 0 0 r.U r.V := by
      funext t x
      simp only [actualGradient, Pi.sub_apply, Pi.zero_apply, zero_add]
    rw [heq] at hn
    exact hn
  rw [zero_reference_budget hH.order_pos r] at hn'
  exact hn'.trans ((mul_le_mul' le_rfl hb).trans_eq hnum)

/-- Finite triangle is applied to the actual joint candidates, then transported
back to the literal gradients on a finite common good set. -/
theorem source_gradient_sum_le {ι : Type*} [DecidableEq ι]
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {α c : ℝ} (hH : OrdinaryHLS α c) (s : Finset ι)
    (g : ι → ℝ → EnergyState) (hg : ∀ i ∈ s, CurveFinite (g i))
    (r : ∀ i, EnergyJointFields volume (g i)) :
    vectorForcingNorm (fun t x => ∑ i ∈ s, sourceGradient α c (r i) t x) ≤
      ∑ i ∈ s, vectorForcingNorm (sourceGradient α c (r i)) := by
  have hd (i : ι) (hi : i ∈ s) := source_domains hDensity hSob hH (hg i hi) (r i)
  have he : ∀ᵐ t ∂volume,
      (fun x => ∑ i ∈ s, sourceGradient α c (r i) t x) =ᵐ[volume]
      (fun x => ∑ i ∈ s, sourceCandidate α c (r i) t x) := by
    filter_upwards [(eventually_all_finset s).2 (fun i hi => (hd i hi).actual_ae_candidate)]
      with t ht
    filter_upwards [(eventually_all_finset s).2 ht] with x hx
    exact Finset.sum_congr rfl hx
  have hn (i : ι) (hi : i ∈ s) :
      vectorForcingNorm (sourceCandidate α c (r i)) =
        vectorForcingNorm (sourceGradient α c (r i)) :=
    (mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (hd i hi).actual_ae_candidate).symm
  calc
    _ = vectorForcingNorm (fun t x => ∑ i ∈ s, sourceCandidate α c (r i) t x) :=
      mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) he
    _ ≤ ∑ i ∈ s, vectorForcingNorm (sourceCandidate α c (r i)) :=
      mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) _
        (fun i hi => (hd i hi).candidate_joint)
    _ = _ := Finset.sum_congr rfl hn

theorem source_gradient_sum_finite {ι : Type*} [DecidableEq ι]
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {α c : ℝ} (hH : OrdinaryHLS α c) (s : Finset ι)
    (g : ι → ℝ → EnergyState) (hg : ∀ i ∈ s, CurveFinite (g i))
    (r : ∀ i, EnergyJointFields volume (g i)) :
    vectorForcingNorm (fun t x => ∑ i ∈ s, sourceGradient α c (r i) t x) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i hi =>
    (source_domains hDensity hSob hH (hg i hi) (r i)).actual_finite))
    (source_gradient_sum_le hDensity hSob hH s g hg r)

end HartreeF.R2TailForcing
