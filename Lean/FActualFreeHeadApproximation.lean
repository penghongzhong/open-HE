import FCompactFreeHeadSlots
import FActualCoupledApproximationAdapter
import FLocalProductContinuity

/-!
Actual finite-E/S/packed-W coefficient closure. Only the VALUE approximants of
the existing actual coupled construction are used. The direction h_n is unchanged.
Every new declaration is an author-source draft, UNCOMPILED.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeHeadSlots
open TimeHolder ProfileApproximation GeneralProfileCross CompactCross
  CrossContinuity LocalProfileProducts ProfileSpatialSmoothing
  FiniteProfileCrossDomains EnergySpace SobolevStretch CriticalTimeSobolev ForcingDomain

/-- A ScalarProfile records genuine domains, without identifying its direction
with the derivative of its value. This constructor keeps the given h unchanged. -/
theorem value_approximation_direction_profile {u G : ℝ → Space → ℂ}
    (A : ScalarCompactApproximation u G) {h : ℝ → Space → ℂ}
    (hh : StronglyMeasurable (Function.uncurry h))
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h ≠ ∞) :
    ScalarProfile u h ∧ ∀ m, ScalarProfile (A.value m) h := by
  exact ⟨⟨A.profile.value_joint,hh,A.profile.value_V,A.profile.value_S,hW⟩,
    fun m => ⟨(A.approximate_profile m).value_joint,hh,
      (A.approximate_profile m).value_V,(A.approximate_profile m).value_S,hW⟩⟩

/-- The fixed finite cap includes exactly four value terms and two direction
terms, independent of the approximation index AND the original sequence index. -/
def approximationCap (b bW : ℝ≥0) : ℝ≥0 := 4*b+2*bW

def approximationError (m : ℕ) : ℝ≥0 := 2*(smoothingPrecision m).toNNReal

theorem approximationError_coe (m : ℕ) :
    (approximationError m : ℝ≥0∞) = smoothingPrecision m+smoothingPrecision m := by
  change ((2 : ℝ≥0) * (smoothingPrecision m).toNNReal : ℝ≥0∞) = _
  rw [ENNReal.coe_toNNReal (show smoothingPrecision m ≠ ∞ from ENNReal.ofReal_ne_top)]
  norm_num only [ENNReal.coe_ofNat, two_mul]

/-- Same-direction continuity, with explicit NNReal cap/error conversions. -/
theorem same_direction_approximation_error {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u G : ℝ → Space → ℂ} (A : ScalarCompactApproximation u G)
    {h : ℕ → ℝ → Space → ℂ}
    (hh : ∀ n, StronglyMeasurable (Function.uncurry (h n)))
    (bW : ℝ≥0)
    (hW : ∀ n, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n) ≤ bW) :
    ∃ C : ℝ≥0, ∀ m n,
      forcingNorm (innerCross α c u (h n) u-innerCross α c (A.value m) (h n) (A.value m)) ≤
        (C : ℝ≥0∞) * boundedModulus α (approximationCap A.bound bW) (approximationError m) ∧
      forcingNorm (outerCross α c u u (h n)-outerCross α c (A.value m) (A.value m) (h n)) ≤
        (C : ℝ≥0∞) * boundedModulus α (approximationCap A.bound bW) (approximationError m) := by
  obtain ⟨C,hC⟩ := separate_cross_bounded_continuity hHLS
  refine ⟨C,?_⟩
  intro m n
  have hWfin := ne_top_of_le_ne_top ENNReal.coe_ne_top (hW n)
  obtain ⟨P,PN⟩ := value_approximation_direction_profile A (hh n) hWfin
  have hJ := P.jointInputs (PN m) P (PN m)
  have hs := P.sliceInputs (PN m) P (PN m)
  have hM : (approximationCap A.bound bW : ℝ≥0∞) = 4*(A.bound : ℝ≥0∞)+2*(bW : ℝ≥0∞) := by
    simp only [approximationCap, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat]
  have hV : valueSize ∞ 6 u (A.value m) u (A.value m) ≤ approximationCap A.bound bW := by
    rw [hM]
    calc
      _ ≤ ((A.bound : ℝ≥0∞)+A.bound)+(A.bound+A.bound) :=
        add_le_add (add_le_add A.value_V_bound (A.approximate_V_bound m))
          (add_le_add A.value_V_bound (A.approximate_V_bound m))
      _ = 4*(A.bound : ℝ≥0∞) := by ring
      _ ≤ _ := le_add_right le_rfl
  have hS : valueSize 10 10 u (A.value m) u (A.value m) ≤ approximationCap A.bound bW := by
    rw [hM]
    calc
      _ ≤ ((A.bound : ℝ≥0∞)+A.bound)+(A.bound+A.bound) :=
        add_le_add (add_le_add A.value_S_bound (A.approximate_S_bound m))
          (add_le_add A.value_S_bound (A.approximate_S_bound m))
      _ = 4*(A.bound : ℝ≥0∞) := by ring
      _ ≤ _ := le_add_right le_rfl
  have hD : referenceSize (h n) (h n) ≤ approximationCap A.bound bW := by
    rw [hM]
    calc
      _ ≤ (bW : ℝ≥0∞)+bW := add_le_add (hW n) (hW n)
      _ = 2*(bW : ℝ≥0∞) := by ring
      _ ≤ _ := le_add_left le_rfl
  have he : changeSize 10 10 u (A.value m) u (A.value m) ≤ approximationError m := by
    rw [approximationError_coe]
    exact add_le_add (A.value_error m) (A.value_error m)
  have hz : changeSize 10 (ENNReal.ofReal (30/13 : ℝ)) (h n) (h n) (h n) (h n) ≤
      approximationError m := by simp [changeSize, mixedNorm]
  have hb := hC u (A.value m) (h n) (h n) u (A.value m) (h n) (h n)
    hJ hs (approximationCap A.bound bW) (approximationError m) hV hS hD he hz
  exact ⟨hb.2.2.1,hb.2.2.2⟩

/-- Full ordinary-filter closure for a supplied ACTUAL coupled approximation.
This is an internal adapter; it neither assumes nor asserts a new density theorem
for every arbitrary measurable V-intersection-S coefficient. -/
theorem value_approximation_free_head_zero {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u G : ℝ → Space → ℂ} (A : ScalarCompactApproximation u G)
    {h : ℕ → ℝ → Space → ℂ}
    (hh : ∀ n, StronglyMeasurable (Function.uncurry (h n)))
    (bE bW : ℝ≥0)
    (hE : ∀ n, mixedNorm volume volume ∞ 2 (h n) ≤ bE)
    (hW : ∀ n, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n) ≤ bW)
    (hlf : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R → ∀ n, cylinderL2 T R z (h n) ≠ ∞)
    (hl0 : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R →
      Tendsto (fun n => cylinderL2 T R z (h n)) atTop (𝓝 0)) :
    (∀ n, SignedFibreDomains α c u (h n) ∧
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u (h n) ≠ ∞ ∧
      forcingNorm (innerCross α c u (h n) u) ≠ ∞ ∧
      forcingNorm (outerCross α c u u (h n)) ≠ ∞) ∧
    Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u (h n)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (innerCross α c u (h n) u)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (outerCross α c u u (h n))) atTop (𝓝 0) := by
  have hWfin (n : ℕ) := ne_top_of_le_ne_top ENNReal.coe_ne_top (hW n)
  have hP (n : ℕ) : ScalarProfile u (h n) :=
    (value_approximation_direction_profile A (hh n) (hWfin n)).1
  have hPN (m n : ℕ) : ScalarProfile (A.value m) (h n) :=
    (value_approximation_direction_profile A (hh n) (hWfin n)).2 m
  have hc (m : ℕ) := compact_free_head_zero hHLS
    (A.value_continuous m) (A.value_compact m) hh bE hE hlf hl0
  obtain ⟨C,hC⟩ := same_direction_approximation_error hHLS A hh bW hW
  let err : ℕ → ℝ≥0∞ := fun m => (C : ℝ≥0∞) *
    boundedModulus α (approximationCap A.bound bW) (approximationError m)
  have he : Tendsto err atTop (𝓝 0) := by
    have hd : Tendsto (fun m => (approximationError m : ℝ≥0∞)) atTop (𝓝 0) := by
      simp_rw [approximationError_coe]
      simpa only [zero_add] using smoothingPrecision_tendsto.add smoothingPrecision_tendsto
    have hm := (boundedModulus_tendsto_zero hHLS.order_pos hHLS.order_lt_three
      (approximationCap A.bound bW)).comp hd
    simpa only [err, Function.comp_apply, mul_zero] using
      ENNReal.Tendsto.const_mul hm (a := (C : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
  have heQ : Tendsto (fun m => smoothingPrecision m * (bW : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const smoothingPrecision_tendsto (b := (bW : ℝ≥0∞))
        (Or.inr ENNReal.coe_ne_top)
  refine ⟨?_,?_,?_,?_⟩
  · intro n
    have hs := scalar_cross_finite hHLS (hP n) (hP n)
    have hQ := Q_le u (h n) A.profile.value_joint.aestronglyMeasurable
      (hh n).aestronglyMeasurable A.profile.value_S (hWfin n)
    exact ⟨scalar_signed_fibre_domains hHLS (hP n),
      ne_top_of_le_ne_top (ENNReal.mul_ne_top A.profile.value_S (hWfin n)) hQ,hs.1,hs.2⟩
  · apply tendsto_zero_of_uniform_approximation heQ (fun m => (hc m).2.1)
    intro m n
    have hdu : mixedNorm volume volume 10 10 (fun t x => u t x-A.value m t x) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (A.value_error m)
    have hdz : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t x => h n t x-h n t x) ≠ ∞ := by simp [mixedNorm]
    let := value_gradient_product_holder
    have hd := normProduct_difference_mixed_le
      (p := 10) (q := ENNReal.ofReal (30/13 : ℝ)) (r := ENNReal.ofReal (15/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) ENNReal.ofReal_ne_top (by norm_num) ENNReal.ofReal_ne_top
      u (A.value m) (h n) (h n) A.profile.value_joint.aestronglyMeasurable
      (A.approximate_profile m).value_joint.aestronglyMeasurable
      (hh n).aestronglyMeasurable (hh n).aestronglyMeasurable
      hdu (hWfin n) (A.approximate_profile m).value_S hdz
    have hd' : mixedNorm volume volume 5 (ENNReal.ofReal (15/8 : ℝ))
        (fun t x => normProduct u (h n) t x-normProduct (A.value m) (h n) t x) ≤
          smoothingPrecision m * (bW : ℝ≥0∞) := by
      simpa only [sub_self, mixedNorm, eLpNorm_fun_zero, mul_zero, add_zero] using
        hd.trans (add_le_add (mul_le_mul' (A.value_error m) (hW n)) le_rfl)
    exact (localProductNorm_le_error_add (by norm_num) ENNReal.ofReal_ne_top
      u (A.value m) (h n) (h n) A.profile.value_joint.aestronglyMeasurable
      (A.approximate_profile m).value_joint.aestronglyMeasurable
      (hh n).aestronglyMeasurable (hh n).aestronglyMeasurable).trans (add_le_add hd' le_rfl)
  · apply tendsto_zero_of_uniform_approximation he (fun m => (hc m).2.2.1)
    intro m n
    exact (forcingNorm_le_difference_add _ _
      (inner_joint_measurable α c (hP n).value_joint.aestronglyMeasurable
        (hh n).aestronglyMeasurable (hP n).value_joint.aestronglyMeasurable)
      (inner_joint_measurable α c (hPN m n).value_joint.aestronglyMeasurable
        (hh n).aestronglyMeasurable (hPN m n).value_joint.aestronglyMeasurable)).trans
      (add_le_add (hC m n).1 le_rfl)
  · apply tendsto_zero_of_uniform_approximation he (fun m => (hc m).2.2.2)
    intro m n
    exact (forcingNorm_le_difference_add _ _
      (outer_joint_measurable α c (hP n).value_joint.aestronglyMeasurable
        (hP n).value_joint.aestronglyMeasurable (hh n).aestronglyMeasurable)
      (outer_joint_measurable α c (hPN m n).value_joint.aestronglyMeasurable
        (hPN m n).value_joint.aestronglyMeasurable (hh n).aestronglyMeasurable)).trans
      (add_le_add (hC m n).2 le_rfl)

/-- Actual rough-profile endpoint. The existing coupled approximation is
constructed for this continuous EnergyState curve and this SAME representative.
Only its value family is extracted; h_n is kept unchanged throughout. -/
theorem actual_free_head_slots {α c K : ℝ} (hHLS : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (hgE : curveEnergy g ≠ ∞)
    (hgS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hgW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (r : EnergyJointFields volume g)
    {h : ℕ → ℝ → Space → ℂ}
    (hh : ∀ n, StronglyMeasurable (Function.uncurry (h n)))
    (bE bW : ℝ≥0)
    (hE : ∀ n, mixedNorm volume volume ∞ 2 (h n) ≤ bE)
    (hW : ∀ n, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n) ≤ bW)
    (hlf : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R → ∀ n, cylinderL2 T R z (h n) ≠ ∞)
    (hl0 : ∀ (T R : ℝ) (z : Space), 0 < T → 0 < R →
      Tendsto (fun n => cylinderL2 T R z (h n)) atTop (𝓝 0)) :
    (∀ n, SignedFibreDomains α c r.u (h n) ∧
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) r.u (h n) ≠ ∞ ∧
      forcingNorm (innerCross α c r.u (h n) r.u) ≠ ∞ ∧
      forcingNorm (outerCross α c r.u r.u (h n)) ≠ ∞) ∧
    Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) r.u (h n)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (innerCross α c r.u (h n) r.u)) atTop (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (outerCross α c r.u r.u (h n))) atTop (𝓝 0) := by
  obtain ⟨uN,RN,IN,_hcoupled,hcoords⟩ :=
    exists_actual_coupled_scalar_compact_approximation hSob g hg hgE hgS hgW r
  obtain ⟨A,_hvalue,_hgradient⟩ := hcoords (0 : Fin 3)
  exact value_approximation_free_head_zero hHLS A hh bE bW hE hW hlf hl0

end HartreeF.FreeHeadSlots
