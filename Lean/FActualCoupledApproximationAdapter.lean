import FActualApproximationBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing EnergySpace SobolevStretch
  CriticalTimeSobolev CutoffApproximation
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- The scalar compact data for all three coordinates come from one actual coupled
value and weak-gradient family, with one common approximation index and finite bound. -/
theorem exists_actual_coupled_scalar_compact_approximation {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (hE : curveEnergy g ≠ ∞)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (r : EnergyJointFields volume g) :
    ∃ (uN : ℕ → ℝ → Space → ℂ) (RN IN : ℕ → ℝ → Space → Space),
      (∀ n t, InDotH1 (uN n t) (RN n t) (IN n t)) ∧
      ∀ j : Fin 3, ∃ A : ScalarCompactApproximation r.u
        (gradientCoordinate j (fun t => complexGradient (r.U t) (r.V t))),
        A.value = uN ∧
        A.gradient = (fun n => gradientCoordinate j (fun t => complexGradient (RN n t) (IN n t))) := by
  choose uN RN IN hc hp hk hkp hd hs hw he using
    (fun n : ℕ => exists_actual_profile_compact_approximation hSob g hg hE hS hW
      (smoothingPrecision n) (smoothingPrecision_pos n))
  let G : ℝ → Space → CGradient := fun t => complexGradient (r.U t) (r.V t)
  let GN : ℕ → ℝ → Space → CGradient := fun n t => complexGradient (RN n t) (IN n t)
  have hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) :=
    packedGradient_joint_stronglyMeasurable r.joint_U r.joint_V
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rw [jointFields_value_mixedNorm g r]
    exact hS
  have hWr : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) G ≠ ∞ := by
    rw [show G = (fun t => complexGradient (r.U t) (r.V t)) from rfl,
      jointFields_packed_mixedNorm g r]
    exact hW
  have hsR (n : ℕ) : mixedNorm volume volume 10 10
      (fun t x => uN n t x - r.u t x) ≤ smoothingPrecision n := by
    rw [← error_to_stateValue_eq_joint g r]
    exact (hs n).le
  have hwR (n : ℕ) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => GN n t x - G t x) ≤ smoothingPrecision n := by
    change mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => GN n t x - complexGradient (r.U t) (r.V t) x) ≤ _
    rw [← error_to_stateGradient_eq_joint g r]
    exact (hw n).le
  let C : ℝ≥0∞ := ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))
  let M0 : ℝ≥0∞ := C * curveEnergy g
  let M1 : ℝ≥0∞ := C * ((1 + (cutoffGradientBound : ℝ≥0∞) * C) * curveEnergy g)
  let M2 : ℝ≥0∞ := 1 + mixedNorm volume volume 10 10 r.u
  let M3 : ℝ≥0∞ := 1 + mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) G
  have hM0 : M0 ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE
  have hM1 : M1 ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨by norm_num,
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top⟩) hE)
  have hM2 : M2 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hSr⟩
  have hM3 : M3 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hWr⟩
  let B : ℝ≥0∞ := max M0 (max M1 (max M2 M3))
  have hBfin : B ≠ ∞ := ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hM0)
    (max_lt (lt_top_iff_ne_top.mpr hM1)
      (max_lt (lt_top_iff_ne_top.mpr hM2) (lt_top_iff_ne_top.mpr hM3))))
  let b : ℝ≥0 := B.toNNReal
  have hb : (b : ℝ≥0∞) = B := ENNReal.coe_toNNReal hBfin
  have h0 : M0 ≤ (b : ℝ≥0∞) := by rw [hb]; exact le_max_left _ _
  have h1 : M1 ≤ (b : ℝ≥0∞) := by
    rw [hb]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have h2 : M2 ≤ (b : ℝ≥0∞) := by
    rw [hb]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h3 : M3 ≤ (b : ℝ≥0∞) := by
    rw [hb]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hV : mixedNorm volume volume ∞ 6 r.u ≤ (b : ℝ≥0∞) :=
    (jointFields_value_sobolev_bound hSob g r).trans h0
  have hSbound : mixedNorm volume volume 10 10 r.u ≤ (b : ℝ≥0∞) :=
    (le_add_self : mixedNorm volume volume 10 10 r.u ≤ M2).trans h2
  have hVN (n : ℕ) : mixedNorm volume volume ∞ 6 (uN n) ≤ (b : ℝ≥0∞) := by
    exact ((coupled_value_mixed_le hSob (uN n) (RN n) (IN n)
      (hc n).aestronglyMeasurable (ae_of_all _ (hd n))).trans
      (mul_le_mul' le_rfl (he n))).trans h1
  have hSN (n : ℕ) : mixedNorm volume volume 10 10 (uN n) ≤ (b : ℝ≥0∞) := by
    exact ((mixedNorm_le_error_add (by norm_num : (1 : ℝ≥0∞) ≤ 10)
      (by norm_num) (by norm_num) (uN n) r.u
      (hc n).aestronglyMeasurable r.joint_u.aestronglyMeasurable).trans
      (add_le_add ((hsR n).trans (smoothingPrecision_le_one n)) le_rfl)).trans h2
  have hWN (n : ℕ) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (GN n) ≤ (b : ℝ≥0∞) := by
    exact ((mixedNorm_le_error_add (by norm_num : (1 : ℝ≥0∞) ≤ 10)
      (by norm_num) ENNReal.ofReal_ne_top (GN n) G
      (hp n).aestronglyMeasurable hG.aestronglyMeasurable).trans
      (add_le_add ((hwR n).trans (smoothingPrecision_le_one n)) le_rfl)).trans h3
  refine ⟨uN, RN, IN, hd, ?_⟩
  intro j
  have hjN (n : ℕ) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (gradientCoordinate j (GN n)) ≤ (b : ℝ≥0∞) :=
    (gradientCoordinate_mixed_le (by norm_num) ENNReal.ofReal_ne_top j (GN n)
      (hp n).aestronglyMeasurable).trans (hWN n)
  refine ⟨{
    value := uN
    gradient := fun n => gradientCoordinate j (GN n)
    profile := ⟨r.joint_u, gradientCoordinate_joint_stronglyMeasurable j G hG,
      ne_top_of_le_ne_top ENNReal.coe_ne_top hV, hSr,
      ne_top_of_le_ne_top hWr (gradientCoordinate_mixed_le (by norm_num)
        ENNReal.ofReal_ne_top j G hG.aestronglyMeasurable)⟩
    approximate_profile := fun n => ⟨(hc n).stronglyMeasurable,
      (gradientCoordinate_continuous j (GN n) (hp n)).stronglyMeasurable,
      ne_top_of_le_ne_top ENNReal.coe_ne_top (hVN n),
      ne_top_of_le_ne_top ENNReal.coe_ne_top (hSN n),
      ne_top_of_le_ne_top ENNReal.coe_ne_top (hjN n)⟩
    value_continuous := hc
    gradient_continuous := fun n => gradientCoordinate_continuous j (GN n) (hp n)
    value_compact := hk
    gradient_compact := fun n => gradientCoordinate_compact j (GN n) (hkp n)
    bound := b
    value_V_bound := hV
    value_S_bound := hSbound
    approximate_V_bound := hVN
    approximate_S_bound := hSN
    approximate_W_bound := hjN
    value_error := ?_
    gradient_error := ?_
  }, rfl, rfl⟩
  · intro n
    rw [mixedNorm_sub_comm]
    exact hsR n
  · intro n
    exact (gradientCoordinate_error_mixed_le (by norm_num) ENNReal.ofReal_ne_top j G (GN n)
      hG.aestronglyMeasurable (hp n).aestronglyMeasurable).trans (by
        rw [mixedNorm_sub_comm]
        exact hwR n)

#print axioms exists_actual_coupled_scalar_compact_approximation
end HartreeF.GeneralProfileCross
