import FBanachWeakDerivativeHelpers

open Set Function MeasureTheory
open scoped Topology ContDiff

namespace BanachWeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous Banach-valued function with vanishing weak derivative is
constant on its open interval. All tests are smooth and compactly supported
inside the interval. -/
theorem eq_const_of_zero_weak_derivative
    {a b : ℝ} (hab : a < b) {h : ℝ → E}
    (hh : ContinuousOn h (Ioo a b))
    (hzero : ∀ η : ℝ → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo a b →
      (∫ x, deriv η x • h x) = 0) :
    ∃ C : E, EqOn h (fun _ ↦ C) (Ioo a b) := by
  let β : ContDiffBump ((a + b) / 2) := {
    rIn := (b - a) / 8
    rOut := (b - a) / 4
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  let ρ : ℝ → ℝ := β.normed volume
  have hρ : ContDiff ℝ ∞ ρ := β.contDiff_normed
  have hρc : HasCompactSupport ρ := β.hasCompactSupport_normed
  have hρint : (∫ x, ρ x) = 1 := β.integral_normed
  have hρS : tsupport ρ ⊆ Ioo a b := by
    rw [show tsupport ρ = Metric.closedBall ((a + b) / 2) ((b - a) / 4) from
      β.tsupport_normed_eq, Real.closedBall_eq_Icc]
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  let C : E := ∫ x, ρ x • h x
  have htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, φ x • (h x - C)) = 0 := by
    intro φ hφ hφc hφS
    let k : ℝ := ∫ x, φ x
    let q : ℝ → ℝ := fun x ↦ φ x - k • ρ x
    have hq : ContDiff ℝ ∞ q := hφ.sub (hρ.const_smul k)
    have hkρc : HasCompactSupport (fun x ↦ k • ρ x) :=
      HasCompactSupport.smul_left (f := fun _ : ℝ ↦ k) hρc
    have hqc : HasCompactSupport q := hφc.sub hkρc
    have hqS : tsupport q ⊆ Ioo a b :=
      (tsupport_sub φ (fun x ↦ k • ρ x)).trans
        (union_subset hφS ((tsupport_smul_subset_right (fun _ ↦ k) ρ).trans hρS))
    have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
    have hqint : (∫ x, q x) = 0 := by
      change (∫ x, φ x - k • ρ x) = 0
      have hkρi : Integrable (fun x ↦ k • ρ x) := hρi.smul k
      rw [integral_sub hφi hkρi, integral_smul, hρint]
      simp [k]
    obtain ⟨ψ, hψ, hψc, hψS, hψderiv⟩ :=
      exists_compact_test_primitive hq hqc hqS hqint
    have hqzero : (∫ x, q x • h x) = 0 := by
      have hd : deriv ψ = q := funext fun x ↦ (hψderiv x).deriv
      simpa only [hd] using hzero ψ hψ hψc hψS
    have hφhi : Integrable (fun x ↦ φ x • h x) :=
      integrable_test_smul hh hφ.continuous hφc hφS
    have hρhi : Integrable (fun x ↦ ρ x • h x) :=
      integrable_test_smul hh hρ.continuous hρc hρS
    have hmom : (∫ x, φ x • h x) = k • C := by
      have hrew : (∫ x, q x • h x) = (∫ x, φ x • h x) - k • C := by
        simp only [q, sub_smul, smul_assoc]
        have hkρhi : Integrable (fun x ↦ k • (ρ x • h x)) := hρhi.smul k
        rw [integral_sub hφhi hkρhi, integral_smul]
      rw [hrew] at hqzero
      exact sub_eq_zero.mp hqzero
    simp only [smul_sub]
    rw [integral_sub hφhi (hφi.smul_const C), integral_smul_const, hmom]
    exact sub_self _
  have hae : ∀ᵐ x, x ∈ Ioo a b → h x - C = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hh.sub continuousOn_const).locallyIntegrableOn measurableSet_Ioo) htest
  have hae' : (fun x ↦ h x - C) =ᵐ[volume.restrict (Ioo a b)] (fun _ ↦ 0) :=
    (ae_restrict_iff' measurableSet_Ioo).2 hae
  have hpoint : EqOn (fun x ↦ h x - C) (fun _ ↦ 0) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo
      (hh.sub continuousOn_const) continuousOn_const
  exact ⟨C, fun x hx ↦ sub_eq_zero.mp (hpoint hx)⟩

end BanachWeakDerivative
