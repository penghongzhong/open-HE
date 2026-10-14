import FLocalL1AffineWeakGradient
import FParabolicJointMeasurability
import FRawL1AffineNormConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffineL1Source
open CriticalAffine AffineMixed RawStabilityInputs TimeHolder SobolevStretch

theorem gradientReal_real_smul (r : ℝ) (g : SourceGradient) :
    gradientReal (r • g)=r • gradientReal g := by
  ext j
  simp [gradientReal]

theorem gradientImag_real_smul (r : ℝ) (g : SourceGradient) :
    gradientImag (r • g)=r • gradientImag g := by
  ext j
  simp [gradientImag]

/-- Transport all actual raw-source fields. The original complex Euclidean G
is used verbatim; no real-plus-imaginary norm replacement occurs. -/
theorem rawSource_parabolic {I : Set ℝ} {e : ℝ → Space → ℂ}
    {G : ℝ → Space → SourceGradient} (h : RawSpatialGradientSource I e G)
    {a : ℝ} (ha : 0<a) (b : Space) (c : ℝ) :
    RawSpatialGradientSource ((timeAffine a c) ⁻¹' I)
      (parabolicField a b c (5/2) e) (parabolicField a b c (7/2) G) where
  value_joint := parabolicField_jointly_measurable ha b c (5/2) I e h.value_joint
  gradient_joint := parabolicField_jointly_measurable ha b c (7/2) I G h.gradient_joint
  value_local := by
    intro A B hAB hI
    have hmap : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I := by
      intro s hs
      let t := (timeAffineHomeomorph ha c).symm s
      have ht : timeAffine a c t=s := (timeAffineHomeomorph ha c).apply_symm_apply s
      have hmem : t ∈ Icc A B := by
        rw [← timeAffine_preimage_Icc ha c A B]
        change timeAffine a c t ∈ Icc (timeAffine a c A) (timeAffine a c B)
        rwa [ht]
      have hx := hI hmem
      change timeAffine a c t ∈ I at hx
      rwa [ht] at hx
    exact (raw_source_local_scaled_norms h ha b c A B hAB hmap).2.2.1
  gradient_finite := by
    rw [parabolic_N_invariant ha b c I G h.gradient_joint]
    exact h.gradient_finite
  weak_gradient := by
    filter_upwards [(timeAffine_quasiMeasurePreserving ha c I).ae h.weak_gradient] with t ht
    have hk : a^(5/2:ℝ)*a=a^(7/2:ℝ) := by
      calc
        _ = a^(5/2:ℝ)*a^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ha]; norm_num
    have hr := hasWeakGradient_affine_local ht.1 ha b (a^(5/2:ℝ))
    have hi := hasWeakGradient_affine_local ht.2 ha b (a^(5/2:ℝ))
    have hfr : (fun x => (parabolicField a b c (5/2) e t x).re)=
        (fun x => a^(5/2:ℝ)*(e (timeAffine a c t) (affine a b x)).re) := by
      funext x
      simp only [parabolicField,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
    have hfi : (fun x => (parabolicField a b c (5/2) e t x).im)=
        (fun x => a^(5/2:ℝ)*(e (timeAffine a c t) (affine a b x)).im) := by
      funext x
      simp only [parabolicField,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,add_zero]
    have hgr : (fun x => gradientReal (parabolicField a b c (7/2) G t x))=
        (fun x => a^(7/2:ℝ) • gradientReal (G (timeAffine a c t) (affine a b x))) := by
      funext x
      exact gradientReal_real_smul _ _
    have hgi : (fun x => gradientImag (parabolicField a b c (7/2) G t x))=
        (fun x => a^(7/2:ℝ) • gradientImag (G (timeAffine a c t) (affine a b x))) := by
      funext x
      exact gradientImag_real_smul _ _
    constructor
    · rw [hfr,hgr]
      simpa only [hk] using hr
    · rw [hfi,hgi]
      simpa only [hk] using hi

#print axioms gradientReal_real_smul
#print axioms gradientImag_real_smul
#print axioms rawSource_parabolic
end HartreeF.AffineL1Source
