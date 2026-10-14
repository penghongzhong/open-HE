import UniformIMSRealBounds

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

/-- All six actual homogeneous approximation errors are small. -/
def IMSApproximationSmall (f : HomogeneousData) (n : ℕ) (ε : ℝ) : Prop :=
  (eLpNorm (fun x => core (cutoffAngle n) f.u x - f.u x) 6 volume).toReal < ε ∧
  (eLpNorm (tail (cutoffAngle n) f.u) 6 volume).toReal < ε ∧
  (eLpNorm (fun x => coreGradient (cutoffAngle n) (fun y => (f.u y).re)
    f.realGradient x - f.realGradient x) 2 volume).toReal < ε ∧
  (eLpNorm (fun x => coreGradient (cutoffAngle n) (fun y => (f.u y).im)
    f.imagGradient x - f.imagGradient x) 2 volume).toReal < ε ∧
  (eLpNorm (tailGradient (cutoffAngle n) (fun y => (f.u y).re) f.realGradient) 2 volume).toReal < ε ∧
  (eLpNorm (tailGradient (cutoffAngle n) (fun y => (f.u y).im) f.imagGradient) 2 volume).toReal < ε

/-- Quantitative propagation from true exterior tails to all six IMS approximation errors. -/
theorem ims_small_of_exterior_tails (f : HomogeneousData) (n : ℕ) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hbudget : (1 + imsGradientConstant) * δ < ε)
    (hu : (eLpNorm (exteriorTail n f.u) 6 volume).toReal ≤ δ)
    (hr : (eLpNorm (exteriorTail n f.realGradient) 2 volume).toReal ≤ δ)
    (hi : (eLpNorm (exteriorTail n f.imagGradient) 2 volume).toReal ≤ δ) :
    IMSApproximationSmall f n ε := by
  have hre : MemLp (fun x => (f.u x).re) 6 volume :=
    f.domain.function_L6.continuousLinearMap_comp Complex.reCLM
  have him : MemLp (fun x => (f.u x).im) 6 volume :=
    f.domain.function_L6.continuousLinearMap_comp Complex.imCLM
  have hrb := component_tail_real_le f.domain.function_L6 hre
    (fun x => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (f.u x)) n
  have hib := component_tail_real_le f.domain.function_L6 him
    (fun x => by simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm (f.u x)) n
  have hrδ := mul_le_mul_of_nonneg_left (hrb.trans hu) imsGradientConstant_nonneg
  have hiδ := mul_le_mul_of_nonneg_left (hib.trans hu) imsGradientConstant_nonneg
  have hGr := gradient_real_bounds hre f.domain.real_gradient_L2 n
  have hGi := gradient_real_bounds him f.domain.imag_gradient_L2 n
  have hU := function_real_bounds f.domain.function_L6 n
  have hδeps : δ < ε := by nlinarith [imsGradientConstant_nonneg]
  unfold IMSApproximationSmall
  refine ⟨hU.1.trans_lt (hu.trans_lt hδeps), hU.2.trans_lt (hu.trans_lt hδeps), ?_, ?_, ?_, ?_⟩
  · nlinarith [hGr.1]
  · nlinarith [hGi.1]
  · nlinarith [hGr.2]
  · nlinarith [hGi.2]

/-- Actual IMS convergence is uniform on a compact L6 × L2 × L2 family and a fixed neighborhood.
No uniform convergence or uniform-tail assumption is part of the input. -/
theorem compact_ims_uniform_neighborhood {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, ∀ g : HomogeneousData,
      dist g.lpData f.lpData < δ → IMSApproximationSmall g n ε := by
  let η := ε / (2 * (1 + imsGradientConstant))
  have hden : 0 < 2 * (1 + imsGradientConstant) := by linarith [imsGradientConstant_nonneg]
  have hη : 0 < η := div_pos hε hden
  have hbudget : (1 + imsGradientConstant) * η < ε := by
    dsimp [η]
    have heq : (1 + imsGradientConstant) * (ε / (2 * (1 + imsGradientConstant))) = ε / 2 := by
      field_simp [ne_of_gt (show 0 < 1 + imsGradientConstant by linarith [imsGradientConstant_nonneg])]
    rw [heq]
    linarith
  obtain ⟨N, hN⟩ := compact_homogeneous_uniform_tails hK hη
  refine ⟨η / 4, by positivity, N, ?_⟩
  intro n hn f hf g hgf
  obtain ⟨hu, hr, hi⟩ := hN n hn f hf g hgf
  exact ims_small_of_exterior_tails g n hη.le hbudget hu.le hr.le hi.le

/-- The same common N works at every sufficiently large radius across the entire compact family. -/
theorem compact_ims_uniform {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, IMSApproximationSmall f n ε := by
  obtain ⟨δ, hδ, N, hN⟩ := compact_ims_uniform_neighborhood hK hε
  exact ⟨N, fun n hn f hf => hN n hn f hf f (by simpa using hδ)⟩

#print axioms ims_small_of_exterior_tails
#print axioms compact_ims_uniform_neighborhood
#print axioms compact_ims_uniform
end HartreeF.ComplexIMS
