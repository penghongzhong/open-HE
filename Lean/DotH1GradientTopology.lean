import DotH1Difference

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.DotH1Topology
open SobolevStretch ComplexIMS SharpOrdinary

/-- The actual pair of L2 gradient classes, without the function's L6 class. -/
def gradientData (f : HomogeneousData) :
    Lp Space 2 (volume : Measure Space) × Lp Space 2 (volume : Measure Space) := f.lpData.2

/-- Genuine homogeneous topology induced solely by the two L2 weak gradients.
It is a pseudometric on representatives, as changes on null sets have zero distance. -/
instance gradientPseudoMetricSpace : PseudoMetricSpace HomogeneousData :=
  PseudoMetricSpace.induced gradientData inferInstance

theorem gradient_distance_eq (f g : HomogeneousData) :
    dist f g = max
      (eLpNorm (fun x => f.realGradient x-g.realGradient x) 2 volume).toReal
      (eLpNorm (fun x => f.imagGradient x-g.imagGradient x) 2 volume).toReal := by
  change dist f.lpData.2 g.lpData.2 = _
  rw [Prod.dist_eq]
  simp only [HomogeneousData.lpData, toLp_distance]

theorem function_data_distance_eq (f g : HomogeneousData) :
    dist f.lpData.1 g.lpData.1 = (eLpNorm (fun x => f.u x-g.u x) 6 volume).toReal :=
  toLp_distance f.domain.function_L6 g.domain.function_L6

/-- Ordinary sharp Sobolev controls the actual L6 difference by the gradient-only metric. -/
theorem function_distance_le_gradient_distance (hS : SharpOrdinarySobolev)
    (f g : HomogeneousData) :
    dist f.lpData.1 g.lpData.1 ≤ Real.sqrt (2 * sharpSobolevConstant) * dist f g := by
  rw [function_data_distance_eq, gradient_distance_eq]
  let a := (eLpNorm (fun x => f.realGradient x-g.realGradient x) 2 volume).toReal
  let b := (eLpNorm (fun x => f.imagGradient x-g.imagGradient x) 2 volume).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hd : 0 ≤ max a b := ha.trans (le_max_left _ _)
  have ha2 := pow_le_pow_left₀ ha (le_max_left a b) 2
  have hb2 := pow_le_pow_left₀ hb (le_max_right a b) 2
  have hsa := mul_le_mul_of_nonneg_left ha2 sharpSobolevConstant_pos.le
  have hsb := mul_le_mul_of_nonneg_left hb2 sharpSobolevConstant_pos.le
  have hs := function_difference_sobolev_sq hS f g
  have hbound : (eLpNorm (fun x => f.u x-g.u x) 6 volume).toReal^2 ≤
      (2 * sharpSobolevConstant) * (max a b)^2 := by
    change (eLpNorm (fun x => f.u x-g.u x) 6 volume).toReal^2 ≤
      sharpSobolevConstant * (a^2+b^2) at hs
    nlinarith
  have hroot : 0 ≤ Real.sqrt (2 * sharpSobolevConstant) * max a b :=
    mul_nonneg (Real.sqrt_nonneg _) hd
  have he : (Real.sqrt (2 * sharpSobolevConstant) * max a b)^2 =
      (2 * sharpSobolevConstant) * (max a b)^2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) sharpSobolevConstant_pos.le)]
  rw [← he] at hbound
  exact (sq_le_sq₀ ENNReal.toReal_nonneg hroot).mp hbound

/-- A harmless topology-only constant; no physical threshold is changed. -/
def topologyLipschitzConstant : ℝ := max 1 (Real.sqrt (2 * sharpSobolevConstant))

theorem topologyLipschitzConstant_pos : 0 < topologyLipschitzConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The actual L6 × L2 × L2 realization is Lipschitz in the true gradient-only metric. -/
theorem lpData_distance_le (hS : SharpOrdinarySobolev) (f g : HomogeneousData) :
    dist f.lpData g.lpData ≤ topologyLipschitzConstant * dist f g := by
  rw [Prod.dist_eq]
  apply max_le
  · exact (function_distance_le_gradient_distance hS f g).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  · change dist f g ≤ topologyLipschitzConstant * dist f g
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (show 1 ≤ topologyLipschitzConstant from le_max_left _ _) (dist_nonneg (x := f) (y := g)))

theorem lpData_lipschitz (hS : SharpOrdinarySobolev) :
    LipschitzWith topologyLipschitzConstant.toNNReal HomogeneousData.lpData :=
  LipschitzWith.of_dist_le' (lpData_distance_le hS)

theorem lpData_continuous (hS : SharpOrdinarySobolev) : Continuous HomogeneousData.lpData :=
  (lpData_lipschitz hS).continuous

/-- True gradient-topology compactness produces the stronger compactness required by IMS consumers. -/
theorem isCompact_lpData_image (hS : SharpOrdinarySobolev) {K : Set HomogeneousData}
    (hK : IsCompact K) : IsCompact (HomogeneousData.lpData '' K) :=
  hK.image (lpData_continuous hS)

#print axioms gradient_distance_eq
#print axioms function_data_distance_eq
#print axioms function_distance_le_gradient_distance
#print axioms topologyLipschitzConstant_pos
#print axioms lpData_distance_le
#print axioms lpData_lipschitz
#print axioms lpData_continuous
#print axioms isCompact_lpData_image
end HartreeF.DotH1Topology
