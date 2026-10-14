import RieszLaplaceProfile
import RieszGaussianParameters
import GaussianProfileConvolution

/-! Absolute physical Gaussian-rate triple domain for the literal Q potential.
The scalar parameter L1 domain is produced independently before spatial Fubini.
The Riesz rate is evaluated only off the fixed-centre null singleton. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz Bubble

def bubbleTripleCoefficient (α : ℝ) : ℝ :=
  Real.pi^(3/2:ℝ)/(rieszWeightDenom α * Real.Gamma ((3+α)/2))

/-- Tuple order is ((s,r),y): bubble rate, Riesz rate, physical point. -/
def bubbleRateTriple (α : ℝ) (x : Space) (p : (ℝ × ℝ) × Space) : ℝ :=
  rieszLaplace α (x-p.2) p.1.2 * gammaProfile ((3+α)/2) p.2 p.1.1

theorem bubbleTripleCoefficient_pos {α : ℝ} (hα : 0<α) : 0<bubbleTripleCoefficient α := by
  have hb := Real.Gamma_pos_of_pos (show 0<(3+α)/2 by linarith)
  have hd := rieszWeightDenom_pos hα
  unfold bubbleTripleCoefficient
  positivity

theorem bubbleRateTriple_factor (α : ℝ) (x : Space) (s r : ℝ) (y : Space) :
    bubbleRateTriple α x ((s,r),y) =
      (r^((3-α)/2-1)*s^((3+α)/2-1)*Real.exp (-s)/
        (rieszWeightDenom α * Real.Gamma ((3+α)/2))) * gaussianProduct r s x y := by
  unfold bubbleRateTriple
  rw [rieszLaplace_factor, gammaProfile_factor]
  unfold gaussianProduct
  ring

theorem bubbleRateTriple_spatial_integrable (α : ℝ) (x : Space)
    {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    Integrable (fun y : Space => bubbleRateTriple α x ((s,r),y)) volume := by
  simp_rw [bubbleRateTriple_factor]
  exact (gaussianProduct_integrable hr hs x).const_mul _

theorem bubbleRateTriple_spatial_integral (α : ℝ) (x : Space)
    {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (∫ y : Space, bubbleRateTriple α x ((s,r),y)) =
      bubbleTripleCoefficient α * parameterKernel ((3-α)/2) (‖x‖^2) (s,r) := by
  have hrs : 0<r+s := add_pos hr hs
  have hg : (Real.pi/(r+s))^(3/2:ℝ) = Real.pi^(3/2:ℝ)*(r+s)^(-(3/2:ℝ)) := by
    rw [Real.div_rpow Real.pi_pos.le hrs.le, Real.rpow_neg hrs.le]
    rfl
  simp_rw [bubbleRateTriple_factor]
  rw [integral_const_mul, gaussianProduct_integral hr hs x, hg]
  unfold bubbleTripleCoefficient parameterKernel
  dsimp only
  rw [show (3+α)/2-1 = 2-(3-α)/2 by ring]
  ring

theorem bubbleRateTriple_nonneg {α : ℝ} (hα : 0<α) (x y : Space)
    {s r : ℝ} (hs : 0<s) (hr : 0<r) : 0≤bubbleRateTriple α x ((s,r),y) :=
  mul_nonneg (rieszLaplace_nonneg hα (x-y) hr)
    (gammaProfile_nonneg (show 0<(3+α)/2 by linarith) y hs)

theorem bubbleRateTriple_measurable (α : ℝ) (x : Space) :
    AEStronglyMeasurable (bubbleRateTriple α x)
      ((positiveTimeMeasure.prod positiveTimeMeasure).prod volume) := by
  apply Measurable.aestronglyMeasurable
  unfold bubbleRateTriple rieszLaplace gammaProfile
  fun_prop

/-- Original positive rate-pair domain plus actual Gaussian convolution yields
joint absolute space-and-rate integrability for every fixed physical x. -/
theorem bubbleRateTriple_integrable {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    Integrable (bubbleRateTriple α x)
      ((positiveTimeMeasure.prod positiveTimeMeasure).prod volume) := by
  apply (integrable_prod_iff (bubbleRateTriple_measurable α x)).mpr
  constructor
  · filter_upwards [positiveTimePair_ae] with q hq
    exact bubbleRateTriple_spatial_integrable α x hq.1 hq.2
  · have hk := parameterKernel_integrable (show 0<(3-α)/2 by linarith)
      (show (3-α)/2<3/2 by linarith) (sq_nonneg ‖x‖)
    apply (hk.const_mul (bubbleTripleCoefficient α)).congr
    filter_upwards [positiveTimePair_ae] with q hq
    rw [← bubbleRateTriple_spatial_integral α x hq.1 hq.2]
    apply integral_congr_ae
    filter_upwards [] with y
    exact (Real.norm_of_nonneg (bubbleRateTriple_nonneg hα x y hq.1 hq.2)).symm

theorem bubbleRateTriple_time_integrable {α : ℝ} (hα : 0<α) (hα3 : α<3)
    (x y : Space) (hxy : x-y≠0) :
    Integrable (fun q : ℝ × ℝ => bubbleRateTriple α x (q,y))
      (positiveTimeMeasure.prod positiveTimeMeasure) := by
  apply ((gammaProfile_time_integrable (show 0<(3+α)/2 by linarith) y).mul_prod
    (rieszLaplace_integrable_nonzero hα3 hxy)).congr
  filter_upwards [] with q
  unfold bubbleRateTriple
  ring

theorem bubbleRateTriple_time_integral {α : ℝ} (hα : 0<α) (hα3 : α<3)
    (x y : Space) (hxy : x-y≠0) :
    (∫ q : ℝ × ℝ, bubbleRateTriple α x (q,y) ∂positiveTimeMeasure.prod positiveTimeMeasure) =
      rieszKernel α (standardRieszConstant α) (x-y) * powerDensity α bubbleC y := by
  have he : (fun q : ℝ × ℝ => bubbleRateTriple α x (q,y)) =
      (fun q => gammaProfile ((3+α)/2) y q.1 * rieszLaplace α (x-y) q.2) := by
    funext q
    unfold bubbleRateTriple
    ring
  rw [he, integral_prod_mul, bubbleDensity_gamma_integral hα y,
    rieszLaplace_integral_nonzero hα3 hxy]
  ring

/-- The actual singular physical convolution fiber is L1 at every x.
The zero separation is excluded only on its proved null singleton. -/
theorem bubble_potential_integrable {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    Integrable (fun y => rieszKernel α (standardRieszConstant α) (x-y)*powerDensity α bubbleC y)
      volume := by
  apply (bubbleRateTriple_integrable hα hα3 x).integral_prod_right.congr
  filter_upwards [fixed_difference_ne_zero_ae x] with y hy
  exact bubbleRateTriple_time_integral hα hα3 x y hy

theorem bubble_potential_parameter_identity {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    potential α (standardRieszConstant α) bubbleC x = bubbleTripleCoefficient α *
      ∫ q : ℝ × ℝ, parameterKernel ((3-α)/2) (‖x‖^2) q
        ∂positiveTimeMeasure.prod positiveTimeMeasure := by
  have hp := bubbleRateTriple_integrable hα hα3 x
  calc
    _ = ∫ y : Space, (∫ q : ℝ × ℝ, bubbleRateTriple α x (q,y)
        ∂positiveTimeMeasure.prod positiveTimeMeasure) := by
      apply integral_congr_ae
      filter_upwards [fixed_difference_ne_zero_ae x] with y hy
      exact (bubbleRateTriple_time_integral hα hα3 x y hy).symm
    _ = ∫ p : (ℝ × ℝ) × Space, bubbleRateTriple α x p
        ∂(positiveTimeMeasure.prod positiveTimeMeasure).prod volume := (integral_prod_symm _ hp).symm
    _ = ∫ q : ℝ × ℝ, (∫ y : Space, bubbleRateTriple α x (q,y))
        ∂positiveTimeMeasure.prod positiveTimeMeasure := integral_prod _ hp
    _ = ∫ q : ℝ × ℝ, bubbleTripleCoefficient α * parameterKernel ((3-α)/2) (‖x‖^2) q
        ∂positiveTimeMeasure.prod positiveTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [positiveTimePair_ae] with q hq
      exact bubbleRateTriple_spatial_integral α x hq.1 hq.2
    _ = _ := integral_const_mul _ _

#print axioms bubbleTripleCoefficient_pos
#print axioms bubbleRateTriple_factor
#print axioms bubbleRateTriple_spatial_integrable
#print axioms bubbleRateTriple_spatial_integral
#print axioms bubbleRateTriple_nonneg
#print axioms bubbleRateTriple_measurable
#print axioms bubbleRateTriple_integrable
#print axioms bubbleRateTriple_time_integrable
#print axioms bubbleRateTriple_time_integral
#print axioms bubble_potential_integrable
#print axioms bubble_potential_parameter_identity
end HartreeF.BubbleProfile
