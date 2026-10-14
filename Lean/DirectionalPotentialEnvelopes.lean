import RieszPointwiseDomination

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.DerivativeMajorization
open ForcingDomain WeakHartreeChain

def sumAmplitude (u v : Space → ℂ) : Space → ℝ := fun x => ‖u x‖+‖v x‖
def differenceAmplitude (u v : Space → ℂ) : Space → ℝ := fun x => ‖u x-v x‖
def directionalDensity (α : ℝ) (u h : Space → ℂ) : Space → ℝ :=
  fun x => densityDerivative (3+α) (u x) (h x)

theorem directionalDensity_measurable (α : ℝ)
    {u h : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (directionalDensity α u h) volume := by
  change AEStronglyMeasurable (fun x => densityDerivative (3+α) (u x) (h x)) volume
  simp_rw [densityDerivative_apply]
  have hure := Complex.continuous_re.comp_aestronglyMeasurable hu
  have huim := Complex.continuous_im.comp_aestronglyMeasurable hu
  have hhre := Complex.continuous_re.comp_aestronglyMeasurable hh
  have hhim := Complex.continuous_im.comp_aestronglyMeasurable hh
  exact (aestronglyMeasurable_const.mul (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable).mul
    ((hure.mul hhre).add (huim.mul hhim))

theorem potential_pair_envelopes {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (x : Space)
    (hbase : Integrable (fun y => rieszKernel α c (x-y)*sumAmplitude u v y^(3+α)) volume)
    (hdiff : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*differenceAmplitude u v y)) volume) :
    Integrable (fun y => rieszKernel α c (x-y)*powerDensity α u y) volume ∧
    Integrable (fun y => rieszKernel α c (x-y)*powerDensity α v y) volume ∧
    ‖potential α c u x‖ ≤ rieszConvolution α c (fun y => sumAmplitude u v y^(3+α)) x ∧
    ‖potential α c u x-potential α c v x‖ ≤
      (3+α)*rieszConvolution α c
        (fun y => sumAmplitude u v y^(2+α)*differenceAmplitude u v y) x := by
  have hmU : AEStronglyMeasurable (powerDensity α u) volume :=
    (density_contDiff_one (by linarith : 1<3+α)).continuous.comp_aestronglyMeasurable hu
  have hmV : AEStronglyMeasurable (powerDensity α v) volume :=
    (density_contDiff_one (by linarith : 1<3+α)).continuous.comp_aestronglyMeasurable hv
  have hbu (y : Space) : ‖powerDensity α u y‖ ≤ sumAmplitude u v y^(3+α) := by
    rw [powerDensity,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _)) (by linarith)
  have hbv (y : Space) : ‖powerDensity α v y‖ ≤ sumAmplitude u v y^(3+α) := by
    rw [powerDensity,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) (by linarith)
  obtain ⟨hUi,hUn⟩ := riesz_fibre_norm_domination hc x hmU hbase hbu
  obtain ⟨hVi,_⟩ := riesz_fibre_norm_domination hc x hmV hbase hbv
  refine ⟨hUi,hVi,hUn,?_⟩
  apply riesz_difference_norm_const_domination hc x hmU hmV hUi hVi hdiff
  intro y
  have h := density_difference_bound (by linarith : 1<3+α) (u y) (v y)
  simpa only [WeakHartreeChain.density,powerDensity,sumAmplitude,differenceAmplitude,show 3+α-1=2+α by ring,mul_assoc] using h

#print axioms directionalDensity_measurable
#print axioms potential_pair_envelopes
end HartreeF.DerivativeMajorization
