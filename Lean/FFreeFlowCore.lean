import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Actual Fourier free evolution for F on R3. This candidate extracts only
linear utilities from frozen D; see PROVENANCE.json. No D/NLS modules are
imported. L2 is used for gradient data, never assumed for the original value.
The Mathlib frequency convention is cycles/unit, hence the 2*pi factor. -/
namespace HartreeF.FreeFlow
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform LineDeriv
open scoped ENNReal SchwartzMap

abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev L2 := Lp ℂ 2 (volume : Measure V)
abbrev TD := TemperedDistribution V ℂ
abbrev Test := SchwartzMap V ℂ
abbrev LpC (p : ℝ≥0∞) := Lp ℂ p (volume : Measure V)

def phase (t : ℝ) (ξ : V) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ))

def free (t : ℝ) : TD →L[ℂ] TD := TemperedDistribution.fourierMultiplierCLM ℂ (phase t)

def lpMul (p q r : ℝ≥0∞) [ENNReal.HolderTriple p q r]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] :
    LpC p →L[ℂ] LpC q →L[ℂ] LpC r :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume p q r

theorem lpMul_coe {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] (f : LpC p) (g : LpC q) :
    (lpMul p q r f g : V → ℂ) =ᵐ[volume] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder f g

private instance : ENNReal.HolderTriple ∞ 2 2 := ⟨by simp⟩

theorem phase_temperate (t : ℝ) : (phase t).HasTemperateGrowth := by
  have hcoord (j : Fin 3) : (fun ξ : V => ξ j).HasTemperateGrowth :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasTemperateGrowth
  have hd : (fun ξ : V => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2).HasTemperateGrowth := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    fun_prop
  have he := Complex.hasTemperateGrowth_exp_mul_I.comp
    ((Function.HasTemperateGrowth.const (-t)).mul hd)
  convert he using 1
  funext ξ
  unfold phase
  congr 1
  simp only [Pi.mul_apply]
  push_cast
  ring

theorem phase_norm (t : ℝ) (ξ : V) : ‖phase t ξ‖ = 1 := by
  have he : phase t ξ = Complex.exp
      (((-t * ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero]

theorem phase_memLp (t : ℝ) : MemLp (phase t) ∞ (volume : Measure V) :=
  memLp_top_of_bound (phase_temperate t).1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ξ => (phase_norm t ξ).le))

def phaseInfinity (t : ℝ) : LpC ∞ := (phase_memLp t).toLp (phase t)

def phaseMultiply (t : ℝ) : L2 →L[ℂ] L2 := lpMul ∞ 2 2 (phaseInfinity t)

theorem phaseMultiply_coe (t : ℝ) (f : L2) :
    (phaseMultiply t f : V → ℂ) =ᵐ[volume] fun ξ => phase t ξ * f ξ := by
  filter_upwards [lpMul_coe (r := 2) (phaseInfinity t) f, (phase_memLp t).coeFn_toLp] with ξ h1 h2
  change phaseInfinity t ξ = phase t ξ at h2
  exact h1.trans (by rw [h2])

theorem phaseMultiply_norm (t : ℝ) (f : L2) : ‖phaseMultiply t f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [phaseMultiply_coe t f] with ξ hξ
  rw [hξ, norm_mul, phase_norm, one_mul]

theorem phaseMultiply_distribution (t : ℝ) (f : L2) :
    Lp.toTemperedDistribution (phaseMultiply t f) =
      TemperedDistribution.smulLeftCLM ℂ (phase t) (Lp.toTemperedDistribution f) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [phaseMultiply_coe t f] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply_apply (phase_temperate t), smul_eq_mul]
  ring

def freeL2 (t : ℝ) : L2 →L[ℂ] L2 :=
  fourierInvCLM ℂ L2 ∘L phaseMultiply t ∘L fourierCLM ℂ L2

theorem freeL2_distribution (t : ℝ) (f : L2) :
    Lp.toTemperedDistribution (freeL2 t f) = free t (Lp.toTemperedDistribution f) := by
  change Lp.toTemperedDistribution (𝓕⁻ (phaseMultiply t (𝓕 f))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (phase t) (𝓕 (Lp.toTemperedDistribution f)))
  rw [← Lp.fourierInv_toTemperedDistribution_eq, phaseMultiply_distribution,
    Lp.fourier_toTemperedDistribution_eq]

theorem freeL2_norm (t : ℝ) (f : L2) : ‖freeL2 t f‖ = ‖f‖ := by
  change ‖𝓕⁻ (phaseMultiply t (𝓕 f))‖ = ‖f‖
  have hi : ∀ g : L2, ‖𝓕⁻ g‖ = ‖g‖ := fun g => by
    have h := Lp.norm_fourier_eq (𝓕⁻ g)
    simpa only [fourier_fourierInv_eq] using h.symm
  rw [hi, phaseMultiply_norm, Lp.norm_fourier_eq]

theorem phase_add (s t : ℝ) (ξ : V) : phase (s+t) ξ = phase s ξ * phase t ξ := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_zero (ξ : V) : phase 0 ξ = 1 := by simp [phase]

theorem free_zero (u : TD) : free 0 u = u := by
  have h : phase 0 = fun _ : V => (1 : ℂ) := funext phase_zero
  simp only [free, h, TemperedDistribution.fourierMultiplierCLM_const,
    one_smul, ContinuousLinearMap.id_apply]

theorem free_add (s t : ℝ) (u : TD) : free (s+t) u = free s (free t u) := by
  have hp : phase t * phase s = phase (s+t) := by
    funext ξ
    simp only [Pi.mul_apply, phase_add, mul_comm]
  unfold free
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (phase_temperate t) (phase_temperate s), hp]

theorem l2_distribution_injective : Function.Injective (Lp.toTemperedDistribution : L2 → TD) := by
  exact LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure V)) (p := 2))

theorem freeL2_add (s t : ℝ) (f : L2) : freeL2 (s+t) f = freeL2 s (freeL2 t f) := by
  apply l2_distribution_injective
  rw [freeL2_distribution, freeL2_distribution, freeL2_distribution, free_add]

theorem freeL2_zero (f : L2) : freeL2 0 f = f := by
  apply l2_distribution_injective
  rw [freeL2_distribution, free_zero]

theorem freeL2_inverse (t : ℝ) (f : L2) : freeL2 t (freeL2 (-t) f) = f := by
  rw [← freeL2_add, add_neg_cancel, freeL2_zero]

theorem freeL2_adjoint (t : ℝ) (f g : L2) :
    inner ℂ (freeL2 t f) g = inner ℂ f (freeL2 (-t) g) := by
  let U : L2 →ₗᵢ[ℂ] L2 :=
    { (freeL2 t).toLinearMap with norm_map' := freeL2_norm t }
  have h := U.inner_map_map f (freeL2 (-t) g)
  change inner ℂ (freeL2 t f) (freeL2 t (freeL2 (-t) g)) = _ at h
  rwa [freeL2_inverse] at h

def freeSchwartz (t : ℝ) : Test →L[ℂ] Test :=
  SchwartzMap.fourierMultiplierCLM ℂ (phase t)

theorem freeSchwartz_toL2 (t : ℝ) (φ : Test) :
    (freeSchwartz t φ).toLp 2 volume = freeL2 t (φ.toLp 2 volume) := by
  apply l2_distribution_injective
  rw [freeL2_distribution]
  simp only [Lp.toTemperedDistribution_toLp_eq]
  exact (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (phase_temperate t) φ).symm

theorem freeSchwartz_fourier (t : ℝ) (φ : Test) (ξ : V) :
    𝓕 (freeSchwartz t φ) ξ = phase t ξ * 𝓕 φ ξ := by
  simp [freeSchwartz, SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (phase_temperate t)]

theorem derivative_free (t : ℝ) (T : TD) (v : V) :
    ∂_{v} (free t T) = free t (∂_{v} T) := by
  change ∂_{v} (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (phase t) (𝓕 T))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (phase t) (𝓕 (∂_{v} T)))
  rw [TemperedDistribution.lineDerivOp_fourierInv_eq,
    TemperedDistribution.fourier_lineDerivOp_eq, map_smul]
  congr 1
  have hi : (fun x : V => (inner ℝ x v : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_inner_left v)
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (phase_temperate t) hi,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hi (phase_temperate t)]
  simp only [mul_comm]

/-- Any distribution with an L2 directional derivative propagates that
actual derivative by the native Fourier L2 group. The value need not be L2. -/
theorem free_derivative_of_L2 (t : ℝ) (T : TD) (v : V) (g : L2)
    (h : ∂_{v} T = Lp.toTemperedDistribution g) :
    ∂_{v} (free t T) = Lp.toTemperedDistribution (freeL2 t g) := by
  rw [derivative_free, h, freeL2_distribution]

end
end HartreeF.FreeFlow
