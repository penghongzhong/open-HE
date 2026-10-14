import FEnergyFreeProperties

/-! Native L2 calculus for genuinely bounded temperate symbols. Every operator
is the literal Mathlib 2π Fourier multiplier; no PDE or Lp-multiplier premise. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization
open EnergySpace

structure BoundedSymbol where
  symbol : V → ℂ
  temperate : symbol.HasTemperateGrowth
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ ξ, ‖symbol ξ‖ ≤ bound

namespace BoundedSymbol
private instance : ENNReal.HolderTriple ∞ 2 2 := ⟨by simp⟩

def distribution (m : BoundedSymbol) : TD →L[ℂ] TD :=
  TemperedDistribution.fourierMultiplierCLM ℂ m.symbol

def schwartz (m : BoundedSymbol) : Test →L[ℂ] Test :=
  SchwartzMap.fourierMultiplierCLM ℂ m.symbol

theorem memLp_top (m : BoundedSymbol) : MemLp m.symbol ∞ (volume : Measure V) :=
  memLp_top_of_bound m.temperate.1.continuous.aestronglyMeasurable m.bound
    (Eventually.of_forall m.norm_le)

def infinity (m : BoundedSymbol) : Lp ℂ ∞ (volume : Measure V) :=
  m.memLp_top.toLp m.symbol

def multiply (m : BoundedSymbol) : L2 →L[ℂ] L2 :=
  FreeFlow.lpMul ∞ 2 2 m.infinity

theorem multiply_coe (m : BoundedSymbol) (f : L2) :
    (m.multiply f : V → ℂ) =ᵐ[volume] fun ξ => m.symbol ξ * f ξ := by
  filter_upwards [FreeFlow.lpMul_coe (r := 2) m.infinity f, m.memLp_top.coeFn_toLp]
    with ξ h₁ h₂
  exact h₁.trans (by change m.infinity ξ = m.symbol ξ at h₂; rw [h₂])

theorem multiply_norm_le (m : BoundedSymbol) (f : L2) :
    ‖m.multiply f‖ ≤ m.bound * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [m.multiply_coe f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

theorem multiply_distribution (m : BoundedSymbol) (f : L2) :
    Lp.toTemperedDistribution (m.multiply f) =
      TemperedDistribution.smulLeftCLM ℂ m.symbol (Lp.toTemperedDistribution f) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [m.multiply_coe f] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply_apply m.temperate, smul_eq_mul]
  ring

def l2 (m : BoundedSymbol) : L2 →L[ℂ] L2 :=
  fourierInvCLM ℂ L2 ∘L m.multiply ∘L fourierCLM ℂ L2

theorem l2_distribution (m : BoundedSymbol) (f : L2) :
    Lp.toTemperedDistribution (m.l2 f) = m.distribution (Lp.toTemperedDistribution f) := by
  change Lp.toTemperedDistribution (𝓕⁻ (m.multiply (𝓕 f))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ m.symbol (𝓕 (Lp.toTemperedDistribution f)))
  rw [← Lp.fourierInv_toTemperedDistribution_eq, m.multiply_distribution,
    Lp.fourier_toTemperedDistribution_eq]

theorem l2_fourier (m : BoundedSymbol) (f : L2) :
    𝓕 (m.l2 f) = m.multiply (𝓕 f) := fourier_fourierInv_eq _

theorem l2_norm_le (m : BoundedSymbol) (f : L2) : ‖m.l2 f‖ ≤ m.bound * ‖f‖ := by
  rw [← Lp.norm_fourier_eq (m.l2 f), m.l2_fourier]
  exact (m.multiply_norm_le _).trans_eq (by rw [Lp.norm_fourier_eq])

theorem derivative_distribution (m : BoundedSymbol) (T : TD) (v : V) :
    ∂_{v} (m.distribution T) = m.distribution (∂_{v} T) := by
  change ∂_{v} (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ m.symbol (𝓕 T))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ m.symbol (𝓕 (∂_{v} T)))
  rw [TemperedDistribution.lineDerivOp_fourierInv_eq,
    TemperedDistribution.fourier_lineDerivOp_eq, map_smul]
  congr 1
  have hi : (fun x : V => (inner ℝ x v : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_inner_left v)
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply m.temperate hi,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hi m.temperate]
  simp only [mul_comm]

theorem distribution_commute (m q : BoundedSymbol) (T : TD) :
    m.distribution (q.distribution T) = q.distribution (m.distribution T) := by
  unfold distribution
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply q.temperate m.temperate,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply m.temperate q.temperate]
  simp only [mul_comm]

theorem distribution_free (m : BoundedSymbol) (t : ℝ) (T : TD) :
    m.distribution (FreeFlow.free t T) = FreeFlow.free t (m.distribution T) := by
  unfold distribution FreeFlow.free
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (FreeFlow.phase_temperate t) m.temperate,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      m.temperate (FreeFlow.phase_temperate t)]
  simp only [mul_comm]

theorem schwartz_distribution (m : BoundedSymbol) (φ : Test) :
    energyDistribution (schwartzEnergyState (m.schwartz φ)) =
      m.distribution (energyDistribution (schwartzEnergyState φ)) := by
  rw [schwartzEnergyState_distribution, schwartzEnergyState_distribution]
  exact (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq m.temperate φ).symm

theorem schwartz_gradient (m : BoundedSymbol) (φ : Test) (j : Fin 3) :
    energyGradient j (schwartzEnergyState (m.schwartz φ)) =
      m.l2 (energyGradient j (schwartzEnergyState φ)) := by
  apply FreeFlow.l2_distribution_injective
  rw [m.l2_distribution]
  change energyGradientDistribution j (schwartzEnergyState (m.schwartz φ)) =
    m.distribution (energyGradientDistribution j (schwartzEnergyState φ))
  rw [← energyDistribution_derivative, ← energyDistribution_derivative,
    m.schwartz_distribution, m.derivative_distribution]

theorem l2_selfAdjoint (m : BoundedSymbol) (hreal : ∀ ξ, star (m.symbol ξ) = m.symbol ξ)
    (f g : L2) : inner ℂ (m.l2 f) g = inner ℂ f (m.l2 g) := by
  rw [← Lp.inner_fourier_eq (m.l2 f) g, ← Lp.inner_fourier_eq f (m.l2 g),
    m.l2_fourier, m.l2_fourier, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [m.multiply_coe (𝓕 f), m.multiply_coe (𝓕 g)] with ξ hf hg
  rw [hf, hg]
  change (𝓕 g) ξ * star (m.symbol ξ * (𝓕 f) ξ) =
    (m.symbol ξ * (𝓕 g) ξ) * star ((𝓕 f) ξ)
  rw [star_mul, hreal]
  ring

/-- Native dominated convergence, with an almost-everywhere symbol limit.
The exceptional zero frequency therefore imposes no mass condition. -/
theorem l2_tendsto (m : ℕ → BoundedSymbol) {C : ℝ}
    (hC : ∀ n, (m n).bound ≤ C)
    (hlim : ∀ᵐ ξ ∂(volume : Measure V), Tendsto (fun n => (m n).symbol ξ) atTop (𝓝 1))
    (f : L2) : Tendsto (fun n => (m n).l2 f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let g : L2 := 𝓕 f
  have hg : Integrable (fun ξ => ‖g ξ‖ ^ 2) := (Lp.memLp g).norm.integrable_sq
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun n ξ => ‖((m n).symbol ξ - 1) * g ξ‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun ξ => (C + 1)^2 * ‖g ξ‖^2)
    (Eventually.of_forall fun n =>
      ((((m n).temperate.1.continuous.aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul (Lp.aestronglyMeasurable g)).norm.pow 2))
    (Eventually.of_forall fun n => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hm : ‖(m n).symbol ξ - 1‖ ≤ C + 1 :=
        (norm_sub_le _ _).trans (by simpa using add_le_add_right ((m n).norm_le ξ |>.trans (hC n)) 1)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm 2) (sq_nonneg _))
    (hg.const_mul _) (by
      filter_upwards [hlim] with ξ hξ
      have ht := (hξ.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul_const (g ξ)
      simpa only [sub_self, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using ht.norm.pow 2)
  have hid (n : ℕ) : ‖(m n).l2 f - f‖^2 = ∫ ξ, ‖((m n).symbol ξ - 1) * g ξ‖^2 := by
    rw [← Lp.norm_fourier_eq ((m n).l2 f - f)]
    have hs : 𝓕 ((m n).l2 f - f) = 𝓕 ((m n).l2 f) - 𝓕 f := (fourierCLM ℂ L2).map_sub _ _
    rw [hs, (m n).l2_fourier, FreeFlow.l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((m n).multiply g) g, (m n).multiply_coe g] with ξ hs hm
    rw [hs, Pi.sub_apply, hm, sub_mul, one_mul]
  have hsq : Tendsto (fun n => ‖(m n).l2 f - f‖^2) atTop (𝓝 0) := by
    simpa only [hid, integral_zero] using hd
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end BoundedSymbol
end HartreeF.Regularization

#print axioms HartreeF.Regularization.BoundedSymbol.l2_tendsto
#print axioms HartreeF.Regularization.BoundedSymbol.l2_selfAdjoint
#print axioms HartreeF.Regularization.BoundedSymbol.derivative_distribution
