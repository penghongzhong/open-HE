import FEnergyGradientTopology
import H1SmoothTestApproximation
import CutoffConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest WeakHartreeProduct WeakCutoffLp

/-- The real coordinate projection, with its value embedded in the complex field. -/
def realCoordinateMap (j : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ (coordinate j))

theorem inDotEnergyState_gradient_eq {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) (j : Fin 3) :
    energyGradient j (inDotEnergyState hu) =
      (realCoordinateMap j).compLpL 2 volume (hu.real_gradient_L2.toLp U) +
      Complex.I • (realCoordinateMap j).compLpL 2 volume (hu.imag_gradient_L2.toLp V) := by
  apply Lp.ext
  filter_upwards [inDotEnergyState_gradient_ae hu j,
    Lp.coeFn_add ((realCoordinateMap j).compLpL 2 volume (hu.real_gradient_L2.toLp U))
      (Complex.I • (realCoordinateMap j).compLpL 2 volume (hu.imag_gradient_L2.toLp V)),
    Lp.coeFn_smul Complex.I ((realCoordinateMap j).compLpL 2 volume (hu.imag_gradient_L2.toLp V)),
    (realCoordinateMap j).coeFn_compLpL (hu.real_gradient_L2.toLp U),
    (realCoordinateMap j).coeFn_compLpL (hu.imag_gradient_L2.toLp V),
    hu.real_gradient_L2.coeFn_toLp, hu.imag_gradient_L2.coeFn_toLp] with x hx ha hs hr hi hU hV
  rw [hx, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hr, hi, hU, hV]
  apply Complex.ext <;>
    simp [directionalField, realCoordinateMap, real_inner_comm, smul_eq_mul]

/-- Genuine two-real weak-gradient convergence gives convergence of actual C43 states.
The target is explicitly constructed from an existing InDotH1 witness. -/
theorem inDotEnergyState_tendsto {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    {un : ℕ → Space → ℂ} {Un Vn : ℕ → Space → Space}
    (hn : ∀ n, InDotH1 (un n) (Un n) (Vn n))
    (hU : Tendsto (fun n => eLpNorm (Un n - U) 2 volume) atTop (𝓝 0))
    (hV : Tendsto (fun n => eLpNorm (Vn n - V) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => inDotEnergyState (hn n)) atTop (𝓝 (inDotEnergyState hu)) := by
  have hUr := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Un
    (fun n => (hn n).real_gradient_L2) U hu.real_gradient_L2).mpr hU
  have hVi := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Vn
    (fun n => (hn n).imag_gradient_L2) V hu.imag_gradient_L2).mpr hV
  apply tendsto_of_gradientTendsto hSob
  intro j
  simp_rw [inDotEnergyState_gradient_eq]
  exact (((realCoordinateMap j).compLpL 2 volume).continuous.tendsto _ |>.comp hUr).add
    ((((realCoordinateMap j).compLpL 2 volume).continuous.tendsto _ |>.comp hVi).const_smul Complex.I)

/-- A genuine compactly supported smooth real test. -/
abbrev CompactSmoothReal := {φ : Space → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}

/-- A single complex approximant with its real and imaginary parts linked. -/
def compactSmoothFunction (φ : CompactSmoothReal × CompactSmoothReal) (x : Space) : ℂ :=
  (φ.1.val x : ℂ) + Complex.I * (φ.2.val x : ℂ)

theorem compactSmoothFunction_contDiff (φ : CompactSmoothReal × CompactSmoothReal) :
    ContDiff ℝ (⊤ : ℕ∞) (compactSmoothFunction φ) :=
  (Complex.ofRealCLM.contDiff.comp φ.1.property.1).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp φ.2.property.1))

theorem compactSmoothFunction_support (φ : CompactSmoothReal × CompactSmoothReal) :
    HasCompactSupport (compactSmoothFunction φ) := by
  have ha : HasCompactSupport (fun x => (φ.1.val x : ℂ)) :=
    φ.1.property.2.comp_left (g := Complex.ofRealCLM) rfl
  have hb : HasCompactSupport (fun x => (φ.2.val x : ℂ)) :=
    φ.2.property.2.comp_left (g := Complex.ofRealCLM) rfl
  exact ha.add hb.mul_left

theorem compactSmoothFunction_inDotH1 (φ : CompactSmoothReal × CompactSmoothReal) :
    InDotH1 (compactSmoothFunction φ) (gradient φ.1.val) (gradient φ.2.val) := by
  refine ⟨(compactSmoothFunction_contDiff φ).continuous.memLp_of_hasCompactSupport
    (compactSmoothFunction_support φ),
    cutoff_gradient_memLp φ.1.property.1 φ.1.property.2 _,
    cutoff_gradient_memLp φ.2.property.1 φ.2.property.2 _, ?_, ?_⟩
  · simpa [compactSmoothFunction] using smooth_hasWeakGradient φ.1.property.1
  · simpa [compactSmoothFunction] using smooth_hasWeakGradient φ.2.property.1

/-- The actual C43 state of one compactly supported smooth complex function. -/
def compactSmoothState (φ : CompactSmoothReal × CompactSmoothReal) : EnergyState :=
  inDotEnergyState (compactSmoothFunction_inDotH1 φ)

theorem compactSmoothState_value_ae (φ : CompactSmoothReal × CompactSmoothReal) :
    (energyValue (compactSmoothState φ) : Space → ℂ) =ᵐ[volume] compactSmoothFunction φ :=
  inDotEnergyState_value_ae _

theorem compactSmoothState_real_gradient_ae (φ : CompactSmoothReal × CompactSmoothReal) :
    energyProjectedGradient Complex.reCLM (compactSmoothState φ) =ᵐ[volume] gradient φ.1.val :=
  inDotEnergyState_real_gradient_ae _

theorem compactSmoothState_imag_gradient_ae (φ : CompactSmoothReal × CompactSmoothReal) :
    energyProjectedGradient Complex.imCLM (compactSmoothState φ) =ᵐ[volume] gradient φ.2.val :=
  inDotEnergyState_imag_gradient_ae _

/-- The ordinary H1 interface is invoked only for actual localized L2 values. -/
theorem h1_compactSmoothState_approximation (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) (hu2 : MemLp u 2 volume) :
    ∃ φ : ℕ → CompactSmoothReal × CompactSmoothReal,
      Tendsto (fun n => compactSmoothState (φ n)) atTop (𝓝 (inDotEnergyState hu)) := by
  obtain ⟨a, ha, _, _, hUa⟩ := h1_smooth_test_approximation hDensity hSob
    (hu2.continuousLinearMap_comp Complex.reCLM)
    (hu.function_L6.continuousLinearMap_comp Complex.reCLM) hu.real_gradient_L2 hu.real_weak
  obtain ⟨b, hb, _, _, hVb⟩ := h1_smooth_test_approximation hDensity hSob
    (hu2.continuousLinearMap_comp Complex.imCLM)
    (hu.function_L6.continuousLinearMap_comp Complex.imCLM) hu.imag_gradient_L2 hu.imag_weak
  refine ⟨fun n => (⟨a n, ha n⟩, ⟨b n, hb n⟩), ?_⟩
  exact inDotEnergyState_tendsto hSob hu
    (fun n => compactSmoothFunction_inDotH1 (⟨a n, ha n⟩, ⟨b n, hb n⟩)) hUa hVb

end HartreeF.EnergySpace
