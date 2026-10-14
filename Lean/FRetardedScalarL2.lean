import FFreeFlowCore
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Scalar retarded L2 realization from a numerical ordinary endpoint estimate.
The phase is the literal exp(-i t |2πξ|²) of FFreeFlowCore. Distribution tests
are complex bilinear, so their exact transpose is F(phase(t) F⁻φ), with no
conjugation and the same time sign. Riesz conversion conjugates once explicitly.
No output operator, energy state, or derivative compatibility is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform LineDeriv
open scoped ENNReal SchwartzMap
namespace HartreeF.Retarded
open FreeFlow

abbrev SourceSpace := Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure V)
instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
abbrev EndpointSource := Lp SourceSpace 2 (volume : Measure ℝ)

/-- Exact transpose of the actual Fourier propagator for bilinear distribution tests. -/
def freeTest (t : ℝ) : Test →L[ℂ] Test :=
  fourierCLM ℂ Test ∘L SchwartzMap.smulLeftCLM ℂ (phase t) ∘L fourierInvCLM ℂ Test

theorem free_apply (t : ℝ) (T : TD) (φ : Test) :
    free t T φ = T (freeTest t φ) := rfl

/-- The scalar time integrand uses the actual endpoint source representative. -/
def scalarIntegrand (t : ℝ) (F : EndpointSource) (φ : Test) (s : ℝ) : ℂ :=
  Lp.toTemperedDistribution (F s) (freeTest (t-s) φ)

/-- Numerical dual endpoint estimate, with source restricted to arbitrary measurable J.
This is the n=3, sigma=3/2, (q,r)=(2,6) specialization of Keel--Tao (5),(6).
It is an explicit Prop premise, never an asserted instance. It does not contain
an L2 output or an EnergyState. This is not the space-time retarded estimate (7). -/
def OrdinaryEndpointBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (J : Set ℝ), MeasurableSet J → ∀ (t : ℝ) (F : EndpointSource) (φ : Test),
    IntegrableOn (scalarIntegrand t F φ) J ∧
    ‖∫ s in J, scalarIntegrand t F φ s‖ ≤ C * ‖F‖ * ‖φ.toLp 2 volume‖

def scalarFunctional {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) : Test →ₗ[ℂ] ℂ where
  toFun φ := ∫ s in J, scalarIntegrand t F φ s
  map_add' φ ψ := by
    simp only [scalarIntegrand, map_add]
    exact integral_add (h.2 J hJ t F φ).1 (h.2 J hJ t F ψ).1
  map_smul' c φ := by
    simp only [scalarIntegrand, map_smul, RingHom.id_apply]
    exact integral_smul c _

def l2Functional {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) : L2 →L[ℂ] ℂ :=
  (scalarFunctional h J hJ t F).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem l2Functional_test {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) (φ : Test) :
    l2Functional h J hJ t F (φ.toLp 2 volume) = ∫ s in J, scalarIntegrand t F φ s := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  · exact ⟨C * ‖F‖, fun ψ => (h.2 J hJ t F ψ).2⟩

theorem l2Functional_norm {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    ‖l2Functional h J hJ t F‖ ≤ C * ‖F‖ := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  · exact mul_nonneg h.1 (norm_nonneg _)
  · exact fun ψ => (h.2 J hJ t F ψ).2

/-- Riesz construction; the conjugation converts its Hermitian pairing to distributions. -/
def restrictedL2 {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) : L2 :=
  star ((InnerProductSpace.toDual ℂ L2).symm (l2Functional h J hJ t F))

theorem l2_star_distribution (u : L2) (φ : Test) :
    Lp.toTemperedDistribution (star u) φ = inner ℂ u (φ.toLp 2 volume) := by
  rw [Lp.toTemperedDistribution_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u, φ.coeFn_toLp 2 volume] with x hu hφ
  simp only [hu, hφ, smul_eq_mul, Pi.star_apply, RCLike.inner_apply, starRingEnd_apply]

theorem l2_star_norm (u : L2) : ‖star u‖ = ‖u‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (Lp.coeFn_star u), eLpNorm_star]

theorem restrictedL2_scalar {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) (φ : Test) :
    Lp.toTemperedDistribution (restrictedL2 h J hJ t F) φ =
      ∫ s in J, scalarIntegrand t F φ s := by
  rw [restrictedL2, l2_star_distribution, InnerProductSpace.toDual_symm_apply,
    l2Functional_test]

theorem restrictedL2_norm {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    ‖restrictedL2 h J hJ t F‖ ≤ C * ‖F‖ := by
  rw [restrictedL2, l2_star_norm, (InnerProductSpace.toDual ℂ L2).symm.norm_map]
  exact l2Functional_norm h J hJ t F

/-- Retarded source realization on the entire past half-line. -/
def retardedL2 {C : ℝ} (h : OrdinaryEndpointBound C) (F : EndpointSource) (t : ℝ) : L2 :=
  restrictedL2 h (Set.Iio t) measurableSet_Iio t F

theorem retardedL2_scalar {C : ℝ} (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (t : ℝ) (φ : Test) :
    Lp.toTemperedDistribution (retardedL2 h F t) φ =
      ∫ s in Set.Iio t, scalarIntegrand t F φ s :=
  restrictedL2_scalar h _ _ _ _ _

theorem retardedL2_norm {C : ℝ} (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (t : ℝ) : ‖retardedL2 h F t‖ ≤ C * ‖F‖ :=
  restrictedL2_norm h _ _ _ _

end HartreeF.Retarded
