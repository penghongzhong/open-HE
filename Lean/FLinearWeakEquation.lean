import FL1RetardedScalarIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory LineDeriv Laplacian FourierTransform
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace

/-- Smooth compactly supported time tests are represented in the actual Schwartz space. -/
abbrev TimeTest := SchwartzMap ℝ ℂ

/-- The genuine distributional time and space operator, with complex-linear duality. -/
def weakOperator (U : ℝ → TD) (η : TimeTest) (φ : Test) (t : ℝ) : ℂ :=
  -Complex.I * deriv η t * U t φ + η t * U t (Δ φ)

/-- Tensor-test distributional equation `i ∂t U + Δ U = F` on `(a,b)`.
No time derivative of U, mild formula, or L2 value-domain is part of this definition. -/
def WeakEquation (a b : ℝ) (U F : ℝ → TD) : Prop :=
  ∀ η : TimeTest, tsupport η ⊆ Set.Ioo a b → ∀ φ : Test,
    IntegrableOn (weakOperator U η φ) (Set.Icc a b) ∧
    IntegrableOn (fun t => η t * F t φ) (Set.Icc a b) ∧
    (∫ t in Set.Icc a b, weakOperator U η φ t) =
      ∫ t in Set.Icc a b, η t * F t φ

theorem test_derivatives_commute (v w : V) (φ : Test) :
    ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  have hf : 𝓕 (∂_{v} (∂_{w} φ)) = 𝓕 (∂_{w} (∂_{v} φ)) := by
    simp only [SchwartzMap.fourier_lineDerivOp_eq]
    ext x
    have hv : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
    have hw : (inner ℝ · w).HasTemperateGrowth := ((innerSL ℝ).flip w).hasTemperateGrowth
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hv,
      SchwartzMap.smulLeftCLM_apply_apply hw]
    simp only [smul_comm (inner ℝ x v) (2 * Real.pi * Complex.I),
      smul_comm (inner ℝ x w) (2 * Real.pi * Complex.I), smul_comm (inner ℝ x v) (inner ℝ x w)]
  simpa only [fourierInv_fourier_eq] using congrArg (fun f : Test => 𝓕⁻ f) hf

theorem test_laplacian_derivative (v : V) (φ : Test) :
    Δ (∂_{v} φ) = ∂_{v} (Δ φ) := by
  rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ V),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ V)]
  rw [lineDerivOp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [test_derivatives_commute ((stdOrthonormalBasis ℝ V) j) v φ,
    test_derivatives_commute ((stdOrthonormalBasis ℝ V) j) v
      (∂_{(stdOrthonormalBasis ℝ V) j} φ)]

theorem weakOperator_derivative (U : ℝ → TD) (v : V) (η : TimeTest)
    (φ : Test) (t : ℝ) :
    weakOperator (fun s => ∂_{v} (U s)) η φ t = weakOperator U η (-∂_{v} φ) t := by
  have hn (ψ : Test) : Δ (-ψ) = -Δ ψ := by
    rw [← SchwartzMap.laplacianCLM_eq ℂ, map_neg, SchwartzMap.laplacianCLM_eq]
  simp only [weakOperator, TemperedDistribution.lineDerivOp_apply_apply,
    hn, test_laplacian_derivative]

/-- Spatial differentiation of the actual weak equation is proved by differentiated tests. -/
theorem WeakEquation.derivative {a b : ℝ} {U F : ℝ → TD}
    (h : WeakEquation a b U F) (v : V) :
    WeakEquation a b (fun t => ∂_{v} (U t)) (fun t => ∂_{v} (F t)) := by
  intro η hη φ
  have he : weakOperator (fun t => ∂_{v} (U t)) η φ = weakOperator U η (-∂_{v} φ) :=
    funext (weakOperator_derivative U v η φ)
  simpa only [he, TemperedDistribution.lineDerivOp_apply_apply]
    using h η hη (-∂_{v} φ)

theorem weakOperator_sub (U V : ℝ → TD) (η : TimeTest) (φ : Test) (t : ℝ) :
    weakOperator (fun s => U s - V s) η φ t =
      weakOperator U η φ t - weakOperator V η φ t := by
  simp only [weakOperator, sub_apply, mul_sub]
  ring

theorem WeakEquation.sub {a b : ℝ} {U V F G : ℝ → TD}
    (hU : WeakEquation a b U F) (hV : WeakEquation a b V G) :
    WeakEquation a b (fun t => U t - V t) (fun t => F t - G t) := by
  intro η hη φ
  obtain ⟨hUi, hFi, hUe⟩ := hU η hη φ
  obtain ⟨hVi, hGi, hVe⟩ := hV η hη φ
  have he : weakOperator (fun t => U t - V t) η φ =
      fun t => weakOperator U η φ t - weakOperator V η φ t :=
    funext (weakOperator_sub U V η φ)
  simp only [he, sub_apply, mul_sub]
  exact ⟨hUi.sub hVi, hFi.sub hGi,
    by rw [integral_sub hUi hVi, integral_sub hFi hGi, hUe, hVe]⟩

theorem WeakEquation.sub_same_source {a b : ℝ} {U V F : ℝ → TD}
    (hU : WeakEquation a b U F) (hV : WeakEquation a b V F) :
    WeakEquation a b (fun t => U t - V t) (fun _ => 0) := by
  simpa only [sub_self] using hU.sub hV

/-- Compatibility comes from the existing closed energy graph, for every time. -/
theorem energy_gradient_weakEquation {a b : ℝ} {u : ℝ → EnergyState}
    {F : ℝ → TD} (hu : WeakEquation a b (fun t => energyDistribution (u t)) F)
    (j : Fin 3) :
    WeakEquation a b (fun t => Lp.toTemperedDistribution (energyGradient j (u t)))
      (fun t => ∂_{coordinate j} (F t)) := by
  have he (t : ℝ) : ∂_{coordinate j} (energyDistribution (u t)) =
      Lp.toTemperedDistribution (energyGradient j (u t)) :=
    energyDistribution_derivative (u t) j
  simpa only [he] using hu.derivative (coordinate j)

end HartreeF.LinearWeakEquation
