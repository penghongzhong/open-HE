import FEnergyWeakGradientTemperedDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.EnergySpace
open SobolevStretch WeakHartreeProduct

theorem energyProjectedGradient_coordinate (L : ℂ →L[ℝ] ℝ) (u : EnergyState)
    (x : Space) (j : Fin 3) :
    ⟪energyProjectedGradient L u x, coordinate j⟫ = L (energyGradient j u x) := by
  fin_cases j <;> simp [energyProjectedGradient, Fin.sum_univ_three, coordinate,
    inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem state_directionalField_coordinate (u : EnergyState) (j : Fin 3) :
    directionalField (energyProjectedGradient Complex.reCLM u)
      (energyProjectedGradient Complex.imCLM u) (coordinate j) = energyGradient j u := by
  funext x
  apply Complex.ext
  · simp only [directionalField, Complex.equivRealProdCLM_symm_apply_re,
      energyProjectedGradient_coordinate, Complex.reCLM_apply]
  · simp only [directionalField, Complex.equivRealProdCLM_symm_apply_im,
      energyProjectedGradient_coordinate, Complex.imCLM_apply]

/-- The inverse direction of the energy-domain bridge: canonical L6 data with
actual two-real weak gradients produce the concrete Banach energy state. -/
def inDotEnergyState {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) : EnergyState :=
  ⟨(hu.function_L6.toLp u, fun j =>
      (directionalField_memLp hu.real_gradient_L2 hu.imag_gradient_L2 (coordinate j)).toLp
        (directionalField U V (coordinate j))),
    (mem_energySubmodule _).mpr (fun j => weak_gradient_tempered_derivative hu.function_L6
      hu.real_gradient_L2 hu.imag_gradient_L2 hu.real_weak hu.imag_weak (coordinate j))⟩

theorem inDotEnergyState_value_ae {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) : (energyValue (inDotEnergyState hu) : Space → ℂ) =ᵐ[volume] u :=
  hu.function_L6.coeFn_toLp

theorem inDotEnergyState_gradient_ae {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) (j : Fin 3) :
    (energyGradient j (inDotEnergyState hu) : Space → ℂ) =ᵐ[volume]
      directionalField U V (coordinate j) :=
  (directionalField_memLp hu.real_gradient_L2 hu.imag_gradient_L2 (coordinate j)).coeFn_toLp

theorem inDotEnergyState_roundtrip (u : EnergyState) :
    inDotEnergyState (energyState_inDotH1 u) = u := by
  apply Subtype.ext
  apply Prod.ext
  · change ((Lp.memLp (energyValue u)).toLp (energyValue u)) = u.val.1
    exact Lp.toLp_coeFn (energyValue u) (Lp.memLp (energyValue u))
  · funext j
    apply Lp.ext
    filter_upwards [inDotEnergyState_gradient_ae (energyState_inDotH1 u) j] with x hx
    change energyGradient j (inDotEnergyState (energyState_inDotH1 u)) x = energyGradient j u x
    rw [hx, state_directionalField_coordinate]

/-- The inverse construction preserves the original real gradient almost everywhere. -/
theorem inDotEnergyState_real_gradient_ae {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) :
    energyProjectedGradient Complex.reCLM (inDotEnergyState hu) =ᵐ[volume] U := by
  have h : ∀ᵐ x ∂(volume : Measure Space), ∀ j : Fin 3,
      energyGradient j (inDotEnergyState hu) x = directionalField U V (coordinate j) x :=
    (ae_all_iff).mpr (inDotEnergyState_gradient_ae hu)
  filter_upwards [h] with x hx
  rw [energyProjectedGradient]
  simp only [hx, directionalField, Complex.reCLM_apply,
    Complex.equivRealProdCLM_symm_apply_re, coordinate, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul]
  exact coordinate_reconstruct (U x)

/-- The inverse construction preserves the original imaginary gradient almost everywhere. -/
theorem inDotEnergyState_imag_gradient_ae {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) :
    energyProjectedGradient Complex.imCLM (inDotEnergyState hu) =ᵐ[volume] V := by
  have h : ∀ᵐ x ∂(volume : Measure Space), ∀ j : Fin 3,
      energyGradient j (inDotEnergyState hu) x = directionalField U V (coordinate j) x :=
    (ae_all_iff).mpr (inDotEnergyState_gradient_ae hu)
  filter_upwards [h] with x hx
  rw [energyProjectedGradient]
  simp only [hx, directionalField, Complex.imCLM_apply,
    Complex.equivRealProdCLM_symm_apply_im, coordinate, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul]
  exact coordinate_reconstruct (V x)

end HartreeF.EnergySpace
