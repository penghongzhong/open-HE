import FRetardedEnergyContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.Retarded
open FreeFlow EnergySpace SobolevStretch StationarySelfTest

/-- Explicit finite constant for the C43 graph norm, for three spatial coordinates. -/
def energyEndpointConstant (K C : ℝ) : ℝ :=
  max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3 * C

theorem energyEndpointConstant_nonneg {K C : ℝ} (h : OrdinaryEndpointBound C) :
    0 ≤ energyEndpointConstant K C := by
  unfold energyEndpointConstant
  exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
    (Real.sqrt_nonneg _)) h.1

/-- A bound on the three genuine coordinate derivatives controls the graph norm.
The source norm is the finite-coordinate maximum of the Bochner L2_t L6/5_x norms. -/
theorem energyState_bound_of_coordinate_bounds {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (u : EnergyState) (G : Fin 3 → EndpointSource)
    (hG : ∀ j : Fin 3, ‖energyGradient j u‖ ≤ C * ‖G j‖) :
    ‖u‖ ≤ energyEndpointConstant K C * ‖G‖ := by
  have hcoord : ‖u.val.2‖ ≤ C * ‖G‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg G))).mpr
    intro j
    exact (hG j).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm G j) h.1)
  calc
    ‖u‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm u :=
      energyState_le_pureGradient hSob u
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * (Real.sqrt 3 * ‖u.val.2‖) :=
      mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_coordinateMax u)
        (le_trans zero_le_one (le_max_right _ _))
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * (Real.sqrt 3 * (C * ‖G‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg _))
        (le_trans zero_le_one (le_max_right _ _))
    _ = _ := by unfold energyEndpointConstant; ring

variable (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))

theorem restrictedEnergyState_norm (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) :
    ‖restrictedEnergyState hDensity hSob h F G hFG J hJ t‖ ≤
      energyEndpointConstant K C * ‖G‖ := by
  apply energyState_bound_of_coordinate_bounds hSob h _ G
  intro j
  rw [restrictedEnergyState_gradient]
  exact restrictedL2_norm h J hJ t (G j)

theorem retardedEnergyState_norm (t : ℝ) :
    ‖retardedEnergyState hDensity hSob h F G hFG t‖ ≤
      energyEndpointConstant K C * ‖G‖ :=
  restrictedEnergyState_norm hDensity hSob h F G hFG _ _ t

theorem forwardEnergyState_norm (a t : ℝ) :
    ‖forwardEnergyState hDensity hSob h a F G hFG t‖ ≤
      energyEndpointConstant K C * ‖G‖ :=
  restrictedEnergyState_norm hDensity hSob h F G hFG _ _ t

variable (F' : EndpointSource) (G' : Fin 3 → EndpointSource)
    (hFG' : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F' s)) = Lp.toTemperedDistribution (G' j s))

/-- The difference identity is derived by the two existing linear maps. -/
theorem restrictedEnergyState_sub_gradient (J : Set ℝ) (hJ : MeasurableSet J)
    (t : ℝ) (j : Fin 3) :
    energyGradient j (restrictedEnergyState hDensity hSob h F G hFG J hJ t -
      restrictedEnergyState hDensity hSob h F' G' hFG' J hJ t) =
      restrictedL2 h J hJ t (G j - G' j) := by
  rw [(energyGradient j).map_sub, restrictedEnergyState_gradient,
    restrictedEnergyState_gradient]
  exact ((restrictedL2CLM h J hJ t).map_sub (G j) (G' j)).symm

theorem retardedEnergyState_sub_gradient (t : ℝ) (j : Fin 3) :
    energyGradient j (retardedEnergyState hDensity hSob h F G hFG t -
      retardedEnergyState hDensity hSob h F' G' hFG' t) =
      retardedL2 h (G j - G' j) t :=
  restrictedEnergyState_sub_gradient hDensity hSob h F G hFG F' G' hFG' _ _ t j

theorem forwardEnergyState_sub_gradient (a t : ℝ) (j : Fin 3) :
    energyGradient j (forwardEnergyState hDensity hSob h a F G hFG t -
      forwardEnergyState hDensity hSob h a F' G' hFG' t) =
      forwardL2 h a (G j - G' j) t :=
  restrictedEnergyState_sub_gradient hDensity hSob h F G hFG F' G' hFG' _ _ t j

theorem restrictedEnergyState_sub_norm (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) :
    ‖restrictedEnergyState hDensity hSob h F G hFG J hJ t -
      restrictedEnergyState hDensity hSob h F' G' hFG' J hJ t‖ ≤
      energyEndpointConstant K C * ‖G - G'‖ := by
  apply energyState_bound_of_coordinate_bounds hSob h _ (G - G')
  intro j
  rw [restrictedEnergyState_sub_gradient]
  exact restrictedL2_norm h J hJ t (G j - G' j)

theorem retardedEnergyState_sub_norm (t : ℝ) :
    ‖retardedEnergyState hDensity hSob h F G hFG t -
      retardedEnergyState hDensity hSob h F' G' hFG' t‖ ≤
      energyEndpointConstant K C * ‖G - G'‖ :=
  restrictedEnergyState_sub_norm hDensity hSob h F G hFG F' G' hFG' _ _ t

theorem forwardEnergyState_sub_norm (a t : ℝ) :
    ‖forwardEnergyState hDensity hSob h a F G hFG t -
      forwardEnergyState hDensity hSob h a F' G' hFG' t‖ ≤
      energyEndpointConstant K C * ‖G - G'‖ :=
  restrictedEnergyState_sub_norm hDensity hSob h F G hFG F' G' hFG' _ _ t

end HartreeF.Retarded
