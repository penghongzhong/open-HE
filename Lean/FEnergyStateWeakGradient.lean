import FEnergyProjectedCoordinateTests

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.EnergySpace
open SobolevStretch

def energyProjectedGradient (L : ℂ →L[ℝ] ℝ) (u : EnergyState) (x : V) : V :=
  ∑ j : Fin 3, L (energyGradient j u x) • coordinate j

theorem energyProjectedGradient_memLp (L : ℂ →L[ℝ] ℝ) (u : EnergyState) :
    MemLp (energyProjectedGradient L u) 2 volume := by
  apply memLp_finsetSum
  intro j _
  exact ((Lp.memLp (energyGradient j u)).continuousLinearMap_comp L).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

theorem coordinate_reconstruct (v : V) : (∑ j : Fin 3, v j • coordinate j) = v := by
  ext i
  fin_cases i <;> simp [coordinate, Fin.sum_univ_three]

theorem energyProjectedGradient_inner (L : ℂ →L[ℝ] ℝ) (u : EnergyState) (x v : V) :
    ⟪energyProjectedGradient L u x, v⟫ = ∑ j : Fin 3, L (energyGradient j u x) * v j := by
  simp [energyProjectedGradient, sum_inner, real_inner_smul_left, coordinate,
    EuclideanSpace.inner_single_left]

theorem energyState_hasWeakGradient (L : ℂ →L[ℝ] ℝ) (u : EnergyState) :
    HasWeakGradient (fun x => L (energyValue u x)) (energyProjectedGradient L u) := by
  have hf := ((Lp.memLp (energyValue u)).continuousLinearMap_comp L).locallyIntegrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 6)
  refine ⟨hf, (energyProjectedGradient_memLp L u).locallyIntegrable (by norm_num), ?_⟩
  intro v φ hφ hc
  have hi₁ (j : Fin 3) : Integrable (fun x => L (energyValue u x) *
      fderiv ℝ φ x (coordinate j)) volume := by
    simpa only [smul_eq_mul, mul_comm] using hf.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (compact_test_derivative_support φ hc (coordinate j))
  have hi₂ (j : Fin 3) : Integrable (fun x => L (energyGradient j u x) * φ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      (((Lp.memLp (energyGradient j u)).continuousLinearMap_comp L).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hleft (x : V) : L (energyValue u x) * fderiv ℝ φ x v =
      ∑ j : Fin 3, v j * (L (energyValue u x) * fderiv ℝ φ x (coordinate j)) := by
    conv_lhs => rw [← coordinate_reconstruct v]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul]
    ring
  have hright (x : V) : ⟪energyProjectedGradient L u x,v⟫ * φ x =
      ∑ j : Fin 3, v j * (L (energyGradient j u x) * φ x) := by
    rw [energyProjectedGradient_inner, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ (fun j _ => (hi₁ j).const_mul (v j)),
    integral_finsetSum _ (fun j _ => (hi₂ j).const_mul (v j))]
  simp only [integral_const_mul, energyState_projected_coordinate_test u _ L φ hφ hc,
    mul_neg, Finset.sum_neg_distrib]

theorem energyState_inDotH1 (u : EnergyState) :
    InDotH1 (energyValue u) (energyProjectedGradient Complex.reCLM u)
      (energyProjectedGradient Complex.imCLM u) :=
  ⟨Lp.memLp (energyValue u), energyProjectedGradient_memLp Complex.reCLM u,
    energyProjectedGradient_memLp Complex.imCLM u,
    energyState_hasWeakGradient Complex.reCLM u,
    energyState_hasWeakGradient Complex.imCLM u⟩

end HartreeF.EnergySpace
