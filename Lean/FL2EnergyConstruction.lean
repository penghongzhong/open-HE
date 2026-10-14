import FEnergyStateInverse
import FullH1Embedding

/-!
Construct the concrete homogeneous energy state from an actual L2 value and
three actual L2 distributional derivatives. The value's L6 membership is
produced by ordinary H1 density and ordinary Sobolev, not assumed.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest ModulusGradient

theorem l2_schwartz_test (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) (j : Fin 3) (φ : Test) :
    (∫ x, fderiv ℝ φ x (coordinate j) * u x) = -(∫ x, φ x * g j x) := by
  have h := congrArg (fun T : TD => T φ) (hderiv j)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, neg_mul,
    integral_neg] at h
  exact neg_eq_iff_eq_neg.mp h

theorem l2_compact_test (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) (j : Fin 3) (φ : V → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, fderiv ℝ φ x (coordinate j) * u x) = -(∫ x, φ x * g j x) :=
  l2_schwartz_test u g hderiv j (hc.toSchwartzMap hφ)

theorem l2_projected_coordinate_test (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) (j : Fin 3)
    (L : ℂ →L[ℝ] ℝ) (φ : V → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ x, L (u x) * fderiv ℝ φ x (coordinate j)) = -(∫ x, L (g j x) * φ x) := by
  let ψ : V → ℂ := fun x => Complex.ofRealCLM (φ x)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hφ
  have hcψ : HasCompactSupport ψ := hc.comp_left (g := Complex.ofRealCLM) (map_zero _)
  have hd (x : V) : fderiv ℝ ψ x (coordinate j) =
      Complex.ofRealCLM (fderiv ℝ φ x (coordinate j)) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x
      ((hφ.differentiable (by simp) x).hasFDerivAt)
    change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (coordinate j) = _
    rw [h.fderiv]
    rfl
  have hi₁ : Integrable (fun x => fderiv ℝ φ x (coordinate j) • u x) volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (compact_test_derivative_support φ hc (coordinate j))
  have hi₂ : Integrable (fun x => φ x • g j x) volume :=
    ((Lp.memLp (g j)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hc
  have h := l2_compact_test u g hderiv j ψ hψ hcψ
  simp only [hd] at h
  simp only [ψ, Complex.ofRealCLM_apply, ← Complex.real_smul] at h
  have hp := congrArg L h
  rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at hp
  simpa only [map_smul, smul_eq_mul, mul_comm] using hp

def l2ProjectedGradient (L : ℂ →L[ℝ] ℝ) (g : Fin 3 → L2) (x : V) : V :=
  ∑ j : Fin 3, L (g j x) • coordinate j

theorem l2ProjectedGradient_memLp (L : ℂ →L[ℝ] ℝ) (g : Fin 3 → L2) :
    MemLp (l2ProjectedGradient L g) 2 volume := by
  apply memLp_finsetSum
  intro j _
  exact ((Lp.memLp (g j)).continuousLinearMap_comp L).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

theorem l2ProjectedGradient_inner (L : ℂ →L[ℝ] ℝ) (g : Fin 3 → L2) (x v : V) :
    ⟪l2ProjectedGradient L g x, v⟫ = ∑ j : Fin 3, L (g j x) * v j := by
  simp [l2ProjectedGradient, sum_inner, real_inner_smul_left, coordinate,
    EuclideanSpace.inner_single_left]

theorem l2_hasWeakGradient (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) (L : ℂ →L[ℝ] ℝ) :
    HasWeakGradient (fun x => L (u x)) (l2ProjectedGradient L g) := by
  have hf := ((Lp.memLp u).continuousLinearMap_comp L).locallyIntegrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨hf, (l2ProjectedGradient_memLp L g).locallyIntegrable (by norm_num), ?_⟩
  intro v φ hφ hc
  have hi₁ (j : Fin 3) : Integrable (fun x => L (u x) *
      fderiv ℝ φ x (coordinate j)) volume := by
    simpa only [smul_eq_mul, mul_comm] using hf.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (compact_test_derivative_support φ hc (coordinate j))
  have hi₂ (j : Fin 3) : Integrable (fun x => L (g j x) * φ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      (((Lp.memLp (g j)).continuousLinearMap_comp L).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hleft (x : V) : L (u x) * fderiv ℝ φ x v =
      ∑ j : Fin 3, v j * (L (u x) * fderiv ℝ φ x (coordinate j)) := by
    conv_lhs => rw [← coordinate_reconstruct v]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul]
    ring
  have hright (x : V) : ⟪l2ProjectedGradient L g x, v⟫ * φ x =
      ∑ j : Fin 3, v j * (L (g j x) * φ x) := by
    rw [l2ProjectedGradient_inner, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ (fun j _ => (hi₁ j).const_mul (v j)),
    integral_finsetSum _ (fun j _ => (hi₂ j).const_mul (v j))]
  simp only [integral_const_mul, l2_projected_coordinate_test u g hderiv _ L φ hφ hc,
    mul_neg, Finset.sum_neg_distrib]

/-- Produce L6 from the actual L2 data and their distributional derivatives. -/
theorem l2_memLp_six (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) : MemLp (u : V → ℂ) 6 volume := by
  have hr := FullH1Embedding.h1_memLp_six hDensity hSob
    ((Lp.memLp u).continuousLinearMap_comp Complex.reCLM)
    (l2ProjectedGradient_memLp Complex.reCLM g) (l2_hasWeakGradient u g hderiv Complex.reCLM)
  have hi := FullH1Embedding.h1_memLp_six hDensity hSob
    ((Lp.memLp u).continuousLinearMap_comp Complex.imCLM)
    (l2ProjectedGradient_memLp Complex.imCLM g) (l2_hasWeakGradient u g hderiv Complex.imCLM)
  have hp : MemLp (fun x => ((u x).re, (u x).im)) 6 volume :=
    memLp_prod_iff.mpr ⟨hr, hi⟩
  have hc := hp.continuousLinearMap_comp Complex.equivRealProdCLM.symm.toContinuousLinearMap
  change MemLp (fun x => Complex.equivRealProdCLM.symm ((u x).re, (u x).im)) 6 volume at hc
  simpa only [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using hc

theorem l2_toL6_distribution (u : L2) (h6 : MemLp (u : V → ℂ) 6 volume) :
    Lp.toTemperedDistribution (h6.toLp u) = Lp.toTemperedDistribution u := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h6.coeFn_toLp] with x hx
  rw [hx]

/-- Canonical energy state with L6 produced internally and the exact given L2 gradients. -/
def l2EnergyState (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) : EnergyState :=
  ⟨((l2_memLp_six hDensity hSob u g hderiv).toLp u, g),
    (mem_energySubmodule _).mpr (fun j => by
      rw [l2_toL6_distribution]
      exact hderiv j)⟩

theorem l2EnergyState_value_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) :
    (energyValue (l2EnergyState hDensity hSob u g hderiv) : V → ℂ) =ᵐ[volume] u :=
  (l2_memLp_six hDensity hSob u g hderiv).coeFn_toLp

theorem l2EnergyState_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) (j : Fin 3) :
    energyGradient j (l2EnergyState hDensity hSob u g hderiv) = g j := rfl

theorem l2EnergyState_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : L2) (g : Fin 3 → L2)
    (hderiv : ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution u) =
      Lp.toTemperedDistribution (g j)) :
    energyDistribution (l2EnergyState hDensity hSob u g hderiv) = Lp.toTemperedDistribution u :=
  l2_toL6_distribution u (l2_memLp_six hDensity hSob u g hderiv)

#print axioms l2_memLp_six
#print axioms l2EnergyState
#print axioms l2EnergyState_value_ae
#print axioms l2EnergyState_gradient
#print axioms l2EnergyState_distribution
end HartreeF.EnergySpace
