import FStateEnergyCalculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.StateEnergy
open EnergySpace EnergyVariation ForcingDomain

attribute [local irreducible] energySubmodule

theorem totalEnergy_eq_original (α : ℝ) (u : EnergyState) :
    totalEnergy α u = DirectionalCoercivity.energy α (energyValue u)
      (energyProjectedGradient Complex.reCLM u)
      (energyProjectedGradient Complex.imCLM u) :=
  totalEnergy_eq_literal α u

/-- A genuine bounded linear regularization of any strongly differentiable
curve is a consumer. This does not assert differentiability of a mild orbit. -/
theorem totalEnergy_regularized_curve {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (P : E →L[ℝ] EnergyState)
    {v : ℝ → E} {dv : E} {t : ℝ} (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => DirectionalCoercivity.energy α (energyValue (P (v s)))
      (energyProjectedGradient Complex.reCLM (P (v s)))
      (energyProjectedGradient Complex.imCLM (P (v s))))
      ((∑ j : Fin 3, inner ℝ (energyGradient j (P (v t)))
        (energyGradient j (P dv))) -
        (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α)
          (energyValue (P (v t))) x) * energyValue (P dv) x).re) t := by
  simpa only [← totalEnergy_eq_original, Function.comp_def] using
    totalEnergy_curve_hasDerivAt hH (P.hasFDerivAt.comp_hasDerivAt t hv)

/-- Endpoint energy passage along actual canonical EnergyState approximation. -/
theorem totalEnergy_endpoint_limit {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u : ℕ → ℝ → EnergyState} {v : ℝ → EnergyState} {a b : ℝ}
    (ha : Tendsto (fun n => u n a) atTop (𝓝 (v a)))
    (hb : Tendsto (fun n => u n b) atTop (𝓝 (v b)))
    (he : Tendsto (fun n => totalEnergy α (u n b) - totalEnergy α (u n a))
      atTop (𝓝 0)) : totalEnergy α (v b) = totalEnergy α (v a) := by
  have h := (totalEnergy_tendsto hH hb).sub (totalEnergy_tendsto hH ha)
  exact sub_eq_zero.mp (tendsto_nhds_unique h he)

/-- The exact Hamiltonian cancellation; the residual is kept as a genuine
difference vector. No norm estimate replaces it before cancellation. -/
theorem hamiltonian_residual_identity (A R : EnergySpace.L2) :
    -(inner ℂ A (Complex.I • (A + R))).re =
      -(inner ℂ A (Complex.I • R)).re := by
  rw [smul_add, inner_add_right, Complex.add_re]
  have hz : (inner ℂ A (Complex.I • A)).re = 0 := by
    rw [inner_smul_right]
    simp [← Complex.ofReal_pow]
  rw [hz, zero_add]

theorem hamiltonian_residual_norm_bound (A R : EnergySpace.L2) :
    |(inner ℂ A (Complex.I • (A + R))).re| ≤ ‖A‖ * ‖R‖ := by
  have he := hamiltonian_residual_identity A R
  have h : (inner ℂ A (Complex.I • (A + R))).re =
      (inner ℂ A (Complex.I • R)).re := neg_injective he
  rw [h]
  calc
    _ ≤ ‖inner ℂ A (Complex.I • R)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖A‖ * ‖Complex.I • R‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]

#print axioms totalEnergy_eq_original
#print axioms totalEnergy_regularized_curve
#print axioms totalEnergy_endpoint_limit
#print axioms hamiltonian_residual_identity
#print axioms hamiltonian_residual_norm_bound
end HartreeF.StateEnergy
