import FEnergyGradientTopology
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch
attribute [local irreducible] energySubmodule

/-- Sobolev norm equivalence, Hahn-Banach and Hilbert Riesz identify every
actual EnergyState functional with three actual coordinate-L2 tests. -/
theorem energyState_dual_gradient_representation {K : ℝ} (hSob : OrdinarySobolev K)
    (L : EnergyState →L[ℝ] ℝ) :
    ∃ w : Fin 3 → L2, ∀ u : EnergyState,
      L u = ∑ j : Fin 3, inner ℝ (energyGradient j u) (w j) := by
  let H := PiLp 2 (fun _ : Fin 3 => L2)
  let G : EnergyState →ₗ[ℝ] H := gradientVector.restrictScalars ℝ
  have hG : Function.Injective G := by
    intro u v huv
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have he : gradientVector (u-v)=0 := by
      change G (u-v)=0
      rw [map_sub, huv, sub_self]
    have hb := energyState_le_pureGradient hSob (u-v)
    rwa [pureGradientNorm_eq_norm_gradientVector, he, norm_zero, mul_zero] at hb
  let e : EnergyState ≃ₗ[ℝ] G.range := LinearEquiv.ofInjective G hG
  have hnorm (x : G.range) : ‖e.symm x‖ ≤ max (K^((6:ℝ)⁻¹)) 1*‖x‖ := by
    have he : gradientVector (e.symm x)=(x:H) :=
      congrArg Subtype.val (e.apply_symm_apply x)
    have hb := energyState_le_pureGradient hSob (e.symm x)
    rwa [pureGradientNorm_eq_norm_gradientVector, he] at hb
  let J : G.range →L[ℝ] EnergyState := e.symm.toLinearMap.mkContinuous (max (K^((6:ℝ)⁻¹)) 1) hnorm
  obtain ⟨M,hM,_⟩ := exists_extension_norm_eq G.range (L.comp J)
  let w : H := (InnerProductSpace.toDual ℝ H).symm M
  have hMu (u : EnergyState) : M (G u)=L u := by
    have hh := hM (e u)
    change M (G u)=L (e.symm (e u)) at hh
    simpa only [e.symm_apply_apply] using hh
  refine ⟨fun j => w j, fun u => ?_⟩
  calc
    L u = M (G u) := (hMu u).symm
    _ = inner ℝ w (G u) := (InnerProductSpace.toDual_symm_apply).symm
    _ = ∑ j : Fin 3, inner ℝ (energyGradient j u) (w j) := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      exact real_inner_comm _ _

/-- The precise native weak topology bridge. No weak-value or local strong
convergence hypothesis is inserted. -/
theorem energyState_dual_tendsto_of_gradient_weak {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℕ → EnergyState} {f : EnergyState}
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v)))
    (L : EnergyState →L[ℝ] ℝ) :
    Tendsto (fun n => L (u n)) atTop (𝓝 (L f)) := by
  obtain ⟨w,hw⟩ := energyState_dual_gradient_representation hSob L
  simpa only [hw] using tendsto_finsetSum Finset.univ (fun j _ => hweak j (w j))

#print axioms energyState_dual_gradient_representation
#print axioms energyState_dual_tendsto_of_gradient_weak
end HartreeF.LocalRellich
