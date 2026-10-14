import FLinearProfileFrame
import FWeakGradientEnergyDual
import FEnergySmoothDensity
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest LocalRellich
attribute [local irreducible] energySubmodule

/-- The actual homogeneous gradient embedding into a complex Hilbert product. -/
def homogeneousGradient : EnergyState →L[ℂ] PiLp 2 (fun _ : Fin 3 => L2) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => L2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi energyGradient)

theorem homogeneousGradient_eq (u : EnergyState) : homogeneousGradient u=gradientVector u := rfl

theorem homogeneousGradient_norm (u : EnergyState) : ‖homogeneousGradient u‖=pureGradientNorm u :=
  (pureGradientNorm_eq_norm_gradientVector u).symm

/-- Sobolev eliminates the homogeneous kernel and gives a closed gradient range. -/
theorem homogeneousGradient_antilipschitz {K : ℝ} (hSob : OrdinarySobolev K) :
    AntilipschitzWith ⟨max (K^((6:ℝ)⁻¹)) 1, le_trans zero_le_one (le_max_right _ _)⟩ homogeneousGradient := by
  apply AntilipschitzWith.of_le_mul_dist
  intro u v
  simp only [dist_eq_norm, ← map_sub, homogeneousGradient_norm]
  exact energyState_le_pureGradient hSob (u-v)

theorem homogeneousGradient_closedRange {K : ℝ} (hSob : OrdinarySobolev K) :
    IsClosed (Set.range homogeneousGradient) :=
  (homogeneousGradient_antilipschitz hSob).isClosed_range homogeneousGradient.uniformContinuous

/-- A literal Hilbert realization of dotH1, rather than a new norm imposed on
EnergyState or a scalar-L2 completion. -/
abbrev HomogeneousProfileSpace := homogeneousGradient.range

theorem homogeneousProfile_complete {K : ℝ} (hSob : OrdinarySobolev K) :
    CompleteSpace HomogeneousProfileSpace :=
  (homogeneousGradient_closedRange hSob).completeSpace_coe

def homogeneousProfileEquiv {K : ℝ} (hSob : OrdinarySobolev K) :
    EnergyState ≃L[ℂ] HomogeneousProfileSpace := by
  let e : EnergyState ≃ₗ[ℂ] HomogeneousProfileSpace :=
    LinearEquiv.ofInjective homogeneousGradient.toLinearMap (homogeneousGradient_antilipschitz hSob).injective
  have hb (v : HomogeneousProfileSpace) : ‖e.symm v‖ ≤ max (K^((6:ℝ)⁻¹)) 1*‖v‖ := by
    have he : homogeneousGradient (e.symm v)=(v : PiLp 2 (fun _ : Fin 3 => L2)) :=
      congrArg Subtype.val (e.apply_symm_apply v)
    have h := energyState_le_pureGradient hSob (e.symm v)
    rwa [← homogeneousGradient_norm, he] at h
  exact { toLinearEquiv := e
          continuous_toFun := homogeneousGradient.continuous.subtype_mk _
          continuous_invFun := (e.symm.toLinearMap.mkContinuous (max (K^((6:ℝ)⁻¹)) 1) hb).continuous }

theorem homogeneousProfileEquiv_norm {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ‖homogeneousProfileEquiv hSob u‖=pureGradientNorm u := homogeneousGradient_norm u

/-- Native compact-smooth density identifies the closed gradient range as the
homogeneous completion to which the published linear theorem applies. -/
theorem homogeneousProfile_compactSmooth_denseRange (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) :
    DenseRange (fun phi : CompactSmoothReal × CompactSmoothReal =>
      homogeneousProfileEquiv hSob (compactSmoothState phi)) := by
  intro v
  obtain ⟨phi,hphi⟩ := compactSmoothState_approximation hDensity hSob ((homogeneousProfileEquiv hSob).symm v)
  have ht := (homogeneousProfileEquiv hSob).continuous.tendsto _ |>.comp hphi
  rw [(homogeneousProfileEquiv hSob).apply_symm_apply] at ht
  exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n => mem_range_self (phi n)))

/-- Exact weak-topology transfer to the actual homogeneous realization. -/
theorem gradientWeakLimit_iff_homogeneous_dual {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℕ → EnergyState} {f : EnergyState} :
    GradientWeakLimit u f ↔
      ∀ L : HomogeneousProfileSpace →L[ℝ] ℝ,
        Tendsto (fun n => L (homogeneousProfileEquiv hSob (u n))) atTop
          (𝓝 (L (homogeneousProfileEquiv hSob f))) := by
  constructor
  · intro hw L
    exact energyState_dual_tendsto_of_gradient_weak hSob hw
      (L.comp ((homogeneousProfileEquiv hSob).toContinuousLinearMap.restrictScalars ℝ))
  · intro hw j v
    let L : EnergyState →L[ℝ] ℝ := (innerSL ℝ v).comp ((energyGradient j).restrictScalars ℝ)
    have ht := hw (L.comp ((homogeneousProfileEquiv hSob).symm.toContinuousLinearMap.restrictScalars ℝ))
    change Tendsto (fun n => L ((homogeneousProfileEquiv hSob).symm
      (homogeneousProfileEquiv hSob (u n)))) atTop
      (𝓝 (L ((homogeneousProfileEquiv hSob).symm (homogeneousProfileEquiv hSob f)))) at ht
    simp only [ContinuousLinearEquiv.symm_apply_apply] at ht
    change Tendsto (fun n => inner ℝ v (energyGradient j (u n))) atTop
      (𝓝 (inner ℝ v (energyGradient j f))) at ht
    simpa only [real_inner_comm] using ht

#print axioms homogeneousGradient
#print axioms homogeneousGradient_eq
#print axioms homogeneousGradient_norm
#print axioms homogeneousGradient_antilipschitz
#print axioms homogeneousGradient_closedRange
#print axioms HomogeneousProfileSpace
#print axioms homogeneousProfile_complete
#print axioms homogeneousProfileEquiv
#print axioms homogeneousProfileEquiv_norm
#print axioms homogeneousProfile_compactSmooth_denseRange
#print axioms gradientWeakLimit_iff_homogeneous_dual
end HartreeF.ProfileEnergy
