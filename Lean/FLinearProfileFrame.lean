import FEnergyFreeProperties
import FCriticalAffineIsometry
import FOneProfileEnergySplit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine EnergyVariation StateEnergy ForcingDomain
attribute [local irreducible] energySubmodule

/-- The literal coordinate-L2 weak topology, not weak scalar-L6 input. -/
def GradientWeakLimit (u : ℕ → EnergyState) (f : EnergyState) : Prop :=
  ∀ j : Fin 3, ∀ v : L2, Tendsto (fun n => inner ℝ (energyGradient j (u n)) v)
    atTop (𝓝 (inner ℝ (energyGradient j f) v))

def freeEnergyEquiv (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (s : ℝ) : EnergyState ≃L[ℂ] EnergyState where
  toLinearEquiv :=
    { toFun := freeEnergyState hDensity hSob s
      invFun := freeEnergyState hDensity hSob (-s)
      left_inv := fun u => by simpa only [neg_neg] using freeEnergyState_inverse hDensity hSob (-s) u
      right_inv := freeEnergyState_inverse hDensity hSob s
      map_add' := freeEnergyState_add hDensity hSob s
      map_smul' := freeEnergyState_smul hDensity hSob s }
  continuous_toFun := freeEnergyState_continuous hDensity hSob s
  continuous_invFun := freeEnergyState_continuous hDensity hSob (-s)

/-- Killip–Visan (4.61) order: T(lambda,y) followed after U(s).
No affine/free commutation or PDE covariance is used. -/
def linearProfileFrame (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) :
    EnergyState ≃L[ℂ] EnergyState :=
  (freeEnergyEquiv hDensity hSob s).trans
    (criticalAffineState lambda hlambda y).toContinuousLinearEquiv

theorem linearProfileFrame_apply (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u : EnergyState) :
    linearProfileFrame hDensity hSob lambda hlambda y s u =
      criticalAffineState lambda hlambda y (freeEnergyState hDensity hSob s u) := rfl

theorem linearProfileFrame_symm_apply (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u : EnergyState) :
    (linearProfileFrame hDensity hSob lambda hlambda y s).symm u =
      freeEnergyState hDensity hSob (-s) ((criticalAffineState lambda hlambda y).symm u) := rfl

theorem linearProfileFrame_gradientSquared (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u : EnergyState) :
    gradientSquared (linearProfileFrame hDensity hSob lambda hlambda y s u)=gradientSquared u := by
  rw [linearProfileFrame_apply, criticalAffineState_gradientSquared, freeEnergyState_gradientSquared]

theorem linearProfileFrame_pureGradientNorm (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u : EnergyState) :
    pureGradientNorm (linearProfileFrame hDensity hSob lambda hlambda y s u)=pureGradientNorm u := by
  simp only [pureGradientNorm, linearProfileFrame_gradientSquared]

theorem linearProfileFrame_totalEnergy (hDensity : OrdinaryH1Density) {K alpha : ℝ} (hSob : OrdinarySobolev K)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u : EnergyState) :
    totalEnergy alpha (linearProfileFrame hDensity hSob lambda hlambda y s u)=
      totalEnergy alpha (freeEnergyState hDensity hSob s u) := by
  rw [linearProfileFrame_apply, criticalAffineState_totalEnergy hOrd]

/-- Actual pure-gradient inner pairing. -/
def gradientPair (u v : EnergyState) : ℝ :=
  ∑ j : Fin 3, inner ℝ (energyGradient j u) (energyGradient j v)

theorem gradientSquared_add_pair (u v : EnergyState) :
    gradientSquared (u+v)=gradientSquared u+gradientSquared v+2*gradientPair u v := by
  simp only [gradientSquared, gradientPair, map_add, norm_add_sq_real, Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem gradientSquared_sub_pair (u v : EnergyState) :
    gradientSquared u-gradientSquared (u-v)-gradientSquared v =
      2*(gradientPair u v-gradientSquared v) := by
  simp only [gradientSquared, gradientPair, map_sub, norm_sub_sq_real, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem linearProfileFrame_gradientPair (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (u v : EnergyState) :
    gradientPair (linearProfileFrame hDensity hSob lambda hlambda y s u)
      (linearProfileFrame hDensity hSob lambda hlambda y s v)=gradientPair u v := by
  have h := linearProfileFrame_gradientSquared hDensity hSob lambda hlambda y s (u+v)
  rw [map_add, gradientSquared_add_pair, gradientSquared_add_pair,
    linearProfileFrame_gradientSquared, linearProfileFrame_gradientSquared] at h
  linarith

/-- Even at divergent normalized times, the kinetic cross term is proved from
the actual full inverse-frame weak limit, not from interaction decay. -/
theorem linearProfileFrame_kinetic_split (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    {u : ℕ → EnergyState} (phi : EnergyState)
    (hw : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)).symm (u n)) phi) :
    Tendsto (fun n => gradientSquared (u n)-gradientSquared
      (u n-linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n) phi)-gradientSquared phi)
      atTop (𝓝 0) := by
  let A (n : ℕ) := linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)
  have hp (n : ℕ) : gradientPair (u n) (A n phi)=gradientPair ((A n).symm (u n)) phi := by
    have hh := linearProfileFrame_gradientPair hDensity hSob (lambda n) (hlambda n) (y n) (s n)
      ((A n).symm (u n)) phi
    change gradientPair (A n ((A n).symm (u n))) (A n phi)=gradientPair ((A n).symm (u n)) phi at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have ht : Tendsto (fun n => gradientPair ((A n).symm (u n)) phi) atTop (𝓝 (gradientSquared phi)) := by
    simpa only [gradientPair, gradientSquared, real_inner_self_eq_norm_sq] using
      tendsto_finsetSum Finset.univ (fun j _ => hw j (energyGradient j phi))
  have he (n : ℕ) : gradientSquared (u n)-gradientSquared (u n-A n phi)-gradientSquared phi =
      2*(gradientPair ((A n).symm (u n)) phi-gradientSquared phi) := by
    have hh := gradientSquared_sub_pair (u n) (A n phi)
    rw [linearProfileFrame_gradientSquared, hp] at hh
    exact hh
  change Tendsto (fun n => gradientSquared (u n)-gradientSquared (u n-A n phi)-gradientSquared phi)
    atTop (𝓝 0)
  simpa only [he, sub_self, mul_zero] using (ht.sub_const (gradientSquared phi)).const_mul 2

#print axioms GradientWeakLimit
#print axioms freeEnergyEquiv
#print axioms linearProfileFrame
#print axioms linearProfileFrame_apply
#print axioms linearProfileFrame_symm_apply
#print axioms linearProfileFrame_gradientSquared
#print axioms linearProfileFrame_pureGradientNorm
#print axioms linearProfileFrame_totalEnergy
#print axioms gradientSquared_add_pair
#print axioms gradientSquared_sub_pair
#print axioms linearProfileFrame_gradientPair
#print axioms linearProfileFrame_kinetic_split
end HartreeF.ProfileEnergy
