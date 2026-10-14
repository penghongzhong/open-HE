import FHomogeneousProfileRealization
import FEnergyCriticalTimeConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest CriticalTimeSobolev
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- A genuine jointly measurable representative of the actual free orbit. -/
def profileFreeJoint (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : ℝ → Space → ℂ :=
  (energyJointFields volume (fun t : ℝ => freeEnergyState hDensity hSob t u)
    (freeEnergyState_time_continuous hDensity hSob u).stronglyMeasurable.aestronglyMeasurable).u

theorem profileFreeJoint_measurable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : StronglyMeasurable (fun z : ℝ × Space => profileFreeJoint hDensity hSob u z.1 z.2) :=
  (energyJointFields volume (fun t : ℝ => freeEnergyState hDensity hSob t u)
    (freeEnergyState_time_continuous hDensity hSob u).stronglyMeasurable.aestronglyMeasurable).joint_u

theorem profileFreeJoint_slice (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : ∀ᵐ t ∂(volume : Measure ℝ),
    profileFreeJoint hDensity hSob u t =ᵐ[volume] (energyValue (freeEnergyState hDensity hSob t u) : Space → ℂ) :=
  (energyJointFields volume (fun t : ℝ => freeEnergyState hDensity hSob t u)
    (freeEnergyState_time_continuous hDensity hSob u).stronglyMeasurable.aestronglyMeasurable).slice_eq.mono
      (fun _ h => h.1)

/-- Literal spacetime L10 from the source, retaining infinity and the actual
joint representative. No unproved mixed/product-norm equality is inserted. -/
def profileFreeSize (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : ℝ≥0∞ :=
  eLpNorm (fun z : ℝ × Space => profileFreeJoint hDensity hSob u z.1 z.2) 10 (volume.prod volume)

/-- Source labels are active exactly when j<count. Finite families are padded
by zero profiles, with no weak/separation condition asserted on inactive labels. -/
structure LinearProfileFamily where
  count : WithTop ℕ
  profile : ℕ → EnergyState
  inactive_zero : ∀ j : ℕ, ¬(j : WithTop ℕ)<count → profile j=0
  scale : ℕ → ℕ → ℝ
  scale_pos : ∀ j n, 0 < scale j n
  center : ℕ → ℕ → Space
  time : ℕ → ℕ → ℝ

def profileAtom (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (j n : ℕ) : EnergyState :=
  linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n) (P.profile j)

def profileRemainder (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) : EnergyState :=
  u n-∑ j ∈ Finset.range J, profileAtom hDensity hSob P j n

theorem profileRemainder_zero (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (n : ℕ) :
    profileRemainder hDensity hSob P u 0 n=u n := by simp [profileRemainder]

theorem profileRemainder_reconstruction (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) :
    u n=(∑ j ∈ Finset.range J, profileAtom hDensity hSob P j n)+profileRemainder hDensity hSob P u J n := by
  simp only [profileRemainder]
  abel

theorem profileRemainder_succ (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) :
    profileRemainder hDensity hSob P u (J+1) n=
      profileRemainder hDensity hSob P u J n-profileAtom hDensity hSob P J n := by
  simp only [profileRemainder, Finset.sum_range_succ]
  abel

theorem profileAtom_inactive (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (j n : ℕ) (hj : ¬(j : WithTop ℕ)<P.count) :
    profileAtom hDensity hSob P j n=0 := by
  simp only [profileAtom, P.inactive_zero j hj, map_zero]

/-- After a finite terminal count, the concrete residual is literally frozen. -/
theorem profileRemainder_finite_padding (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (N J n : ℕ)
    (hcount : P.count=(N : WithTop ℕ)) (hNJ : N≤J) :
    profileRemainder hDensity hSob P u J n=profileRemainder hDensity hSob P u N n := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hNJ
  clear hNJ
  induction d with
  | zero => simp
  | succ d hd =>
    rw [Nat.add_succ, profileRemainder_succ]
    have hi : ¬((N+d : ℕ) : WithTop ℕ)<P.count := by
      rw [hcount]
      exact not_lt.mpr (by exact_mod_cast Nat.le_add_right N d)
    rw [profileAtom_inactive hDensity hSob P (N+d) n hi, sub_zero, hd]

/-- Every finite residual inherits an actual pure-gradient bound from exact
reconstruction and the frame isometry, before any nonlinear conclusion. -/
theorem profileRemainder_pureGradient_bound (hDensity : OrdinaryH1Density) {K B : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n)≤B) (J n : ℕ) :
    pureGradientNorm (profileRemainder hDensity hSob P u J n)≤
      B+∑ j ∈ Finset.range J, pureGradientNorm (P.profile j) := by
  calc
    pureGradientNorm (profileRemainder hDensity hSob P u J n)
        = ‖gradientVector (u n)-∑ j ∈ Finset.range J,
          gradientVector (profileAtom hDensity hSob P j n)‖ := by
            simp only [profileRemainder, pureGradientNorm_eq_norm_gradientVector, map_sub, map_sum]
    _ ≤ ‖gradientVector (u n)‖+‖∑ j ∈ Finset.range J,
          gradientVector (profileAtom hDensity hSob P j n)‖ := norm_sub_le _ _
    _ ≤ B+∑ j ∈ Finset.range J, ‖gradientVector (profileAtom hDensity hSob P j n)‖ :=
      add_le_add (by simpa only [← pureGradientNorm_eq_norm_gradientVector] using hB n)
        (norm_sum_le _ _)
    _ = B+∑ j ∈ Finset.range J, pureGradientNorm (P.profile j) := by
      simp only [← pureGradientNorm_eq_norm_gradientVector, profileAtom,
        linearProfileFrame_pureGradientNorm]

/-- Ordinary linear extraction only, specialized to the natively identified
homogeneous realization. Killip–Visan Theorem 4.27, (4.61)–(4.65): published
p.374/PDF381; author pp.50–51/PDF49–50. The epsilon/tail remainder conclusion is
a weaker consequence of (4.62). If count is finite, its selected depth must be
the terminal count (including count=0); otherwise some finite depth is selected.
There is no Hartree energy, nonlinear residual, wave operator or scattering field. -/
structure LinearProfileProperties (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : ℕ → EnergyState) (P : LinearProfileFamily) : Prop where
  small_remainder : ∀ ε : ℝ, 0 < ε → ∃ J N : ℕ,
    (P.count=⊤ ∨ P.count=(J : WithTop ℕ)) ∧
    ∀ n ≥ N, profileFreeSize hDensity hSob (profileRemainder hDensity hSob P u J n) ≤ ENNReal.ofReal ε
  kinetic : ∀ J : ℕ, (J : WithTop ℕ)≤P.count →
    Tendsto (fun n => gradientSquared (u n)-(∑ j ∈ Finset.range J, gradientSquared (P.profile j))-
      gradientSquared (profileRemainder hDensity hSob P u J n)) atTop (𝓝 0)
  weak_remainder : ∀ J j : ℕ, j<J → (J : WithTop ℕ)≤P.count →
    GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)).symm
        (profileRemainder hDensity hSob P u J n)) 0
  orthogonal : ∀ j k : ℕ, (j : WithTop ℕ)<P.count → (k : WithTop ℕ)<P.count → j≠k →
    Tendsto (fun n => P.scale j n/P.scale k n+P.scale k n/P.scale j n+
      ‖P.center j n-P.center k n‖^2/(P.scale j n*P.scale k n)+
      |P.time j n*(P.scale j n)^2-P.time k n*(P.scale k n)^2|/(P.scale j n*P.scale k n)) atTop atTop

/-- The sole new ordinary-analysis premise is published linear extraction on
the actual homogeneous realization. All subsequent Hartree claims are native. -/
structure OrdinaryLinearProfileExtraction (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) : Prop where
  extract : ∀ (u : ℕ → EnergyState) (B : ℝ), (∀ n, pureGradientNorm (u n) ≤ B) →
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ P : LinearProfileFamily,
      LinearProfileProperties hDensity hSob (u ∘ σ) P

/-- The per-stage profile weak limit is a native consequence of exact
reconstruction and the source weak-zero statement at the next remainder. -/
theorem profileRemainder_stage_weak (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (j : ℕ)
    (hw : GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)).symm
        (profileRemainder hDensity hSob P u (j+1) n)) 0) :
    GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)).symm
        (profileRemainder hDensity hSob P u j n)) (P.profile j) := by
  let A (n : ℕ) := linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)
  have he (n : ℕ) : (A n).symm (profileRemainder hDensity hSob P u j n)=
      (A n).symm (profileRemainder hDensity hSob P u (j+1) n)+P.profile j := by
    have hr : profileRemainder hDensity hSob P u j n=
        profileRemainder hDensity hSob P u (j+1) n+A n (P.profile j) := by
      rw [profileRemainder_succ]
      change _=(_-A n (P.profile j))+A n (P.profile j)
      abel
    rw [hr, map_add, ContinuousLinearEquiv.symm_apply_apply]
  intro k v
  have ht := (hw k v).add_const (inner ℝ (energyGradient k (P.profile j)) v)
  simp only [map_zero, inner_zero_left, zero_add] at ht
  change Tendsto (fun n => inner ℝ (energyGradient k ((A n).symm (profileRemainder hDensity hSob P u j n))) v)
    atTop (𝓝 (inner ℝ (energyGradient k (P.profile j)) v))
  simpa only [he, map_add, inner_add_left] using ht

#print axioms profileFreeJoint
#print axioms profileFreeJoint_measurable
#print axioms profileFreeJoint_slice
#print axioms profileFreeSize
#print axioms LinearProfileFamily
#print axioms profileRemainder_zero
#print axioms profileRemainder_reconstruction
#print axioms profileRemainder_succ
#print axioms profileAtom_inactive
#print axioms profileRemainder_finite_padding
#print axioms profileRemainder_pureGradient_bound
#print axioms LinearProfileProperties
#print axioms OrdinaryLinearProfileExtraction
#print axioms profileRemainder_stage_weak
end HartreeF.ProfileEnergy
