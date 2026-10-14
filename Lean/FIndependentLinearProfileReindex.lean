import FOrdinaryLinearProfileInterface

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LinearProfileIndependentReview
open ProfileEnergy EnergySpace SobolevStretch StationarySelfTest

/-- Reindex the actual scale, center and normalized-time sequences while keeping
all profiles and their active count unchanged. -/
def reindexFamily (P : LinearProfileFamily) (τ : ℕ → ℕ) : LinearProfileFamily where
  count := P.count
  profile := P.profile
  inactive_zero := P.inactive_zero
  scale := fun j n => P.scale j (τ n)
  scale_pos := fun j n => P.scale_pos j (τ n)
  center := fun j n => P.center j (τ n)
  time := fun j n => P.time j (τ n)

/-- The operation order T U is unchanged under reindexing. -/
theorem profileAtom_reindex (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (τ : ℕ → ℕ) (j n : ℕ) :
    profileAtom hDensity hSob (reindexFamily P τ) j n =
      profileAtom hDensity hSob P j (τ n) := rfl

/-- The literal finite remainder is the same actual EnergyState. -/
theorem profileRemainder_reindex (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (τ : ℕ → ℕ) (J n : ℕ) :
    profileRemainder hDensity hSob (reindexFamily P τ) (u ∘ τ) J n =
      profileRemainder hDensity hSob P u J (τ n) := rfl

/-- Every ordinary linear property survives a strictly increasing subsequence.
The smallness field remains eventual; its finite depth is chosen before its tail. -/
theorem linearProfileProperties_reindex (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {P : LinearProfileFamily} {u : ℕ → EnergyState}
    (hP : LinearProfileProperties hDensity hSob u P)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) :
    LinearProfileProperties hDensity hSob (u ∘ τ) (reindexFamily P τ) := by
  constructor
  · intro ε hε
    obtain ⟨J,N,hcount,hsmall⟩ := hP.small_remainder ε hε
    have ht : ∀ᶠ n in atTop,
        profileFreeSize hDensity hSob (profileRemainder hDensity hSob P u J (τ n)) ≤
          ENNReal.ofReal ε :=
      hτ.tendsto_atTop.eventually (eventually_atTop.mpr ⟨N,hsmall⟩)
    obtain ⟨M,hM⟩ := eventually_atTop.mp ht
    exact ⟨J,M,hcount,hM⟩
  · intro J hJ
    exact (hP.kinetic J hJ).comp hτ.tendsto_atTop
  · intro J j hj hJ k v
    exact (hP.weak_remainder J j hj hJ k v).comp hτ.tendsto_atTop
  · intro j k hj hk hjk
    exact (hP.orthogonal j k hj hk hjk).comp hτ.tendsto_atTop

/-- A preselected finite depth and eventual bound are inherited along the
energy refinement. No limsup or eventual bound is promoted to an all-n bound. -/
theorem fixed_depth_smallness_reindex (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J : ℕ) {ε : ℝ}
    (hsmall : ∀ᶠ n in atTop,
      profileFreeSize hDensity hSob (profileRemainder hDensity hSob P u J n) ≤ ENNReal.ofReal ε)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) :
    ∀ᶠ n in atTop,
      profileFreeSize hDensity hSob
        (profileRemainder hDensity hSob (reindexFamily P τ) (u ∘ τ) J n) ≤ ENNReal.ofReal ε :=
  hτ.tendsto_atTop.eventually hsmall

#print axioms reindexFamily
#print axioms profileAtom_reindex
#print axioms profileRemainder_reindex
#print axioms linearProfileProperties_reindex
#print axioms fixed_depth_smallness_reindex
end HartreeF.LinearProfileIndependentReview
