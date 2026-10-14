import FActualFreeValueDomains
import FActualFreeRemainderInputs

/-! The eventual kinetic cap is uniform in its numerical value only.
The threshold depends on the fixed eligible depth J. Static, UNCOMPILED.
The inherited all-index headGradientCap remains separate and may grow with J. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeRemainderInputs
open EnergySpace SobolevStretch ProfileEnergy ActualStrichartz ActualFreeValue TimeHolder

/-- Every original sequence index has the inherited fixed-depth cap B_J.
This cap is allowed to grow with J and does not consume kinetic asymptotics. -/
theorem profileRemainder_free_all_index_bounds (hDensity : OrdinaryH1Density)
    {K B C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J n : ℕ) :
    mixedNorm volume volume ∞ 6
      (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)) ≤
        ENNReal.ofReal (K^(1/6 : ℝ)*headGradientCap B P J) ∧
    mixedNorm volume volume 10 10
      (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)) ≤
        ENNReal.ofReal (10*K^(1/6 : ℝ)*C*headGradientCap B P J) ∧
    ∀ k : Fin 3, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n))) ≤
        ENNReal.ofReal (C*headGradientCap B P J) := by
  have hK0 := hSob.nonneg
  have hC0 := hStr.1
  have hr : pureGradientNorm (profileRemainder hDensity hSob P u J n) ≤
      headGradientCap B P J := profileRemainder_pureGradient_bound hDensity hSob P u hB J n
  refine ⟨(profileFreeJoint_E_bound hDensity hSob _).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hSob.nonneg _))), ?_, ?_⟩
  · exact (profileFreeJoint_S_finite_and_bound hDensity hSob hStr _).2.2.2.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by positivity)))
  · intro k
    exact (freeGradient_W_bound hStr _ k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hr hStr.1))

/-- The literal remainder supplies every-index scalar E/S/W domains. -/
theorem profileRemainder_free_scalarProfile (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) (k : Fin 3) :
    GeneralProfileCross.ScalarProfile
      (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n))
      (freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n))) :=
  profileFreeJoint_scalarProfile hDensity hSob hStr _ k

/-- Kinetic decoupling produces the J-independent eventual numerical cap.
No common-in-J threshold or all-index J-independent bound is asserted. -/
theorem profileRemainder_eventually_pureGradient_le (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J : ℕ)
    (hJ : (J : WithTop ℕ) ≤ P.count) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      pureGradientNorm (profileRemainder hDensity hSob P u J n) ≤ B+η := by
  have hB0 : 0 ≤ B := (pureGradientNorm_nonneg (u 0)).trans (hB 0)
  let δ : ℝ := 2*B*η+η^2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he := (hp.kinetic J hJ).eventually
    (eventually_gt_nhds (show -δ < (0 : ℝ) by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  have hu : gradientSquared (u n) ≤ B^2 := by
    rw [← pureGradientNorm_sq]
    exact (sq_le_sq₀ (pureGradientNorm_nonneg (u n)) hB0).mpr (hB n)
  have hsum : 0 ≤ ∑ j ∈ Finset.range J, gradientSquared (P.profile j) :=
    Finset.sum_nonneg (fun j _ => gradientSquared_nonneg (P.profile j))
  have herr := hN n hn
  apply (sq_le_sq₀ (pureGradientNorm_nonneg _) (add_nonneg hB0 hη.le)).mp
  rw [pureGradientNorm_sq]
  dsimp only [δ] at herr
  nlinarith

/-- Specializing eta=1 fixes the numerical cap before a future selected J. -/
theorem profileRemainder_eventually_pureGradient_le_add_one (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J : ℕ)
    (hJ : (J : WithTop ℕ) ≤ P.count) :
    ∃ N : ℕ, ∀ n ≥ N,
      pureGradientNorm (profileRemainder hDensity hSob P u J n) ≤ B+1 :=
  profileRemainder_eventually_pureGradient_le hDensity hSob P u hp hB J hJ 1 (by norm_num)

/-- Actual free E/S/W inherit one eventual numerical cap for fixed J. -/
theorem profileRemainder_eventually_free_bounds (hDensity : OrdinaryH1Density)
    {K B C : ℝ} (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J : ℕ)
    (hJ : (J : WithTop ℕ) ≤ P.count) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      mixedNorm volume volume ∞ 6
        (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)) ≤
          ENNReal.ofReal (K^(1/6 : ℝ)*(B+η)) ∧
      mixedNorm volume volume 10 10
        (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)) ≤
          ENNReal.ofReal (10*K^(1/6 : ℝ)*C*(B+η)) ∧
      ∀ k : Fin 3, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n))) ≤
          ENNReal.ofReal (C*(B+η)) := by
  have hK0 := hSob.nonneg
  have hC0 := hStr.1
  obtain ⟨N,hN⟩ := profileRemainder_eventually_pureGradient_le hDensity hSob P u hp hB J hJ η hη
  refine ⟨N, fun n hn => ?_⟩
  refine ⟨(profileFreeJoint_E_bound hDensity hSob _).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hN n hn) (Real.rpow_nonneg hSob.nonneg _))), ?_, ?_⟩
  · exact (profileFreeJoint_S_finite_and_bound hDensity hSob hStr _).2.2.2.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hN n hn) (by positivity)))
  · intro k
    exact (freeGradient_W_bound hStr _ k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hN n hn) hStr.1))

end HartreeF.FreeRemainderInputs
