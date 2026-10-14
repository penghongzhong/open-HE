import FEnergyStateInverse
import DirectionalKineticPositive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.EnergySpace
open SobolevStretch

/-- The sum of the squared actual complex L2 coordinate-gradient norms. -/
def gradientSquared (u : EnergyState) : ℝ := ∑ j : Fin 3, ‖energyGradient j u‖^2

/-- The Euclidean pure-gradient norm, with no L2 requirement on the value. -/
def pureGradientNorm (u : EnergyState) : ℝ := Real.sqrt (gradientSquared u)

theorem gradientSquared_nonneg (u : EnergyState) : 0 ≤ gradientSquared u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem pureGradientNorm_nonneg (u : EnergyState) : 0 ≤ pureGradientNorm u :=
  Real.sqrt_nonneg _

theorem pureGradientNorm_sq (u : EnergyState) : pureGradientNorm u ^ 2 = gradientSquared u :=
  Real.sq_sqrt (gradientSquared_nonneg u)

/-- Exact Re/Im assembly. Complex coordinate modulus already includes both parts. -/
theorem state_complexGradient_coordinate (u : EnergyState) (x : V) (j : Fin 3) :
    complexGradient (energyProjectedGradient Complex.reCLM u)
      (energyProjectedGradient Complex.imCLM u) x j = energyGradient j u x := by
  have hre := energyProjectedGradient_coordinate Complex.reCLM u x j
  have him := energyProjectedGradient_coordinate Complex.imCLM u x j
  simp only [coordinate, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  apply Complex.ext <;> simp [complexGradient, hre, him]

/-- A finite Lp norm's natural power is its genuine integral. -/
theorem energyLp_norm_pow {n : ℕ} (hn : n ≠ 0) [Fact ((1 : ℝ≥0∞) ≤ n)]
    (f : Lp ℂ n (volume : Measure V)) : ‖f‖^n = ∫ x, ‖f x‖^n := by
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnonneg : 0 ≤ ∫ x, ‖f x‖^n := integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _)
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by simpa using hn)
    (by simp) (Lp.memLp f)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
    ← Real.rpow_natCast, ← Real.rpow_mul hnonneg, inv_mul_cancel₀ hnn.ne', Real.rpow_one]

/-- The reconstructed full complex kinetic energy equals the coordinate L2 sum exactly. -/
theorem state_kinetic_eq_gradientSquared (u : EnergyState) :
    kinetic (energyProjectedGradient Complex.reCLM u)
      (energyProjectedGradient Complex.imCLM u) = gradientSquared u := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  unfold kinetic
  simp only [EuclideanSpace.norm_sq_eq, state_complexGradient_coordinate]
  rw [integral_finsetSum _ (fun j _ =>
    (Lp.memLp (energyGradient j u)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))]
  unfold gradientSquared
  exact Finset.sum_congr rfl (fun j _ => (energyLp_norm_pow (n := 2) (by decide) (energyGradient j u)).symm)

/-- Ordinary Sobolev is consumed on the C43-produced genuine weak-gradient domain. -/
theorem energyValue_sixth_bound {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ‖energyValue u‖^6 ≤ K * gradientSquared u ^ 3 := by
  let : Fact ((1 : ℝ≥0∞) ≤ (6 : ℕ)) := ⟨by norm_num⟩
  have h := hSob.bound (energyState_inDotH1 u)
  rw [state_kinetic_eq_gradientSquared, ← energyLp_norm_pow (n := 6) (by decide) (energyValue u)] at h
  exact h

/-- Exact conversion from the sixth-mass Sobolev constant, including K = 0. -/
theorem energyValue_le_pureGradient {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ‖energyValue u‖ ≤ K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u := by
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (energyValue u)) 6)
    (energyValue_sixth_bound hSob u) (by positivity : 0 ≤ (6 : ℝ)⁻¹)
  rw [Real.mul_rpow hSob.nonneg (pow_nonneg (gradientSquared_nonneg u) 3)] at h
  have hl : (‖energyValue u‖^6) ^ ((6 : ℝ)⁻¹) = ‖energyValue u‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hr : (gradientSquared u ^ 3) ^ ((6 : ℝ)⁻¹) = pureGradientNorm u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (gradientSquared_nonneg u)]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  rwa [hl, hr] at h

theorem energyGradient_le_pureGradient (u : EnergyState) (j : Fin 3) :
    ‖energyGradient j u‖ ≤ pureGradientNorm u := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖energyGradient k u‖) (Finset.mem_univ j)

theorem coordinateMax_le_pureGradient (u : EnergyState) :
    ‖u.val.2‖ ≤ pureGradientNorm u :=
  (pi_norm_le_iff_of_nonneg (pureGradientNorm_nonneg u)).mpr
    (energyGradient_le_pureGradient u)

/-- The C43 subtype inherits exactly the max graph norm. -/
theorem energyState_norm_eq_max (u : EnergyState) :
    ‖u‖ = max ‖energyValue u‖ ‖u.val.2‖ := rfl

/-- The Euclidean-versus-coordinate-max constant is sqrt(3), not 1. -/
theorem pureGradient_le_sqrt_three_coordinateMax (u : EnergyState) :
    pureGradientNorm u ≤ Real.sqrt 3 * ‖u.val.2‖ := by
  have hb : gradientSquared u ≤ 3 * ‖u.val.2‖^2 := by
    calc
      gradientSquared u ≤ ∑ _j : Fin 3, ‖u.val.2‖^2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_le_pi_norm u.val.2 j) 2)
      _ = _ := by simp
  calc
    pureGradientNorm u ≤ Real.sqrt (3 * ‖u.val.2‖^2) := Real.sqrt_le_sqrt hb
    _ = _ := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]

theorem pureGradient_le_sqrt_three_energyState (u : EnergyState) :
    pureGradientNorm u ≤ Real.sqrt 3 * ‖u‖ :=
  (pureGradient_le_sqrt_three_coordinateMax u).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _))

/-- Quantitative domination of the actual graph norm by its pure-gradient norm. -/
theorem energyState_le_pureGradient {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ‖u‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm u := by
  rw [energyState_norm_eq_max]
  apply max_le
  · exact (energyValue_le_pureGradient hSob u).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pureGradientNorm_nonneg u))
  · calc
      ‖u.val.2‖ ≤ pureGradientNorm u := coordinateMax_le_pureGradient u
      _ = 1 * pureGradientNorm u := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pureGradientNorm_nonneg u)

/-- Both inequalities concern the existing C43 norm and literal coordinate-gradient data. -/
theorem energyState_pureGradient_equivalence {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) :
    pureGradientNorm u ≤ Real.sqrt 3 * ‖u‖ ∧
    ‖u‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm u :=
  ⟨pureGradient_le_sqrt_three_energyState u, energyState_le_pureGradient hSob u⟩

/-- Sobolev removes the kernel of the pure-gradient seminorm on this actual domain. -/
theorem pureGradientNorm_eq_zero_iff {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : pureGradientNorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [h, mul_zero] using energyState_le_pureGradient hSob u)
      (norm_nonneg _)
  · rintro rfl
    simp [pureGradientNorm, gradientSquared]

end HartreeF.EnergySpace
