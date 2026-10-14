import FActualForcedEndpointDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder CriticalSourceBounds
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap criticalPathIntervalSource
  CompatibleL1IntervalSource.retardedCriticalPath

/-- Finite arithmetic is isolated from the dependent path objects. -/
theorem ofReal_sum_three {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (ENNReal.ofReal x + ENNReal.ofReal y) + ENNReal.ofReal z =
      ENNReal.ofReal (x+y+z) := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) hz]

theorem three_ofReal_sum {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3*((ENNReal.ofReal x+ENNReal.ofReal y)+ENNReal.ofReal z) =
      ENNReal.ofReal (3*(x+y+z)) := by
  rw [ofReal_sum_three hx hy hz, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ENNReal.ofReal_ofNat]

/-- The actual graph norm, Euclidean endpoint gradient, and scalar critical
mixed norm of the same difference. No independent norm variables occur. -/
def fullZSDifferenceSize {a b : ℝ} (u q : CriticalPath (intervalMeasure a b)) : ℝ≥0∞ :=
  ENNReal.ofReal ‖u-q‖ + mixedNorm (intervalMeasure a b) volume 2 6
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) +
    mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x)

/-- Quantitative full-Z+S small-interval stability for the original scalar-L1,
gradient-L2 forced mild identity. The radius and constant precede the interval,
data, approximate path, and error. All smallness/source estimates are produced. -/
theorem exists_actual_solution_fullZ_of_small_forcing (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨a, le_rfl, hab⟩ = f ∧
        ‖u-q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
          max (energyEndpointConstant K C0) Cr * ‖E.gradient‖) ∧
        fullZSDifferenceSize u q ≤ ENNReal.ofReal (C * (‖f-g‖ + ‖E.gradient‖)) ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsMildHartreePath hab alpha c f v → v=u := by
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) Cr
  let A := Cf+Q
  let S := (5/3 : ℝ)*K^(1/6 : ℝ)*6
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hA : 0 ≤ A := add_nonneg hCf hQ
  have hK := hSob.nonneg
  have hChe := hefree.1
  have hCre := heret.1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let C := 2*A + 3*(Che+Cre*(2*A+1)) + S*(2*A) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let solver := exists_actual_solution_of_small_forcing
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r0 : ℝ := Classical.choose solver
  have hr0 : 0 < r0 := (Classical.choose_spec solver).1
  have hr01 : r0 ≤ 1 := (Classical.choose_spec solver).2.1
  let sourceChoice := criticalPathIntervalSource_cap_uniform_smallness
    hDensity hSob hH (B := B+1) (epsilon := 1) (by linarith only [hB]) (by norm_num)
  let rho : ℝ := Classical.choose sourceChoice
  have hrho : 0 < rho := (Classical.choose_spec sourceChoice).1
  let r := min r0 (rho/2)
  have hr : 0 < r := lt_min hr0 (half_pos hrho)
  have hrr : r ≤ r0 := min_le_left _ _
  have hrrho : r ≤ rho/2 := min_le_right _ _
  have hr1 : r ≤ 1 := hrr.trans hr01
  refine ⟨r, C, hr, hr1, hC, ?_⟩
  intro a b hab f g q E hforced hqE hqW hsmall
  have hs0 : Cf*‖f-g‖+Q*‖E.gradient‖ ≤ r0/2 := hsmall.trans (by linarith only [hrr])
  let result := (Classical.choose_spec solver).2.2 hab f g q E hforced hqE (hqW.trans hrr) hs0
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  have humild := hu.1
  have huZ := hu.2.1
  have huinit := hu.2.2.1
  have huclose := hu.2.2.2.1
  have huunique := hu.2.2.2.2
  have huw : ‖u-q‖ ≤ r := huclose.trans (by linarith only [hsmall])
  have huE : ‖energyPath (intervalMeasure a b) u‖ ≤ B+1 := by
    have he : u = q+(u-q) := by abel
    rw [he, map_add]
    exact (norm_add_le (energyPath (intervalMeasure a b) q)
      (energyPath (intervalMeasure a b) (u-q))).trans (add_le_add hqE
      ((energyPath_norm_le _ (u-q)).trans (huw.trans hr1)))
  have huW : ‖fun j => criticalGradient (intervalMeasure a b) j u‖ ≤ rho := by
    apply (pi_norm_le_iff_of_nonneg hrho.le).mpr
    intro j
    have he : u = q+(u-q) := by abel
    have hqj := (norm_le_pi_norm (fun j => criticalGradient _ j q) j).trans hqW
    have hwj := (criticalGradient_norm_le _ (u-q) j).trans huw
    rw [he, map_add]
    exact (norm_add_le (criticalGradient (intervalMeasure a b) j q)
      (criticalGradient (intervalMeasure a b) j (u-q))).trans (by linarith only [hqj, hwj, hrrho])
  have hsrc : ∀ j : Fin 3,
      ‖(criticalPathIntervalSource hDensity hSob hH hab u q).gradient j‖ ≤ ‖u-q‖ := by
    have hqE' : ‖energyPath (intervalMeasure a b) q‖ ≤ B+1 := by linarith only [hqE]
    have hqW' : ‖fun j => criticalGradient (intervalMeasure a b) j q‖ ≤ rho := by linarith only [hqW, hrrho, hrho]
    simpa only [one_mul] using (Classical.choose_spec sourceChoice).2.2 hab u q huE hqE' huW hqW'
  have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f u).mp humild
  have hdiffZ : FullZPath (u-q) := ⟨actual_forced_difference_endpointWitness
    hDensity hSob h0 hfree hret hefree heret hH hab f g u q E hfix hforced⟩
  refine ⟨u, humild, huZ, hdiffZ, huinit, huclose, ?_, huunique⟩
  let d := ‖f-g‖
  let e := ‖E.gradient‖
  let s := d+e
  have hd : 0 ≤ d := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have hs : 0 ≤ s := add_nonneg hd he
  have hds : d ≤ s := le_add_of_nonneg_right he
  have hes : e ≤ s := le_add_of_nonneg_left hd
  have hseed : Cf*d+Q*e ≤ A*s :=
    (add_le_add (mul_le_mul_of_nonneg_left hds hCf)
      (mul_le_mul_of_nonneg_left hes hQ)).trans_eq (by dsimp only [A]; ring)
  have hw : ‖u-q‖ ≤ 2*A*s := huclose.trans
    ((mul_le_mul_of_nonneg_left hseed (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hendpoint := actual_forced_complex_difference_endpoint_bound hDensity hSob h0 hfree hret
    hefree heret hH hab f g u q E hfix hforced hsrc
  have hep : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤
      ENNReal.ofReal ((3*(Che+Cre*(2*A+1)))*s) := by
    have hsum : Che*d+Cre*‖u-q‖+Cre*e ≤ (Che+Cre*(2*A+1))*s := by
      have h1 := mul_le_mul_of_nonneg_left hds hefree.1
      have h2 := mul_le_mul_of_nonneg_left hw heret.1
      have h3 := mul_le_mul_of_nonneg_left hes heret.1
      exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)
    have heq := three_ofReal_sum (x := Che*d) (y := Cre*‖u-q‖) (z := Cre*e)
      (mul_nonneg hefree.1 hd) (mul_nonneg heret.1 (norm_nonneg (u-q)))
      (mul_nonneg heret.1 he)
    exact hendpoint.trans (heq.le.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))))
  have hsp : mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) ≤
      ENNReal.ofReal ((S*(2*A))*s) := by
    have h := (actual_scalar_difference_S_bound hDensity hSob u q).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hw))
    exact h.trans_eq ((ENNReal.ofReal_mul hS).symm.trans
      (congrArg ENNReal.ofReal (by ring : S*(2*A*s)=(S*(2*A))*s)))
  unfold fullZSDifferenceSize
  have hh := add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hw) hep) hsp
  have h2 : 0 ≤ 2*A*s := by positivity
  have h3 : 0 ≤ (3*(Che+Cre*(2*A+1)))*s := by positivity
  have h4 : 0 ≤ (S*(2*A))*s := by positivity
  apply hh.trans ((ofReal_sum_three h2 h3 h4).le.trans (ENNReal.ofReal_le_ofReal ?_))
  have ha := le_add_of_nonneg_right (a := 2*A*s+(3*(Che+Cre*(2*A+1)))*s+(S*(2*A))*s) hs
  exact ha.trans_eq (by dsimp only [C]; ring)

end HartreeF.ActualPerturbation
