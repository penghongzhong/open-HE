import FCriticalAffineIsometry
import CompactLpTails
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Data.Nat.Find

/-! Actual finite-L6 restrictions and an intrinsic open-ball mass gauge.
This source is UNCOMPILED. It uses no L2 domain for the state value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace HartreeF.L6OrbitGauge
open EnergySpace CriticalAffine

local instance : Fact ((1 : ℝ≥0∞) ≤ (6 : ℕ)) := ⟨by norm_num⟩

/-- The actual indicator class, with its finite-L6 domain supplied first. -/
def restrictLp (A : Set Space) (hA : MeasurableSet A) (f : L6) : L6 :=
  MemLp.toLp (A.indicator (f : Space → ℂ))
    (MemLp.indicator hA.nullMeasurableSet (Lp.memLp f))

theorem restrictLp_ae (A : Set Space) (hA : MeasurableSet A) (f : L6) :
    (restrictLp A hA f : Space → ℂ) =ᵐ[volume] A.indicator (f : Space → ℂ) :=
  (MemLp.indicator hA.nullMeasurableSet (Lp.memLp f)).coeFn_toLp

theorem restrictLp_norm (A : Set Space) (hA : MeasurableSet A) (f : L6) :
    ‖restrictLp A hA f‖ = (eLpNorm (A.indicator (f : Space → ℂ)) 6 volume).toReal :=
  Lp.norm_toLp _ _

theorem restrictLp_zero (A : Set Space) (hA : MeasurableSet A) :
    restrictLp A hA 0 = 0 := by
  apply Lp.ext
  filter_upwards [restrictLp_ae A hA 0,
    Lp.coeFn_zero ℂ 6 (volume : Measure Space)] with x hx hz
  rw [hx]
  by_cases h : x ∈ A
  · simp only [Set.indicator_of_mem h, hz]
  · simp only [Set.indicator_of_notMem h, hz, Pi.zero_apply]

/-- The quotient restriction is 1-Lipschitz, uniformly over measurable sets. -/
theorem restrictLp_lipschitz (A : Set Space) (hA : MeasurableSet A) :
    LipschitzWith 1 (restrictLp A hA) := by
  apply LipschitzWith.of_edist_le
  intro f g
  unfold restrictLp
  erw [Lp.edist_toLp_toLp, Lp.edist_def]
  have he : A.indicator (f : Space → ℂ) - A.indicator (g : Space → ℂ) =
      A.indicator ((f : Space → ℂ) - (g : Space → ℂ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  rw [he]
  exact eLpNorm_indicator_le _ hA.nullMeasurableSet

theorem restrictLp_norm_le (A : Set Space) (hA : MeasurableSet A) (f : L6) :
    ‖restrictLp A hA f‖ ≤ ‖f‖ := by
  simpa only [restrictLp_zero, dist_zero_right, NNReal.coe_one, one_mul] using
    (restrictLp_lipschitz A hA).dist_le_mul f 0

theorem restrictLp_norm_triangle (A : Set Space) (hA : MeasurableSet A) (f g : L6) :
    ‖restrictLp A hA f‖ ≤ ‖f-g‖ + ‖restrictLp A hA g‖ := by
  have hc := (restrictLp_lipschitz A hA).dist_le_mul f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hc
  have ht := norm_add_le (restrictLp A hA f - restrictLp A hA g) (restrictLp A hA g)
  rw [sub_add_cancel] at ht
  exact ht.trans (add_le_add hc le_rfl)

theorem restrictLp_norm_mono {A B : Set Space} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (f : L6) :
    ‖restrictLp A hA f‖ ≤ ‖restrictLp B hB f‖ := by
  rw [restrictLp_norm, restrictLp_norm]
  apply ENNReal.toReal_mono
    (MemLp.indicator hB.nullMeasurableSet (Lp.memLp f)).eLpNorm_ne_top
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet,
    eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet]
  exact eLpNorm_mono_measure _ (volume.restrict_mono_set hAB)

def setMass (f : L6) (A : Set Space) : ℝ := ∫ z in A, ‖f z‖^6

def mass (u : EnergyState) : ℝ := ‖energyValue u‖^6

def ballMass (u : EnergyState) (x : Space) (R : ℝ) : ℝ :=
  setMass (energyValue u) (ball x R)

theorem sixth_integrable (f : L6) : Integrable (fun z => ‖f z‖^6) volume :=
  (Lp.memLp f).integrable_norm_pow (by decide : (6 : ℕ) ≠ 0)

theorem restrictLp_norm_pow (A : Set Space) (hA : MeasurableSet A) (f : L6) :
    ‖restrictLp A hA f‖^6 = setMass f A := by
  rw [energyLp_norm_pow (by decide : (6 : ℕ) ≠ 0)]
  calc
    _ = ∫ z, A.indicator (fun x => ‖f x‖^6) z := by
      apply integral_congr_ae
      filter_upwards [restrictLp_ae A hA f] with z hz
      rw [hz]
      by_cases h : z ∈ A <;> simp [Set.indicator, h]
    _ = setMass f A := integral_indicator hA

theorem setMass_nonneg (f : L6) (A : Set Space) : 0 ≤ setMass f A :=
  integral_nonneg (fun z => pow_nonneg (norm_nonneg (f z)) 6)

theorem setMass_mono (f : L6) {A B : Set Space} (hAB : A ⊆ B) :
    setMass f A ≤ setMass f B :=
  setIntegral_mono_set (sixth_integrable f).integrableOn
    (ae_of_all _ (fun z => pow_nonneg (norm_nonneg (f z)) 6))
    (ae_of_all _ hAB)

theorem setMass_add_compl (f : L6) (A : Set Space) (hA : MeasurableSet A) :
    setMass f A + setMass f Aᶜ = ‖f‖^6 := by
  rw [energyLp_norm_pow (by decide : (6 : ℕ) ≠ 0)]
  exact integral_add_compl hA (sixth_integrable f)

theorem mass_pos {u : EnergyState} (hu : u ≠ 0) : 0 < mass u := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro h
  apply hu
  apply energyValue_injective
  simpa only [map_zero] using h

/-- Fixed-function absolute continuity, made uniform over every ball center. -/
theorem exists_small_ball_norm (f : L6) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x : Space, ‖restrictLp (ball x r) measurableSet_ball f‖ ≤ ε := by
  obtain ⟨δ, hδ, hsmall⟩ := (Lp.memLp f).eLpNorm_indicator_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 6) (by norm_num : (6 : ℝ≥0∞) ≠ ∞)
    (ENNReal.ofReal_pos.mpr hε)
  have hreal : Tendsto (fun n : ℕ =>
      (1 / ((n : ℝ)+1))^3 * (Real.pi*4/3)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3).mul_const (Real.pi*4/3)
  have hvol : Tendsto (fun n : ℕ => volume (ball (0 : Space) (1/((n:ℝ)+1))))
      atTop (𝓝 0) := by
    have hh := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    have heq (n : ℕ) : volume (ball (0 : Space) (1/((n:ℝ)+1))) =
        ENNReal.ofReal ((1/((n:ℝ)+1))^3 * (Real.pi*4/3)) := by
      rw [EuclideanSpace.volume_ball_fin_three,
        ENNReal.ofReal_mul (show 0 ≤ (1/((n:ℝ)+1))^3 by positivity),
        ENNReal.ofReal_pow (show 0 ≤ 1/((n:ℝ)+1) by positivity)]
    simpa only [Function.comp_def, heq, ENNReal.ofReal_zero] using hh
  obtain ⟨N, hN⟩ := (hvol.eventually_lt_const hδ).exists
  refine ⟨1/((N:ℝ)+1), by positivity, ?_⟩
  intro x
  rw [restrictLp_norm]
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  apply hsmall _ measurableSet_ball.nullMeasurableSet
  simpa only [EuclideanSpace.volume_ball_fin_three] using hN.le

/-- Complements of OPEN balls are dominated by the older strict exterior tail.
The radius is N+1; no sphere-null assertion or false complement equality occurs. -/
theorem exists_exterior_norm (f : L6) {ε : ℝ} (hε : 0 < ε) :
    ∃ S > 0, ‖restrictLp (ball (0 : Space) S)ᶜ measurableSet_ball.compl f‖ ≤ ε := by
  have ht := ComplexIMS.exteriorLp_norm_tendsto_zero
    (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num : (6 : ℝ≥0∞) ≠ ∞) f
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const hε).exists
  let A : Set Space := {z : Space | (N : ℝ) < ‖z‖}
  have hA : MeasurableSet A :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hsub : (ball (0 : Space) ((N : ℝ)+1))ᶜ ⊆ A := by
    intro z hz
    have hz' : (N : ℝ)+1 ≤ ‖z‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
    change (N : ℝ) < ‖z‖
    linarith
  refine ⟨(N : ℝ)+1, by positivity, ?_⟩
  exact (restrictLp_norm_mono measurableSet_ball.compl hA hsub f).trans hN.le

/-- Both conditions use open balls; the half-radius condition quantifies over ALL centers. -/
structure Gauge (u : EnergyState) (R : ℝ) (x : Space) : Prop where
  radius_pos : 0 < R
  lower : 3*mass u/8 ≤ ballMass u x R
  half_upper : ∀ y : Space, ballMass u y (R/2) ≤ mass u/2

private theorem exists_large_ball {u : EnergyState} (hu : u ≠ 0) :
    ∃ R > 0, mass u/2 < ballMass u 0 R := by
  have hq : 0 < ‖energyValue u‖ := norm_pos_iff.mpr (fun h =>
    hu (energyValue_injective (by simpa only [map_zero] using h)))
  obtain ⟨R, hR, htail⟩ := exists_exterior_norm (energyValue u)
    (show 0 < ‖energyValue u‖/2 by positivity)
  have hp := pow_le_pow_left₀ (norm_nonneg _) htail 6
  rw [restrictLp_norm_pow] at hp
  have hsplit := setMass_add_compl (energyValue u) (ball (0 : Space) R) measurableSet_ball
  refine ⟨R, hR, ?_⟩
  change ‖energyValue u‖^6 / 2 < setMass (energyValue u) (ball 0 R)
  have hm : 0 < ‖energyValue u‖^6 := pow_pos hq _
  nlinarith [hp]

/-- The least successful dyadic subdivision supplies an intrinsic gauge.
No maximizing center, concentration supremum, or gauge continuity is assumed. -/
theorem exists_gauge {u : EnergyState} (hu : u ≠ 0) : ∃ R x, Gauge u R x := by
  classical
  obtain ⟨R₀, hR₀, hlarge⟩ := exists_large_ball hu
  have hm : 0 < mass u := mass_pos hu
  have hq : 0 < ‖energyValue u‖ := norm_pos_iff.mpr (fun h =>
    hu (energyValue_injective (by simpa only [map_zero] using h)))
  obtain ⟨r, hr, hsmall⟩ := exists_small_ball_norm (energyValue u)
    (show 0 < ‖energyValue u‖/2 by positivity)
  have hsmallmass : ∀ x : Space, ballMass u x r ≤ mass u/2 := by
    intro x
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hsmall x) 6
    rw [restrictLp_norm_pow] at hp
    change setMass (energyValue u) (ball x r) ≤ ‖energyValue u‖^6/2
    have hp0 := pow_nonneg (norm_nonneg (energyValue u)) 6
    nlinarith [hp]
  let P : ℕ → Prop := fun n => ∀ x : Space, ballMass u x (R₀/2^(n+1)) ≤ mass u/2
  have hex : ∃ n, P n := by
    have hlim : Tendsto (fun n : ℕ => R₀/2^(n+1)) atTop (𝓝 0) := by
      have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n * (R₀/2)) atTop (𝓝 0) := by
        simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)).mul_const (R₀/2)
      have he (n : ℕ) : R₀/2^(n+1) = (1/2 : ℝ)^n * (R₀/2) := by
        simp only [pow_succ, div_pow, one_pow]
        ring
      simpa only [he] using ht
    obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hr).exists
    refine ⟨n, fun x => ?_⟩
    exact (setMass_mono (energyValue u) (ball_subset_ball hn.le)).trans (hsmallmass x)
  let k : ℕ := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hR : 0 < R₀/2^k := by positivity
  have hhalf : ∀ y : Space, ballMass u y ((R₀/2^k)/2) ≤ mass u/2 := by
    intro y
    simpa only [pow_succ, div_div] using hk y
  have hcenter : ∃ x, mass u/2 < ballMass u x (R₀/2^k) := by
    cases hk0 : k with
    | zero => exact ⟨0, by simpa only [hk0, pow_zero, div_one] using hlarge⟩
    | succ j =>
      have hj : ¬P j := Nat.find_min hex (by change j < k; omega)
      change ¬ ∀ x : Space, ballMass u x (R₀/2^(j+1)) ≤ mass u/2 at hj
      push Not at hj
      obtain ⟨x, hx⟩ := hj
      exact ⟨x, by simpa only [hk0, Nat.succ_eq_add_one] using hx⟩
  obtain ⟨x, hx⟩ := hcenter
  exact ⟨R₀/2^k, x, ⟨hR, by linarith, hhalf⟩⟩

end HartreeF.L6OrbitGauge
