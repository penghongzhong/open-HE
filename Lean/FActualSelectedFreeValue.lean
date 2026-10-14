import FActualFreeValueHeadData
import FProfileRemainderEventualBounds
import FFreeValueGradientDefect

/-! Selected-depth free-value error for one fixed actual finite head.
The original extraction depth is retained throughout. This source supplies
neither nonlinear tails nor a full approximate-solution PDE. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualSelectedFreeValue
open EnergySpace SobolevStretch StationarySelfTest CriticalTimeSobolev ProfileEnergy
  ActualStrichartz TimeHolder ProfileApproximation GeneralProfileCross CompactCross
  LocalProfileProducts ProfileSpatialSmoothing FreeHeadSlots FreeRemainderInputs
  ActualFreeRemainderHead ActualFreeValueHeadData ActualFreeValue FreeValueFullCandidate
  FreeValueSplice FreeValueGradient CrossContinuity WeakHartreeProduct ForcingDomain

variable {L : ℕ} {g : Fin L → ℝ → EnergyState}

/-- All input representatives still refer to the same original r_n^J. -/
def freeValue (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) : ℝ → Space → ℂ :=
  profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)

def freeReal (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) : ℝ → Space → Space :=
  (freeValueFields hDensity hSob (profileRemainder hDensity hSob P u J n)).U

def freeImag (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ) : ℝ → Space → Space :=
  (freeValueFields hDensity hSob (profileRemainder hDensity hSob P u J n)).V

theorem free_direction (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J n : ℕ) (k : Fin 3) :
    directionCoordinate (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n) k =
      physicalFreeGradient hDensity hSob P u J k n := by
  funext t x
  change directionalField
    (jointProjection Complex.reCLM (fun j => freeJoint
      (energyGradient j (profileRemainder hDensity hSob P u J n))) t)
    (jointProjection Complex.imCLM (fun j => freeJoint
      (energyGradient j (profileRemainder hDensity hSob P u J n))) t)
      (EuclideanSpace.basisFun (Fin 3) ℝ k) x =
      freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n)) t x
  fin_cases k <;> apply Complex.ext <;>
    simp [directionalField, jointProjection, Fin.sum_univ_three, coordinate,
      EuclideanSpace.inner_single_right]

theorem head_direction (P : LinearProfileFamily)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) (k : Fin 3) :
    directionCoordinate (headReal P r J n) (headImag P r J n) k =
      headDirection P r J k n := funext (head_directional P r J n k)

def source (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (α c : ℝ) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) : ℝ → Space → ℂ :=
  literalForcing α c (headValue P r J n) (freeValue hDensity hSob P u J n)

def gradient (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (α c : ℝ) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) :
    ℝ → Space → EuclideanSpace ℂ (Fin 3) :=
  actualGradient α c (headValue P r J n) (freeValue hDensity hSob P u J n)
    (headReal P r J n) (headImag P r J n)
    (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n)

/-- Literal source on the original canonical framed values and original free
energy evolution. The numerical gradient below represents this same source. -/
def canonicalSource (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (α c : ℝ) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : Fin L → ℝ → EnergyState) (J n : ℕ) : ℝ → Space → ℂ := fun t =>
  forcing α c (fun x => canonicalHeadValue P g J n t x +
    energyValue (freeEnergyState hDensity hSob t (profileRemainder hDensity hSob P u J n)) x) -
  forcing α c (canonicalHeadValue P g J n t)

private theorem forcing_ae {u v : Space → ℂ} (α c : ℝ) (hu : u =ᵐ[volume] v) :
    forcing α c u =ᵐ[volume] forcing α c v := by
  filter_upwards [hu] with x hx
  simp only [forcing_apply, potential_congr_ae α c hu x, hx]

/-- Spatial AE is asserted after the genuine common finite-time exceptional
set has been removed. No arbitrary representative equality is postulated. -/
theorem canonical_source_nested_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (α c : ℝ) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) :
    ∀ᵐ t ∂volume, canonicalSource hDensity hSob α c P u g J n t =ᵐ[volume]
      source hDensity hSob α c P u r J n t := by
  filter_upwards [head_canonical_nested_ae P r J n,
    (freeValueFields hDensity hSob (profileRemainder hDensity hSob P u J n)).slice_eq]
    with t hA hz
  have hsum : (fun x => canonicalHeadValue P g J n t x +
      energyValue (freeEnergyState hDensity hSob t
        (profileRemainder hDensity hSob P u J n)) x) =ᵐ[volume]
      (fun x => headValue P r J n t x + freeValue hDensity hSob P u J n t x) := by
    filter_upwards [hA, hz.1] with x hAx hzx
    exact congrArg₂ (· + ·) hAx hzx.symm
  exact (forcing_ae α c hsum).sub (forcing_ae α c hA)

/-- Every index has an actual scalar source and its true Euclidean weak gradient,
independently of later selected-depth smallness. -/
theorem actual_head_free_value_domains (hDensity : OrdinaryH1Density) {α c K C : ℝ}
    (hH : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hg : ∀ j, Continuous (g j)) (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) :
    ActualDefectDomains α c (headValue P r J n) (freeValue hDensity hSob P u J n)
      (headReal P r J n) (headImag P r J n)
      (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n) := by
  apply actual_free_value_gradient_domains hDensity hSob hH
  · intro k
    rw [head_direction]
    exact head_profile hSob P hg hE hS hW r J n k
  · intro k
    rw [free_direction]
    exact profileFreeJoint_scalarProfile hDensity hSob hStr _ k
  · exact (head_slices P r hS hW J n).mono (fun _ ht => ht.1)
  · exact profileFreeJoint_inDotH1 hDensity hSob _

/-- The same finite-head/free gradient is a genuine weak gradient of the
canonical source. This is only representative transport, not a PDE assertion. -/
theorem canonical_source_weak (hDensity : OrdinaryH1Density) {α c K C : ℝ}
    (hH : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hg : ∀ j, Continuous (g j)) (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) :
    ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (canonicalSource hDensity hSob α c P u g J n t x).re)
        (fun x => gradientReal (gradient hDensity hSob α c P u r J n t x)) ∧
      HasWeakGradient (fun x => (canonicalSource hDensity hSob α c P u g J n t x).im)
        (fun x => gradientImag (gradient hDensity hSob α c P u r J n t x)) := by
  have hd := actual_head_free_value_domains hDensity hH hSob hStr P u hg hE hS hW r J n
  filter_upwards [hd.actual_weak, canonical_source_nested_ae hDensity hSob α c P u r J n]
    with t ht he
  exact ⟨weakGradient_congr_fields ht.1 (he.symm.mono (fun _ hx => congrArg Complex.re hx))
    Filter.EventuallyEq.rfl,
    weakGradient_congr_fields ht.2 (he.symm.mono (fun _ hx => congrArg Complex.im hx))
    Filter.EventuallyEq.rfl⟩

private theorem const_mul_zero_limit {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0))
    {a : ℝ≥0∞} (ha : a ≠ ∞) : Tendsto (fun n => a*f n) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.rpow_one] using
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ha (by norm_num : (0:ℝ)<1)).comp hf

/-- A positive tolerance is chosen before extraction. The harmless pre-existing
precision sequence supplies a real sigma; it does not change any profile frame. -/
private theorem choose_free_tolerance {α : ℝ} (ha : 0 < α) (ha3 : α < 3)
    (Ccont M : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 6*(Ccont : ℝ≥0∞)*boundedModulus α M (approximationError m) ≤
      ENNReal.ofReal (ε/2) := by
  have hd : Tendsto (fun m => (approximationError m : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [approximationError_coe, zero_add] using
      smoothingPrecision_tendsto.add smoothingPrecision_tendsto
  have hm := (boundedModulus_tendsto_zero ha ha3 M).comp hd
  have ht := const_mul_zero_limit hm (show 6*(Ccont : ℝ≥0∞) ≠ ∞ by finiteness)
  exact ((ENNReal.tendsto_nhds_zero.mp ht) _ (ENNReal.ofReal_pos.mpr (by positivity))).exists

/-- The only convergence claim about the complete free-value error is at a
selected depth. The original J is retained; the fixed head is min(J,L).
Every domain is produced at every n, before the eventual uniform B+1 cap. -/
theorem actual_selected_head_free_value (hDensity : OrdinaryH1Density) {α c K B C : ℝ}
    (hH : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (hg : ∀ j, Continuous (g j)) (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) :
    (∀ J n, ActualDefectDomains α c (headValue P r J n) (freeValue hDensity hSob P u J n)
      (headReal P r J n) (headImag P r J n)
      (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ J N : ℕ,
      (P.count = ⊤ ∨ P.count = (J : WithTop ℕ)) ∧
      ∀ n ≥ N, vectorForcingNorm (gradient hDensity hSob α c P u r J n) ≤
        ENNReal.ofReal ε := by
  classical
  refine ⟨fun J n => actual_head_free_value_domains hDensity hH hSob hStr P u
    hg hE hS hW r J n, ?_⟩
  obtain ⟨Ccont, KQ, hcontrol⟩ := actual_free_value_gradient_bound hDensity hSob hH
  obtain ⟨b, hb⟩ := head_uniform_cap hSob P hg hE hS hW r
  let e : ℝ≥0 := (ENNReal.ofReal (K^(1/6 : ℝ)*(B+1))).toNNReal
  let s : ℝ≥0 := (ENNReal.ofReal (10*K^(1/6 : ℝ)*C*(B+1))).toNNReal
  let w : ℝ≥0 := (ENNReal.ofReal (C*(B+1))).toNNReal
  let M : ℝ≥0 := (4*b+2*e)+(4*b+2*s)+2*(b+w)
  have he : (e : ℝ≥0∞) = ENNReal.ofReal (K^(1/6 : ℝ)*(B+1)) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  have hs : (s : ℝ≥0∞) = ENNReal.ofReal (10*K^(1/6 : ℝ)*C*(B+1)) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  have hw : (w : ℝ≥0∞) = ENNReal.ofReal (C*(B+1)) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  have hME : 4*(b : ℝ≥0∞)+2*e ≤ M := by
    have h : 4*b+2*e ≤ M := by
      calc
        _ = (4*b+2*e)+0+0 := by simp
        _ ≤ M := add_le_add (add_le_add le_rfl bot_le) bot_le
    exact_mod_cast h
  have hMS : 4*(b : ℝ≥0∞)+2*s ≤ M := by
    have h : 4*b+2*s ≤ M := by
      calc
        _ = 0+(4*b+2*s)+0 := by simp
        _ ≤ M := add_le_add (add_le_add bot_le le_rfl) bot_le
    exact_mod_cast h
  have hMW : 2*((b : ℝ≥0∞)+w) ≤ M := by
    have h : 2*(b+w) ≤ M := by
      calc
        _ = 0+0+2*(b+w) := by simp
        _ ≤ M := add_le_add (add_le_add bot_le bot_le) le_rfl
    exact_mod_cast h
  intro ε hε
  obtain ⟨m, hm⟩ := choose_free_tolerance hH.order_pos hH.order_lt_three Ccont M hε
  obtain ⟨J, Ns, hcount, hsmall⟩ := hp.small_remainder
    (CutoffApproximation.cutoffScale m) (CutoffApproximation.cutoffScale_pos m)
  have hJ : (J : WithTop ℕ) ≤ P.count := by
    rcases hcount with ht | ht
    · simpa only [ht] using (le_top : (J : WithTop ℕ) ≤ ⊤)
    · simpa only [ht] using (le_rfl : (J : WithTop ℕ) ≤ (J : WithTop ℕ))
  obtain ⟨Nb, hfree⟩ := profileRemainder_eventually_free_bounds hDensity hSob hStr P u hp hB J hJ
    1 (by norm_num)
  have hq (k : Fin 3) := actual_head_Q_zero hDensity hH hSob hStr q P u hB hp
    hg hE hS hW r J hJ k
  let D : ℝ≥0∞ := (KQ : ℝ≥0∞)*(b : ℝ≥0∞)^(2*α)*(b : ℝ≥0∞)^(3 : ℝ)
  have hD : D ≠ ∞ := by
    have hα := hH.order_pos
    have h2 : 0 ≤ 2*α := by positivity
    dsimp only [D]
    finiteness
  have hqsum : Tendsto (fun n => ∑ k : Fin 3,
      Q (headValue P r J n) (physicalFreeGradient hDensity hSob P u J k n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => (hq k).2)
  have hlim := const_mul_zero_limit hqsum hD
  obtain ⟨Nq, hNq⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_nhds_zero.mp hlim) _ (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε/2)))
  refine ⟨J, max Ns (max Nb Nq), hcount, fun n hn => ?_⟩
  have hnS : Ns ≤ n := le_trans (le_max_left _ _) hn
  have hnb : Nb ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnq : Nq ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hzE : E (freeValue hDensity hSob P u J n) ≤ e := by rw [he]; exact (hfree n hnb).1
  have hzS : S (freeValue hDensity hSob P u J n) ≤ s := by rw [hs]; exact (hfree n hnb).2.1
  have hzW (k : Fin 3) : W (physicalFreeGradient hDensity hSob P u J k n) ≤ w := by
    rw [hw]; exact (hfree n hnb).2.2 k
  have hA (k : Fin 3) : ScalarProfile (headValue P r J n)
      (directionCoordinate (headReal P r J n) (headImag P r J n) k) := by
    rw [head_direction]
    exact head_profile hSob P hg hE hS hW r J n k
  have hz (k : Fin 3) : ScalarProfile (freeValue hDensity hSob P u J n)
      (directionCoordinate (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n) k) := by
    rw [free_direction]
    exact profileFreeJoint_scalarProfile hDensity hSob hStr _ k
  have hcE : 4*E (headValue P r J n)+2*E (freeValue hDensity hSob P u J n) ≤ M :=
    (add_le_add (mul_le_mul' le_rfl (hb J n 0).1) (mul_le_mul' le_rfl hzE)).trans hME
  have hcS : 4*S (headValue P r J n)+2*S (freeValue hDensity hSob P u J n) ≤ M :=
    (add_le_add (mul_le_mul' le_rfl (hb J n 0).2.1) (mul_le_mul' le_rfl hzS)).trans hMS
  have hcW (k : Fin 3) : 2*W
      (directionCoordinate (headReal P r J n) (headImag P r J n) k +
       directionCoordinate (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n) k) ≤ M := by
    have htri := mixed_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 10)
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (30/13 : ℝ)) ENNReal.ofReal_ne_top
      _ _ (hA k).gradient_joint.aestronglyMeasurable (hz k).gradient_joint.aestronglyMeasurable
    have hB : W (directionCoordinate (headReal P r J n) (headImag P r J n) k) ≤ b := by
      rw [head_direction]; exact (hb J n k).2.2
    have hZ : W (directionCoordinate (freeReal hDensity hSob P u J n)
        (freeImag hDensity hSob P u J n) k) ≤ w := by rw [free_direction]; exact hzW k
    exact (mul_le_mul' le_rfl (htri.trans (add_le_add hB hZ))).trans hMW
  have hsz : S (freeValue hDensity hSob P u J n) ≤ smoothingPrecision m := by
    change mixedNorm volume volume 10 10
      (profileFreeJoint hDensity hSob (profileRemainder hDensity hSob P u J n)) ≤ _
    rw [profileFreeJoint_S_eq_profileFreeSize]
    exact hsmall n hnS
  have hcd : 2*S (freeValue hDensity hSob P u J n) ≤ approximationError m := by
    rw [approximationError_coe]
    simpa only [two_mul] using add_le_add hsz hsz
  have hc := hcontrol (headValue P r J n) (freeValue hDensity hSob P u J n)
    (headReal P r J n) (headImag P r J n)
    (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n)
    hA hz ((head_slices P r hS hW J n).mono (fun _ ht => ht.1))
    (profileFreeJoint_inDotH1 hDensity hSob _) M (approximationError m) hcE hcS hcW hcd
  have hco : (KQ : ℝ≥0∞)*E (headValue P r J n)^(2*α)*S (headValue P r J n)^(3:ℝ) ≤ D := by
    exact mul_le_mul' (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow (hb J n 0).1 (by linarith [hH.order_pos])))
      (ENNReal.rpow_le_rpow (hb J n 0).2.1 (by norm_num))
  calc
    vectorForcingNorm (gradient hDensity hSob α c P u r J n) ≤
        ∑ k : Fin 3, coordinateBound α Ccont KQ M (approximationError m)
          (headValue P r J n)
          (directionCoordinate (freeReal hDensity hSob P u J n)
            (freeImag hDensity hSob P u J n) k) := hc.bound
    _ ≤ ∑ k : Fin 3, (2*(Ccont : ℝ≥0∞)*boundedModulus α M (approximationError m)+
        D*Q (headValue P r J n) (physicalFreeGradient hDensity hSob P u J k n)) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [coordinateBound, free_direction]
      exact add_le_add le_rfl (mul_le_mul' hco le_rfl)
    _ = 6*(Ccont : ℝ≥0∞)*boundedModulus α M (approximationError m)+
        D*∑ k : Fin 3, Q (headValue P r J n)
          (physicalFreeGradient hDensity hSob P u J k n) := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hm (hNq n hnq)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ ε/2)]
      congr 1
      ring

end HartreeF.ActualSelectedFreeValue
