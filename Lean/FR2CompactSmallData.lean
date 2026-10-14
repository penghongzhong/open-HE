import FUniformSmallDataPath
import FUniformBackwardTerminalSolver
import FBackwardFreePathDifference
import FClosedBackwardPathMaximalExtension
import FIntervalAdvancedPathLinearity
import FCompatibleIntervalSourceDifference
import FEnergyGradientTopology

/-! Actual compact two-sided small-data paths and their canonical trajectory.
The public backward comparison radius is chosen before the terminal solver.
All constants precede every anchor, datum and compact interval. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.R2SmallData
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence CriticalSourceBounds
open IntervalTimeTransport MaximalTrajectory
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
local instance r2PathAddCommGroup (a b : ℝ) :
    AddCommGroup (CriticalPath (intervalMeasure a b)) :=
  Submodule.addCommGroup (criticalPathSubmodule (intervalMeasure a b))
local instance r2PathModule (a b : ℝ) :
    Module ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.module (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource freeCriticalPath freeEnergyState
  actualMaximalTrajectory intervalAdvancedCriticalPath

/-- Uniform compact graph and correction caps on the two sides of an anchor.
The pointwise equalities identify the paths with the specified actual curve. -/
structure AnchoredCompactBounds (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (alpha a : ℝ) (f : EnergyState) (U : ℝ → EnergyState) (B D : ℝ) : Prop where
  forward : ∀ (b : ℝ) (_hab : a ≤ b),
    ∃ p : CriticalPath (intervalMeasure a b),
      (∀ t : Set.Icc a b, energyPath _ p t = U t) ∧
      ‖p‖ ≤ B * ‖f‖ ∧
      ‖p - freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) f)‖ ≤ D * ‖f‖ ^ (5 + 2*alpha)
  backward : ∀ (b : ℝ) (_hba : b ≤ a),
    ∃ p : CriticalPath (intervalMeasure b a),
      (∀ t : Set.Icc b a, energyPath _ p t = U t) ∧
      ‖p‖ ≤ B * ‖f‖ ∧
      ‖p - freeCriticalPath hDensity hSob hfree b a
        (freeEnergyState hDensity hSob (-a) f)‖ ≤ D * ‖f‖ ^ (5 + 2*alpha)

/-- Multiplication-only power combination, including the zero datum. -/
theorem rpow_mul_fifth {alpha x : ℝ} (halpha : 0 < alpha) (hx : 0 ≤ x) :
    x ^ (2*alpha) * x^5 = x ^ (5 + 2*alpha) := by
  by_cases hzero : x = 0
  · simp only [hzero, zero_pow (by norm_num : (5 : ℕ) ≠ 0), mul_zero,
      Real.zero_rpow (by linarith : 5 + 2*alpha ≠ 0)]
  · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    congr 1; norm_num; ring

/-- The actual compatible derivative source has degree 5+2 alpha in the
existing graph norm. No source-domain or source-cap premise is added. -/
theorem exists_source_power_bound (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (u : CriticalPath (intervalMeasure a b)),
      ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
        C * ‖u‖ ^ (5 + 2*alpha) := by
  obtain ⟨C, hC⟩ := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let L := normComparisonConstant K
  have hL : 0 ≤ L := (normComparisonConstant_pos hSob).le
  refine ⟨(C : ℝ)*L^5, mul_nonneg C.coe_nonneg (pow_nonneg
    (normComparisonConstant_pos hSob).le 5), ?_⟩
  intro a b hab u
  have hW : ‖fun j => criticalGradient (intervalMeasure a b) j u‖ ≤ ‖u‖ :=
    (le_max_right _ _).trans_eq (criticalPath_norm (intervalMeasure a b) u).symm
  have hb : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
      (C : ℝ)*‖u‖^(2*alpha)*L^5*‖u‖^5 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    exact hC hab u ‖u‖ ‖u‖ (norm_nonneg _) (norm_nonneg _)
      (energyPath_norm_le _ u) hW
  calc
    _ ≤ (C : ℝ)*‖u‖^(2*alpha)*L^5*‖u‖^5 := hb
    _ = ((C : ℝ)*L^5)*(‖u‖^(2*alpha)*‖u‖^5) := by ring
    _ = _ := by rw [rpow_mul_fifth hH.order_pos (norm_nonneg u)]

/-- The actual backward map at the zero path is the terminal free path.
Source-class and advanced-path subtraction supply the zero identity. -/
theorem backwardHartreeDuhamelMap_zero_path (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f : EnergyState) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f 0 =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) f) := by
  let F := criticalPathIntervalSource hDensity hSob hH hab
    (0 : CriticalPath (intervalMeasure a b)) 0
  have hs : F.sub F = F := criticalPathIntervalSource_sub_zero hDensity hSob hH hab 0 0
  have hz : intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F = 0 :=
    (congrArg (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret) hs).symm.trans
      ((intervalAdvancedCriticalPath_sub hDensity hSob h0 hfree hret F F).trans
        (by
          apply Subtype.ext
          change (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F).val -
            (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F).val = 0
          exact sub_self _))
  unfold backwardHartreeDuhamelMap
  change _ - Complex.I • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F = _
  rw [hz, smul_zero, sub_zero]

set_option diagnostics true in
/-- Datum-linear terminal paths. The first radius is the public comparison
witness, and the terminal solver is called with delta equal to that witness. -/
theorem exists_uniform_backward_small_data_path (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {a b : ℝ} (hab : a ≤ b) (f : EnergyState),
      ‖f‖ ≤ delta → ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab alpha c f u ∧
        energyPath _ u ⟨b, hab, le_rfl⟩ = f ∧
        ‖u‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f‖) := by
  let comparisonChoice :=
    BackwardSolutionComparison.exists_actual_backward_source_smallness_and_contraction
      hDensity hSob h0 hfree hret hH (B := 1) (by norm_num)
  let rho : ℝ := Classical.choose comparisonChoice
  have hrho : 0 < rho := (Classical.choose_spec comparisonChoice).1
  let terminalChoice := WaveTerminal.exists_uniform_backward_terminal_radius
    hDensity hSob h0 hfree hret hH (B := 1) (delta := rho) (by norm_num) hrho
  let eta : ℝ := Classical.choose terminalChoice
  have heta : 0 < eta := (Classical.choose_spec terminalChoice).1
  have hetarho : eta ≤ rho := (Classical.choose_spec terminalChoice).2.1
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  let delta := min 1 eta / (2*(Cf+1))
  have hdelta : 0 < delta := div_pos (lt_min (by norm_num) heta) (by positivity)
  have hCd : Cf*delta ≤ min 1 eta / 2 := by
    dsimp [delta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Cf+1))).mpr
    have hm : 0 ≤ min 1 eta := le_min (by norm_num) heta.le
    nlinarith
  refine ⟨delta, hdelta, ?_⟩
  intro a b hab f hf
  let p := freeCriticalPath hDensity hSob hfree a b
    (freeEnergyState hDensity hSob (-b) f)
  have hp : ‖p‖ ≤ min 1 eta / 2 :=
    (BackwardUniformData.actual_backwardFreeCriticalPath_norm_le hDensity hSob hfree a b f).trans
      ((mul_le_mul_of_nonneg_left hf hCf).trans hCd)
  have hpE : ‖energyPath _ p‖ ≤ (1 : ℝ)/2 :=
    ((energyPath_norm_le _ p).trans hp).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hpW (j : Fin 3) : ‖criticalGradient _ j p‖ ≤ eta/2 :=
    ((norm_le_pi_norm (fun j => criticalGradient (intervalMeasure a b) j p) j).trans
      (((le_max_right _ _).trans_eq (criticalPath_norm _ p).symm).trans hp)).trans
        (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  let solutionChoice := (Classical.choose_spec terminalChoice).2.2 hab f hpE hpW
  let u : CriticalPath (intervalMeasure a b) := Classical.choose solutionChoice
  have hfix := (Classical.choose_spec solutionChoice).1
  have hterminal := (Classical.choose_spec solutionChoice).2.1
  have huE := (Classical.choose_spec solutionChoice).2.2.1
  have huW := (Classical.choose_spec solutionChoice).2.2.2.1
  have hzeroE : ‖energyPath (intervalMeasure a b) (0 : CriticalPath (intervalMeasure a b))‖ ≤
      (1 : ℝ) := by
    have hz : ‖(0 : C(Set.Icc a b, EnergyState))‖ = 0 :=
      norm_zero (E := C(Set.Icc a b, EnergyState))
    exact (le_of_eq ((congrArg norm ((energyPath (intervalMeasure a b)).map_zero)).trans hz)).trans
      (by norm_num : (0 : ℝ) ≤ 1)
  have hzeroW : ‖fun j => criticalGradient (intervalMeasure a b) j
      (0 : CriticalPath (intervalMeasure a b))‖ ≤ rho := by
    apply (pi_norm_le_iff_of_nonneg hrho.le).mpr
    intro j
    have hz : ‖(0 : CriticalGradient (intervalMeasure a b))‖ = 0 :=
      norm_zero (E := CriticalGradient (intervalMeasure a b))
    exact (le_of_eq ((congrArg norm ((criticalGradient (intervalMeasure a b) j).map_zero)).trans hz)).trans
      hrho.le
  have hc := ((Classical.choose_spec comparisonChoice).2.2 hab f u 0 huE hzeroE (huW.trans hetarho) hzeroW).2
  rw [hfix, backwardHartreeDuhamelMap_zero_path hDensity hSob h0 hfree hret hH hab f,
    sub_zero] at hc
  have htriangle : ‖u‖ ≤ ‖u-p‖ + ‖p‖ := by
    calc
      ‖u‖ = ‖(u-p)+p‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le (u-p) p
  have hlinear : ‖u‖ ≤ 2 * ‖p‖ := by change ‖u-p‖ ≤ (1/2 : ℝ)*‖u‖ at hc; linarith
  exact ⟨u, (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hab f u).mpr hfix, hterminal, hlinear.trans
      (mul_le_mul_of_nonneg_left
        (BackwardUniformData.actual_backwardFreeCriticalPath_norm_le hDensity hSob hfree a b f)
        (by norm_num))⟩

/-- A bound on the native graph norm controls every represented state. -/
theorem represented_state_norm_le {a b : ℝ}
    (p : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    ‖energyPath _ p t‖ ≤ ‖p‖ :=
  ((energyPath _ p).norm_coe_le_norm t).trans (energyPath_norm_le _ p)

theorem AnchoredCompactBounds.pointwise (hDensity : OrdinaryH1Density)
    {K Ch alpha a B D : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) {f : EnergyState} {U : ℝ → EnergyState}
    (h : AnchoredCompactBounds hDensity hSob hfree alpha a f U B D) (t : ℝ) :
    ‖U t‖ ≤ B*‖f‖ := by
  rcases le_total a t with hat | hta
  · obtain ⟨p, hp, hnorm, _⟩ := h.forward t hat
    exact ((congrArg norm (hp ⟨t, hat, le_rfl⟩)).symm.trans_le
      (represented_state_norm_le p ⟨t, hat, le_rfl⟩)).trans hnorm
  · obtain ⟨p, hp, hnorm, _⟩ := h.backward t hta
    exact ((congrArg norm (hp ⟨t, le_rfl, hta⟩)).symm.trans_le
      (represented_state_norm_le p ⟨t, le_rfl, hta⟩)).trans hnorm

/-- Subtracting the actual free graph represents the literal anchored
correction as an EnergyState identity at every compact time. -/
theorem represented_correction_state (hDensity : OrdinaryH1Density)
    {K Ch a b s : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (f : EnergyState)
    (U : ℝ → EnergyState) (p : CriticalPath (intervalMeasure a b))
    (hp : ∀ t : Set.Icc a b, energyPath _ p t = U t) (t : Set.Icc a b) :
    energyPath _ (p - freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-s) f)) t =
      U t - freeEnergyState hDensity hSob ((t : ℝ)-s) f := by
  have hsub := congrArg (fun q : C(Set.Icc a b, EnergyState) => q t)
    ((energyPath (intervalMeasure a b)).map_sub p
      (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-s) f)))
  exact hsub.trans (congrArg₂ (fun x y : EnergyState => x-y) (hp t)
    ((freeCriticalPath_energy hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-s) f) t).trans
      (by rw [← freeEnergyState_add_time, sub_eq_add_neg])))

theorem AnchoredCompactBounds.correction_pointwise (hDensity : OrdinaryH1Density)
    {K Ch alpha a B D : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) {f : EnergyState} {U : ℝ → EnergyState}
    (h : AnchoredCompactBounds hDensity hSob hfree alpha a f U B D) (t : ℝ) :
    ‖U t - freeEnergyState hDensity hSob (t-a) f‖ ≤ D*‖f‖^(5+2*alpha) := by
  rcases le_total a t with hat | hta
  · obtain ⟨p, hp, _, hnorm⟩ := h.forward t hat
    exact ((congrArg norm (represented_correction_state hDensity hSob hfree (s := a) f U p hp
      ⟨t, hat, le_rfl⟩)).symm.trans_le (represented_state_norm_le _
        ⟨t, hat, le_rfl⟩)).trans hnorm
  · obtain ⟨p, hp, _, hnorm⟩ := h.backward t hta
    exact ((congrArg norm (represented_correction_state hDensity hSob hfree (s := a) f U p hp
      ⟨t, le_rfl, hta⟩)).symm.trans_le (represented_state_norm_le _
        ⟨t, le_rfl, hta⟩)).trans hnorm

set_option diagnostics true in
/-- Same canonical trajectory on the whole line, with datum-linear compact
bounds and a genuine 5+2 alpha correction. There is no small-global input. -/
theorem exists_uniform_two_sided_small_data (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta B D : ℝ, 0 < delta ∧ 0 ≤ B ∧ 0 ≤ D ∧
      ∀ (a : ℝ) (f : EnergyState), ‖f‖ ≤ delta →
        let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a f
        M.domain = Set.univ ∧
          AnchoredCompactBounds hDensity hSob hfree alpha a f M.state B D := by
  let forwardChoice := SmallEnergy.exists_uniform_small_data_path
    hDensity hSob h0 hfree hret hefree heret hH
  let df : ℝ := Classical.choose forwardChoice
  have hdf : 0 < df := (Classical.choose_spec forwardChoice).1
  let backwardChoice := exists_uniform_backward_small_data_path
    hDensity hSob h0 hfree hret hH
  let db : ℝ := Classical.choose backwardChoice
  have hdb : 0 < db := (Classical.choose_spec backwardChoice).1
  let sourceChoice := exists_source_power_bound hDensity hSob hH
  let C : ℝ := Classical.choose sourceChoice
  have hC : 0 ≤ C := (Classical.choose_spec sourceChoice).1
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  let B := 2*Cf
  let Q := max (energyEndpointConstant K C0) (Ch*C0+Cr)
  let D := Q*C*B^(5+2*alpha)
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) hCf
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hQ hC) (Real.rpow_nonneg hB _)
  have hQforward : max (energyEndpointConstant K C0) Cr ≤ Q :=
    max_le_max le_rfl (le_add_of_nonneg_left (mul_nonneg hfree.1 h0.1))
  have hpower : 0 ≤ 5+2*alpha := by linarith [hH.order_pos]
  have hnonlinear {l r : ℝ} (hlr : l ≤ r) (f : EnergyState)
      (p : CriticalPath (intervalMeasure l r)) (hp : ‖p‖ ≤ B*‖f‖) :
      Q*‖(criticalPathIntervalSource hDensity hSob hH hlr p 0).gradient‖ ≤
        D*‖f‖^(5+2*alpha) := by
    calc
      _ ≤ Q*(C*‖p‖^(5+2*alpha)) := mul_le_mul_of_nonneg_left ((Classical.choose_spec sourceChoice).2 hlr p) hQ
      _ ≤ Q*(C*((B*‖f‖)^(5+2*alpha))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hp hpower) hC) hQ
      _ = D*‖f‖^(5+2*alpha) := by rw [Real.mul_rpow hB (norm_nonneg _)]; dsimp [D]; ring
  refine ⟨min df db, B, D, lt_min hdf hdb, hB, hD, ?_⟩
  intro a f hf
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a f
  have hF (b : ℝ) (hab : a ≤ b) :
      ∃ p : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f p ∧ ‖p‖ ≤ B*‖f‖ ∧
        ‖p-freeCriticalPath hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-a) f)‖ ≤ D*‖f‖^(5+2*alpha) := by
    obtain ⟨p, hp, _, hn, _⟩ := (Classical.choose_spec forwardChoice).2 hab f (hf.trans (min_le_left _ _))
    have hn' : ‖p‖ ≤ B*‖f‖ := hn.trans_eq (by dsimp [B, Cf]; ring)
    have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hab f p).mp hp
    have hc := hartreeDuhamelMap_sub_free_norm hDensity hSob h0 hfree hret hH hab f p
    rw [hfix] at hc
    exact ⟨p, hp, hn', hc.trans
      ((mul_le_mul_of_nonneg_right hQforward (norm_nonneg _)).trans (hnonlinear hab f p hn'))⟩
  have hBwd (b : ℝ) (hba : b ≤ a) :
      ∃ p : CriticalPath (intervalMeasure b a),
        IsBackwardMildHartreePath hba alpha c f p ∧ ‖p‖ ≤ B*‖f‖ ∧
        ‖p-freeCriticalPath hDensity hSob hfree b a
          (freeEnergyState hDensity hSob (-a) f)‖ ≤ D*‖f‖^(5+2*alpha) := by
    obtain ⟨p, hp, _, hn⟩ := (Classical.choose_spec backwardChoice).2 hba f (hf.trans (min_le_right _ _))
    have hn' : ‖p‖ ≤ B*‖f‖ := hn.trans_eq (by dsimp [B, Cf]; ring)
    have hfix := (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hba f p).mp hp
    have hc := WaveTerminal.backward_map_sub_free_norm hDensity hSob h0 hfree hret hH hba f p
    rw [hfix] at hc
    exact ⟨p, hp, hn', hc.trans (hnonlinear hba f p hn')⟩
  have hMdom : M.domain = maximalDomain alpha c a f := by
    unfold M actualMaximalTrajectory
    rfl
  have hglobal : M.domain = Set.univ := by
    rw [hMdom]
    apply Set.eq_univ_of_forall
    intro t
    rcases le_total a t with hat | hta
    · obtain ⟨p, hp, _, _⟩ := hF t hat
      exact closed_mildPath_right_mem_maximalDomain hDensity hSob h0 hfree hret
        hefree heret hH hat f p hp
    · obtain ⟨p, hp, _, _⟩ := hBwd t hta
      exact closed_backward_mildPath_left_mem_maximalDomain hDensity hSob h0 hfree hret
        hefree heret hH hta f p hp
  refine ⟨hglobal, ?_⟩
  dsimp only [M, actualMaximalTrajectory]
  constructor
  · intro b hab
    obtain ⟨p, hp, hn, hc⟩ := hF b hab
    obtain ⟨V, hV, hVp⟩ := closed_mildPath_extends_to_localTrajectory
      hDensity hSob h0 hfree hret hefree heret hH hab f p hp
    refine ⟨p, ?_, hn, hc⟩
    intro t
    exact (hVp t).symm.trans
      (maximalState_agrees hDensity hSob h0 hfree hret hH V (hV t.property)).symm
  · intro b hba
    obtain ⟨p, hp, hn, hc⟩ := hBwd b hba
    obtain ⟨V, hV, hVp⟩ := closed_backward_mildPath_extends_to_localTrajectory
      hDensity hSob h0 hfree hret hefree heret hH hba f p hp
    refine ⟨p, ?_, hn, hc⟩
    intro t
    exact (hVp t).symm.trans
      (maximalState_agrees hDensity hSob h0 hfree hret hH V (hV t.property)).symm

/-- Recenter a global actual maximal curve back at the original mark. The
second inclusion is what proves the original maximal domain is all of R. -/
theorem actualMaximalTrajectory_global_of_recenter (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c T s : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c)
    (f : EnergyState)
    (hs : s ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f).domain)
    (hg : (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f).state s)).domain = Set.univ) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s (M.state s)
    M.domain = Set.univ ∧ M.state = V.state := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  let R := M.recenter s hs
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s (M.state s)
  have hRV : R.domain ⊆ V.domain := by
    simpa only [V, actualMaximalTrajectory] using subset_maximalDomain R
  have hT : T ∈ V.domain := hRV M.center_mem
  have hVT : V.state T = f :=
    (LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH V R hT M.center_mem).trans
      M.initial
  let W := V.recenterWithDatum T f hT hVT
  have hWM : W.domain ⊆ M.domain := by
    simpa only [M, actualMaximalTrajectory] using subset_maximalDomain W
  have hglobal : M.domain = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact hWM (hg.symm ▸ Set.mem_univ t)
  refine ⟨hglobal, ?_⟩
  funext t
  exact LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH M W
    (hglobal.symm ▸ Set.mem_univ t) (hg.symm ▸ Set.mem_univ t)

/-- Quantitative free comparison at arbitrary matching times; no assumption
on the time sequence itself is needed. -/
theorem matching_state_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v phi : EnergyState) (s : ℝ) :
    ‖v‖ ≤ max (K^((6 : ℝ)⁻¹)) 1 * pureGradientNorm phi +
      ‖v-freeEnergyState hDensity hSob s phi‖ := by
  let w := freeEnergyState hDensity hSob s phi
  have hw : ‖w‖ ≤ max (K^((6 : ℝ)⁻¹)) 1 * pureGradientNorm phi := by
    simpa only [w, freeEnergyState_pureGradientNorm] using energyState_le_pureGradient hSob w
  calc
    ‖v‖ = ‖(v-w)+w‖ := by rw [sub_add_cancel]
    _ ≤ ‖v-w‖+‖w‖ := norm_add_le _ _
    _ ≤ ‖v-w‖+max (K^((6 : ℝ)⁻¹)) 1*pureGradientNorm phi := add_le_add le_rfl hw
    _ = _ := add_comm _ _

/-- Small matching profiles globalize the originally marked actual maximal
trajectory. Every sufficiently late retained time supplies compact bounds on
that same curve, so a later norm limit has a fixed left-hand side. -/
theorem exists_uniform_matching_compact_bounds (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta B D : ℝ, 0 < delta ∧ 0 ≤ B ∧ 0 ≤ D ∧
      ∀ (T : ℝ) (f phi : EnergyState) (s : ℕ → ℝ),
        let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
        (∀ᶠ n in atTop, s n ∈ M.domain) →
        Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
          atTop (𝓝 0) →
        pureGradientNorm phi ≤ delta →
        M.domain = Set.univ ∧
          (∀ᶠ n in atTop, AnchoredCompactBounds hDensity hSob hfree alpha
            (s n) (M.state (s n)) M.state B D) ∧
          (∀ n, ‖M.state (s n)‖ ≤ max (K^((6 : ℝ)⁻¹)) 1*pureGradientNorm phi +
            ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖) := by
  obtain ⟨d, B, D, hd, hB, hD, (Classical.choose_spec terminalChoice).2.2⟩ := exists_uniform_two_sided_small_data
    hDensity hSob h0 hfree hret hefree heret hH
  let A := max (K^((6 : ℝ)⁻¹)) 1
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  let delta := d / (2*(A+1))
  have hdelta : 0 < delta := div_pos hd (by positivity)
  have hAdelta : A*delta ≤ d/2 := by
    dsimp [delta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*(A+1))).mpr
    nlinarith
  refine ⟨delta, B, D, hdelta, hB, hD, ?_⟩
  intro T f phi s
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  dsimp only
  intro hdom hmatch hphi
  have hdata (n : ℕ) : ‖M.state (s n)‖ ≤ A*pureGradientNorm phi +
      ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖ :=
    matching_state_norm_le hDensity hSob (M.state (s n)) phi (s n)
  have hevent : ∀ᶠ n in atTop, s n ∈ M.domain ∧ ‖M.state (s n)‖ ≤ d := by
    filter_upwards [hdom, hmatch.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < d/2))]
      with n hn herr
    refine ⟨hn, ?_⟩
    have hmain : A*pureGradientNorm phi ≤ d/2 :=
      (mul_le_mul_of_nonneg_left hphi hA).trans hAdelta
    linarith [hdata n]
  obtain ⟨n, hn, hsmall⟩ := hevent.exists
  obtain ⟨hglobalV, _⟩ := (Classical.choose_spec terminalChoice).2.2 (s n) (M.state (s n)) hsmall
  have hglobal := (actualMaximalTrajectory_global_of_recenter
    hDensity hSob h0 hfree hret hefree heret hH f hn hglobalV).1
  refine ⟨hglobal, ?_, hdata⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hglobalV, hb⟩ := (Classical.choose_spec terminalChoice).2.2 (s n) (M.state (s n)) hn.2
  have heq := (actualMaximalTrajectory_global_of_recenter
    hDensity hSob h0 hfree hret hefree heret hH f hn.1 hglobalV).2
  exact Eq.mpr (congrArg (fun U : ℝ → EnergyState =>
    AnchoredCompactBounds hDensity hSob hfree alpha (s n) (M.state (s n)) U B D) heq) hb

/-- Exact pure-gradient matching cap, with the free isometry constant one. -/
theorem matching_state_pureGradient_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (v phi : EnergyState) (s : ℝ) :
    pureGradientNorm v ≤ pureGradientNorm phi +
      pureGradientNorm (v-freeEnergyState hDensity hSob s phi) := by
  calc
    pureGradientNorm v = pureGradientNorm
        ((v-freeEnergyState hDensity hSob s phi)+freeEnergyState hDensity hSob s phi) := by
      rw [sub_add_cancel]
    _ ≤ pureGradientNorm (v-freeEnergyState hDensity hSob s phi) +
        pureGradientNorm (freeEnergyState hDensity hSob s phi) := pureGradientNorm_add_le _ _
    _ = _ := by rw [freeEnergyState_pureGradientNorm, add_comm]

/-- The retained graph-norm matching error gives the actual pure-gradient
error limit, with no division by the profile or datum size. -/
theorem matching_error_pureGradient_tendsto {e : ℕ → EnergyState}
    (he : Tendsto (fun n => ‖e n‖) atTop (𝓝 0)) :
    Tendsto (fun n => pureGradientNorm (e n)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => Real.sqrt 3*‖e n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (Real.sqrt 3)
  exact squeeze_zero (fun n => pureGradientNorm_nonneg (e n))
    (fun n => pureGradient_le_sqrt_three_energyState (e n)) hb

/-- A zero linear profile forces the same selected canonical trajectory to
vanish everywhere, even when its original marked datum was not written as zero. -/
theorem actual_matching_zero_profile (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c)
    (T : ℝ) (f phi : EnergyState) (s : ℕ → ℝ) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
    (∀ᶠ n in atTop, s n ∈ M.domain) →
    Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0) →
    pureGradientNorm phi = 0 → M.domain = Set.univ ∧ ∀ t, M.state t = 0 := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  dsimp only
  intro hdom hmatch hphi
  obtain ⟨delta, B, D, hdelta, _, _, (Classical.choose_spec terminalChoice).2.2⟩ := exists_uniform_matching_compact_bounds
    hDensity hSob h0 hfree hret hefree heret hH
  have hsmall : pureGradientNorm phi ≤ delta := by rw [hphi]; exact hdelta.le
  obtain ⟨hglobal, hbounds, hdata⟩ := (Classical.choose_spec terminalChoice).2.2 T f phi s hdom hmatch hsmall
  have hnorm : Tendsto (fun n => ‖M.state (s n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg (M.state (s n))) _ hmatch
    intro n
    simpa only [hphi, mul_zero, zero_add] using hdata n
  refine ⟨hglobal, ?_⟩
  intro t
  have hlim : Tendsto (fun n => ‖M.state t‖-B*‖M.state (s n)‖)
      atTop (𝓝 ‖M.state t‖) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := ‖M.state t‖)).sub (hnorm.const_mul B)
  have hnonpos : ‖M.state t‖ ≤ 0 := le_of_tendsto hlim (hbounds.mono fun n hn =>
    sub_nonpos.mpr (AnchoredCompactBounds.pointwise hDensity hSob hfree hn t))
  exact norm_eq_zero.mp (le_antisymm hnonpos (norm_nonneg _))

end HartreeF.R2SmallData
