import FR2ActualGlobalX
import FR2CompactSmallData

/-! Half-line exhaustion of the same actual curve, then the existing two-half
nested-Lp theorem. No adjacent whole-graph estimate and no global X assumption. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.R2Global
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest TimeHolder
  CriticalTimeSobolev ProfileApproximation ProfileSpatialSmoothing
  HomogeneousStability IntervalNormExhaustion CriticalSourceBounds
  R2SmallData ActualStrichartz FreeDataDependence ActualDuhamelPath EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath freeEnergyState

structure TwoHalfGraphBound (g : ℝ → EnergyState) (a R : ℝ) : Prop where
  left : ∀ b : ℝ, b ≤ a → ∃ p : CriticalPath (intervalMeasure b a),
    (∀ t : Icc b a, energyPath _ p t=g t) ∧ ‖p‖ ≤ R
  right : ∀ b : ℝ, a ≤ b → ∃ p : CriticalPath (intervalMeasure a b),
    (∀ t : Icc a b, energyPath _ p t=g t) ∧ ‖p‖ ≤ R

private theorem left_union (a : ℝ) : (⋃ n : ℕ, Icc (a-n) a)=Iic a := by
  ext t
  simp only [mem_iUnion,mem_Icc,mem_Iic]
  constructor
  · rintro ⟨n,_,ht⟩; exact ht
  · intro ht
    obtain ⟨n,hn⟩ := exists_nat_ge (a-t)
    exact ⟨n, by linarith, ht⟩

private theorem right_union (a : ℝ) : (⋃ n : ℕ, Icc a (a+n))=Ici a := by
  ext t
  simp only [mem_iUnion,mem_Icc,mem_Ici]
  constructor
  · rintro ⟨n,ht,_⟩; exact ht
  · intro ht
    obtain ⟨n,hn⟩ := exists_nat_ge (t-a)
    exact ⟨n, ht, by linarith⟩

private theorem left_antitone (a : ℝ) : Antitone (fun n : ℕ => a-n) := by
  intro n m hnm
  have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
  linarith

private theorem right_monotone (a : ℝ) : Monotone (fun n : ℕ => a+n) := by
  intro n m hnm
  have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
  linarith

/-- The all-exponent vector exhaustion is used at infinity/2 and 10/(30/13).
Spatial slice domains remain an explicit input here and are discharged below. -/
theorem vector_of_two_half_graph (g : ℝ → EnergyState) {a R C : ℝ}
    (h : TwoHalfGraphBound g a R) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (r ≠ ∞)] (hC : 0 ≤ C)
    (hbound : ∀ {l u : ℝ} (q : CriticalPath (intervalMeasure l u)), ‖q‖ ≤ R →
      mixedNorm (intervalMeasure l u) volume p r
        (fun t => energyComplexGradient (energyPath _ q t)) ≤ ENNReal.ofReal C)
    (hslices : ∀ {l u : ℝ} (q : CriticalPath (intervalMeasure l u)), ‖q‖ ≤ R →
      ∀ᵐ t ∂intervalMeasure l u,
        MemLp (energyComplexGradient (energyPath _ q t)) r volume) :
    ∃ F : Lp (Lp (EuclideanSpace ℂ (Fin 3)) r (volume : Measure Space)) p (volume : Measure ℝ),
      ‖F‖ ≤ C+C ∧
      (∀ᵐ t ∂volume, (F t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume]
        energyComplexGradient (g t)) := by
  have hLn (n : ℕ) : a-(n:ℝ) ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hRn (n : ℕ) : a ≤ a+(n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  choose QL hQL hQLn using fun n : ℕ => h.left (a-n) (hLn n)
  choose QR hQR hQRn using fun n : ℕ => h.right (a+n) (hRn n)
  obtain ⟨FL,hFL,hLa,hLz⟩ := exists_actual_global_vector_gradient_of_compact_with_slices
    p r hC (fun n : ℕ => a-n) (fun _ => a) (left_antitone a) monotone_const hLn g QL hQL
    (fun n => hbound (QL n) (hQLn n)) (fun n => hslices (QL n) (hQLn n))
  obtain ⟨FR,hFR,hRa,hRz⟩ := exists_actual_global_vector_gradient_of_compact_with_slices
    p r hC (fun _ => a) (fun n : ℕ => a+n) antitone_const (right_monotone a) hRn g QR hQR
    (fun n => hbound (QR n) (hQRn n)) (fun n => hslices (QR n) (hQRn n))
  obtain ⟨F,hF,hFa,_⟩ := exists_global_nestedLp_of_two_halves volume p r univ
    measurableSet_univ a (fun t => energyComplexGradient (g t)) C C FL FR hFL hFR
    (by simpa only [left_union,univ_inter] using hLa)
    (by simpa only [right_union,univ_inter] using hRa)
    (by simpa only [left_union,univ_inter] using hLz)
    (by simpa only [right_union,univ_inter] using hRz)
  exact ⟨F,hF,by simpa only [Measure.restrict_univ] using hFa⟩

theorem value_of_two_half_graph (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (g : ℝ → EnergyState) {a R : ℝ}
    (hR : 0 ≤ R) (h : TwoHalfGraphBound g a R) :
    ∃ F : Lp (Lp ℂ 10 (volume : Measure Space)) 10 (volume : Measure ℝ),
      ‖F‖ ≤ (normComparisonConstant K*R)+(normComparisonConstant K*R) ∧
      (∀ᵐ t ∂volume, (F t : Space → ℂ) =ᵐ[volume] energyValue (g t)) := by
  have hC : 0 ≤ normComparisonConstant K*R :=
    mul_nonneg (normComparisonConstant_pos hSob).le hR
  have hb {l u : ℝ} (q : CriticalPath (intervalMeasure l u)) (hq : ‖q‖ ≤ R) :
      pathValueSize (intervalMeasure l u) q ≤ ENNReal.ofReal (normComparisonConstant K*R) :=
    (path_sizes_le_coordinate_cap (intervalMeasure l u) hDensity hSob hR q
      ((le_max_right _ _).trans ((criticalPath_norm _ q).symm.le.trans hq))).2
  have hLn (n : ℕ) : a-(n:ℝ) ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hRn (n : ℕ) : a ≤ a+(n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  choose QL hQL hQLn using fun n : ℕ => h.left (a-n) (hLn n)
  choose QR hQR hQRn using fun n : ℕ => h.right (a+n) (hRn n)
  obtain ⟨FL,hFL,hLa,hLz⟩ := exists_actual_global_value_of_coherent_paths
    hDensity hSob hC (fun n : ℕ => a-n) (fun _ => a) (left_antitone a) monotone_const hLn
    g QL hQL (fun n => hb (QL n) (hQLn n))
  obtain ⟨FR,hFR,hRa,hRz⟩ := exists_actual_global_value_of_coherent_paths
    hDensity hSob hC (fun _ => a) (fun n : ℕ => a+n) antitone_const (right_monotone a) hRn
    g QR hQR (fun n => hb (QR n) (hQRn n))
  obtain ⟨F,hF,hFa,_⟩ := exists_global_nestedLp_of_two_halves volume 10 10 univ
    measurableSet_univ a (fun t => energyValue (g t))
    (normComparisonConstant K*R) (normComparisonConstant K*R) FL FR hFL hFR
    (by simpa only [left_union,univ_inter] using hLa)
    (by simpa only [right_union,univ_inter] using hRa)
    (by simpa only [left_union,univ_inter] using hLz)
    (by simpa only [right_union,univ_inter] using hRz)
  exact ⟨F,hF,by simpa only [Measure.restrict_univ] using hFa⟩

def graphToXConstant (K : ℝ) : ℝ := 2*(Real.sqrt 3+normComparisonConstant K+3)

theorem graphToXConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K) :
    0 ≤ graphToXConstant K := by
  have h := (normComparisonConstant_pos hSob).le
  unfold graphToXConstant
  positivity

theorem TwoHalfGraphBound.pointwise {g : ℝ → EnergyState} {a R : ℝ}
    (h : TwoHalfGraphBound g a R) (t : ℝ) : pureGradientNorm (g t) ≤ Real.sqrt 3*R := by
  rcases le_total a t with hat | hta
  · obtain ⟨q,hq,hn⟩ := h.right t hat
    rw [← hq ⟨t,hat,le_rfl⟩]
    exact (pureGradient_le_sqrt_three_energyState _).trans
      (mul_le_mul_of_nonneg_left ((energyPath_value_norm_le _ q _).trans hn) (Real.sqrt_nonneg _))
  · obtain ⟨q,hq,hn⟩ := h.left t hta
    rw [← hq ⟨t,le_rfl,hta⟩]
    exact (pureGradient_le_sqrt_three_energyState _).trans
      (mul_le_mul_of_nonneg_left ((energyPath_value_norm_le _ q _).trans hn) (Real.sqrt_nonneg _))

/-- All three actual nested-Lp classes are constructed before finiteness and
before toReal. The pointwise energy cap is retained separately. -/
theorem curveX_of_two_half_graph (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (g : ℝ → EnergyState) (hg : Continuous g) {a R : ℝ}
    (hR : 0 ≤ R) (h : TwoHalfGraphBound g a R) :
    CurveFinite g ∧ curveX g ≤ ENNReal.ofReal (graphToXConstant K*R) ∧
      (∀ t, pureGradientNorm (g t) ≤ Real.sqrt 3*R) := by
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : Fact ((1 : ℝ≥0∞) ≤ criticalExponent) := ⟨by norm_num [criticalExponent]⟩
  let : Fact (criticalExponent ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩
  have hCE : 0 ≤ Real.sqrt 3*R := mul_nonneg (Real.sqrt_nonneg _) hR
  have hCW : 0 ≤ 3*R := by positivity
  obtain ⟨FE,hFE,hEa⟩ := vector_of_two_half_graph g h ∞ 2 hCE
    (fun q hq => (actual_complex_energy_le_sqrt_three_graph q).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _))))
    (fun q _ => ae_of_all _ fun t => energyComplexGradient_memLp_two (energyPath _ q t))
  have hWcap {l u : ℝ} (q : CriticalPath (intervalMeasure l u)) (hq : ‖q‖ ≤ R) :
      mixedNorm (intervalMeasure l u) volume 10 criticalExponent
        (fun t => energyComplexGradient (energyPath _ q t)) ≤ ENNReal.ofReal (3*R) := by
    exact (actual_complex_W_le_three_graph q).trans
      ((mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hq)).trans_eq
        (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),ENNReal.ofReal_ofNat]))
  obtain ⟨FW,hFW,hWa⟩ := vector_of_two_half_graph g h 10 criticalExponent hCW hWcap
    (fun q hq => finite_mixedNorm_ae_slice_memLp _ volume 10 criticalExponent
      (by norm_num) (by norm_num) _ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hWcap q hq)))
  obtain ⟨FS,hFS,hSa⟩ := value_of_two_half_graph hDensity hSob g hR h
  have he : curveEnergy g ≤ ENNReal.ofReal (Real.sqrt 3*R+Real.sqrt 3*R) := by
    rw [curveEnergy_eq_actual g hg]
    simpa only [Measure.restrict_univ] using actual_mixedNorm_le_of_global_nestedLp
      volume ∞ 2 univ FE (fun t => energyComplexGradient (g t)) hFE
        (by simpa only [Measure.restrict_univ] using hEa)
  have hs : curveS g ≤ ENNReal.ofReal (normComparisonConstant K*R+normComparisonConstant K*R) := by
    simpa only [curveS,stateValueField,Measure.restrict_univ] using
      actual_mixedNorm_le_of_global_nestedLp volume 10 10 univ FS
        (fun t => energyValue (g t)) hFS (by simpa only [Measure.restrict_univ] using hSa)
  have hw : curveW g ≤ ENNReal.ofReal (3*R+3*R) := by
    rw [curveW_eq_actual]
    simpa only [Measure.restrict_univ] using actual_mixedNorm_le_of_global_nestedLp
      volume 10 criticalExponent univ FW (fun t => energyComplexGradient (g t)) hFW
        (by simpa only [Measure.restrict_univ] using hWa)
  have hCS : 0 ≤ normComparisonConstant K*R :=
    mul_nonneg (normComparisonConstant_pos hSob).le hR
  have hx : curveX g ≤ ENNReal.ofReal (graphToXConstant K*R) := by
    convert curveX_le_of_component_caps g (add_nonneg hCE hCE) (add_nonneg hCS hCS)
      (add_nonneg hCW hCW) he hs hw using 1
    unfold graphToXConstant
    ring
  exact ⟨CurveFinite.of_le hg hx,hx,h.pointwise⟩

/-- Compact paths for the actual curve, with their original radius. -/
theorem anchored_two_half_graph (hDensity : OrdinaryH1Density) {K Ch alpha a B D : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    {f : EnergyState} {g : ℝ → EnergyState}
    (h : AnchoredCompactBounds hDensity hSob hfree alpha a f g B D) :
    TwoHalfGraphBound g a (B*‖f‖) := by
  constructor
  · intro b hb
    let choice := h.backward b hb
    let p : CriticalPath (intervalMeasure b a) := Classical.choose choice
    exact ⟨p, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1⟩
  · intro b hb
    let choice := h.forward b hb
    let p : CriticalPath (intervalMeasure a b) := Classical.choose choice
    exact ⟨p, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1⟩

theorem anchored_correction_two_half_graph (hDensity : OrdinaryH1Density)
    {K Ch alpha a B D : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) {f : EnergyState} {g : ℝ → EnergyState}
    (h : AnchoredCompactBounds hDensity hSob hfree alpha a f g B D) :
    TwoHalfGraphBound (fun t => g t-freeEnergyState hDensity hSob (t-a) f)
      a (D*‖f‖^(5+2*alpha)) := by
  constructor
  · intro b hb
    let choice := h.backward b hb
    let p : CriticalPath (intervalMeasure b a) := Classical.choose choice
    exact ⟨p-freeCriticalPath hDensity hSob hfree b a
      (freeEnergyState hDensity hSob (-a) f),
      represented_correction_state hDensity hSob hfree f g p
        (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.2⟩
  · intro b hb
    let choice := h.forward b hb
    let p : CriticalPath (intervalMeasure a b) := Classical.choose choice
    exact ⟨p-freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-a) f),
      represented_correction_state hDensity hSob hfree f g p
        (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.2⟩

/-- The same Fourier orbit, with a literal anchor. -/
def anchoredFreeCurve (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (f : EnergyState) : ℝ → EnergyState :=
  fun t => freeEnergyState hDensity hSob (t-a) f

def freeXConstant (K Ch : ℝ) : ℝ :=
  graphToXConstant K * max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch *
    max (K^((6 : ℝ)⁻¹)) 1

theorem freeXConstant_nonneg {K Ch : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) : 0 ≤ freeXConstant K Ch := by
  have hA : 0 ≤ max (K^((6 : ℝ)⁻¹)) 1 := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hC : 0 ≤ max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch := hfree.1.trans (le_max_right _ _)
  exact mul_nonneg (mul_nonneg (graphToXConstant_nonneg hSob) hC) hA

theorem anchoredFreeCurve_continuous (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (f : EnergyState) :
    Continuous (anchoredFreeCurve hDensity hSob a f) :=
  (freeEnergyState_time_continuous hDensity hSob f).comp (continuous_id.sub continuous_const)

/-- The free global X/domain bound is itself an actual compact exhaustion.
No global Strichartz field or pre-existing finite real norm is an input. -/
theorem anchoredFreeCurve_bound (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a : ℝ) (f : EnergyState) :
    CurveFinite (anchoredFreeCurve hDensity hSob a f) ∧
      xNorm (anchoredFreeCurve hDensity hSob a f) ≤ freeXConstant K Ch*pureGradientNorm f := by
  let C := max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch
  have hC : 0 ≤ C := hfree.1.trans (le_max_right _ _)
  have h : TwoHalfGraphBound (anchoredFreeCurve hDensity hSob a f) a (C*‖f‖) := by
    constructor
    · intro b _
      refine ⟨freeCriticalPath hDensity hSob hfree b a
        (freeEnergyState hDensity hSob (-a) f),?_,
        BackwardUniformData.actual_backwardFreeCriticalPath_norm_le hDensity hSob hfree b a f⟩
      intro t
      rw [freeCriticalPath_energy,← freeEnergyState_add_time]
      rfl
    · intro b _
      refine ⟨freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) f),?_,
        actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b f⟩
      intro t
      rw [freeCriticalPath_energy,← freeEnergyState_add_time]
      rfl
  obtain ⟨hfin,hx,_⟩ := curveX_of_two_half_graph hDensity hSob _
    (anchoredFreeCurve_continuous hDensity hSob a f) (mul_nonneg hC (norm_nonneg _)) h
  refine ⟨hfin,?_⟩
  calc
    _ ≤ graphToXConstant K*(C*‖f‖) :=
      xNorm_le (mul_nonneg (graphToXConstant_nonneg hSob) (mul_nonneg hC (norm_nonneg _))) hx
    _ ≤ graphToXConstant K*(C*(max (K^((6 : ℝ)⁻¹)) 1*pureGradientNorm f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (energyState_le_pureGradient hSob f) hC)
        (graphToXConstant_nonneg hSob)
    _ = _ := by dsimp [freeXConstant,C]; ring

end HartreeF.R2Global
