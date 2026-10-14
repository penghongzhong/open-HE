import FActualBilateralPathTools
import FSpatialProfileStateLimit

/-! Native graph windows, with physical mark zero and normalized mark s.
All indices and compact-domain proofs are explicit. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.BilateralGraphBounds
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine MaximalTrajectory
  Retarded ActualStrichartz EndpointOutput ForcingDomain CriticalPathSpace
  AffineMixed BilateralPathTools
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)

/-- Large genuine compact graph windows on both sides of the zero mark.
This is a sequence contract; its actual producer uses finite S mass bisection. -/
def BilateralGraphWindows (u : ℕ → EnergyState) : Prop :=
  ∀ n, let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u n)
    ∃ (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b)
      (hL : Icc a 0 ⊆ U.domain) (hR : Icc 0 b ⊆ U.domain),
      (n : ℝ)+1 ≤ ‖U.path ha hL‖ ∧ (n : ℝ)+1 ≤ ‖U.path hb hR‖

/-- The normalization uses c=s, so the transformed actual mark is exactly zero. -/
theorem future_cap_spatial_pullback (u : EnergyState) {lambda : ℝ}
    (hlambda : 0 < lambda) (y : Space) (s R : ℝ)
    (hdom : Ici s ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      s ((criticalAffineState lambda hlambda y).symm u)).domain)
    (hcap : ∀ (b : ℝ) (hb : s ≤ b)
      (hI : Icc s b ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        s ((criticalAffineState lambda hlambda y).symm u)).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        s ((criticalAffineState lambda hlambda y).symm u)).path hb hI‖ ≤ R) :
    ∀ (b : ℝ) (hb : 0 ≤ b)
      (hI : Icc 0 b ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 u).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 u).path hb hI‖ ≤ R := by
  let z := (criticalAffineState lambda hlambda y).symm u
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s z
  have hd : affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) z = u :=
    (criticalAffineState lambda hlambda y).apply_symm_apply u
  let normAt : ℝ → EnergyState → Prop := fun mark datum =>
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH mark datum
    ∀ (A B : ℝ) (hAB : A ≤ B)
      (hN : Icc (timeAffine lambda⁻¹ s A) (timeAffine lambda⁻¹ s B) ⊆ N.domain)
      (hV : Icc A B ⊆ V.domain),
      ‖V.path hAB hV‖ =
        ‖N.path (AffinePath.timeAffine_monotone (inv_pos.mpr hlambda) s hAB) hN‖
  have hraw : normAt ((s-s)/lambda⁻¹^2)
      (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) z) :=
    actualMaximalTrajectory_affine_norm hDensity hSob h0 hfree hret hefree heret hH
      (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) s s z
  have hmark : (s-s)/lambda⁻¹^2 = 0 := by
    simp only [sub_self, zero_div]
  have hn : normAt 0 u := Eq.mp (congrArg₂ normAt hmark hd) hraw
  intro b hb hI
  have hNs : Icc (timeAffine lambda⁻¹ s 0) (timeAffine lambda⁻¹ s b) ⊆ N.domain := by
    intro t ht
    apply hdom
    simpa only [mem_Ici, timeAffine, mul_zero, zero_add] using ht.1
  have heq := hn 0 b hb hNs hI
  apply heq.trans_le
  let capAt : ℝ → Prop := fun A =>
    ∀ (hAB : A ≤ timeAffine lambda⁻¹ s b)
      (hD : Icc A (timeAffine lambda⁻¹ s b) ⊆ N.domain),
      ‖N.path hAB hD‖ ≤ R
  have hbase : capAt s := hcap (timeAffine lambda⁻¹ s b)
  have hzero : timeAffine lambda⁻¹ s 0 = s := by
    simp only [timeAffine, mul_zero, zero_add]
  have hnormalized : capAt (timeAffine lambda⁻¹ s 0) :=
    Eq.mpr (congrArg capAt hzero) hbase
  exact hnormalized _ _

/-- Past normalization has the same positive orientation, not a time reflection. -/
theorem past_cap_spatial_pullback (u : EnergyState) {lambda : ℝ}
    (hlambda : 0 < lambda) (y : Space) (s R : ℝ)
    (hdom : Iic s ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      s ((criticalAffineState lambda hlambda y).symm u)).domain)
    (hcap : ∀ (a : ℝ) (ha : a ≤ s)
      (hI : Icc a s ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        s ((criticalAffineState lambda hlambda y).symm u)).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        s ((criticalAffineState lambda hlambda y).symm u)).path ha hI‖ ≤ R) :
    ∀ (a : ℝ) (ha : a ≤ 0)
      (hI : Icc a 0 ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 u).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 u).path ha hI‖ ≤ R := by
  let z := (criticalAffineState lambda hlambda y).symm u
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s z
  have hd : affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) z = u :=
    (criticalAffineState lambda hlambda y).apply_symm_apply u
  let normAt : ℝ → EnergyState → Prop := fun mark datum =>
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH mark datum
    ∀ (A B : ℝ) (hAB : A ≤ B)
      (hN : Icc (timeAffine lambda⁻¹ s A) (timeAffine lambda⁻¹ s B) ⊆ N.domain)
      (hV : Icc A B ⊆ V.domain),
      ‖V.path hAB hV‖ =
        ‖N.path (AffinePath.timeAffine_monotone (inv_pos.mpr hlambda) s hAB) hN‖
  have hraw : normAt ((s-s)/lambda⁻¹^2)
      (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) z) :=
    actualMaximalTrajectory_affine_norm hDensity hSob h0 hfree hret hefree heret hH
      (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) s s z
  have hmark : (s-s)/lambda⁻¹^2 = 0 := by
    simp only [sub_self, zero_div]
  have hn : normAt 0 u := Eq.mp (congrArg₂ normAt hmark hd) hraw
  intro a ha hI
  have hNs : Icc (timeAffine lambda⁻¹ s a) (timeAffine lambda⁻¹ s 0) ⊆ N.domain := by
    intro t ht
    apply hdom
    simpa only [mem_Iic, timeAffine, mul_zero, zero_add] using ht.2
  have heq := hn a 0 ha hNs hI
  apply heq.trans_le
  let capAt : ℝ → Prop := fun B =>
    ∀ (hAB : timeAffine lambda⁻¹ s a ≤ B)
      (hD : Icc (timeAffine lambda⁻¹ s a) B ⊆ N.domain),
      ‖N.path hAB hD‖ ≤ R
  have hbase : capAt s := hcap (timeAffine lambda⁻¹ s a)
  have hzero : timeAffine lambda⁻¹ s 0 = s := by
    simp only [timeAffine, mul_zero, zero_add]
  have hnormalized : capAt (timeAffine lambda⁻¹ s 0) :=
    Eq.mpr (congrArg capAt hzero) hbase
  exact hnormalized _ _

/-- A common subsequence cannot turn the future large graph windows into a
uniformly bounded family; the same physical data occur on both sides. -/
theorem no_eventual_future_cap (u : ℕ → EnergyState)
    (hw : BilateralGraphWindows hDensity hSob h0 hfree hret hefree heret hH u)
    (k : ℕ → ℕ) (hk : StrictMono k) (R : ℝ) (N : ℕ)
    (hcap : ∀ n, N ≤ n → ∀ (b : ℝ) (hb : 0 ≤ b)
      (hI : Icc 0 b ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u (k n))).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u (k n))).path hb hI‖ ≤ R) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt R
  let n := max N m
  obtain ⟨_a, b, _ha, hb, _hL, hR, _hleft, hright⟩ := hw (k n)
  have hbound := hcap n (le_max_left _ _) b hb hR
  have hnk : n ≤ k n := hk.id_le n
  have hmn : m ≤ n := le_max_right _ _
  have hcast : (m : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hmn.trans hnk
  linarith

theorem no_eventual_past_cap (u : ℕ → EnergyState)
    (hw : BilateralGraphWindows hDensity hSob h0 hfree hret hefree heret hH u)
    (k : ℕ → ℕ) (hk : StrictMono k) (R : ℝ) (N : ℕ)
    (hcap : ∀ n, N ≤ n → ∀ (a : ℝ) (ha : a ≤ 0)
      (hI : Icc a 0 ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u (k n))).domain),
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u (k n))).path ha hI‖ ≤ R) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt R
  let n := max N m
  obtain ⟨a, _b, ha, _hb, hL, _hR, hleft, _hright⟩ := hw (k n)
  have hbound := hcap n (le_max_left _ _) a ha hL
  have hnk : n ≤ k n := hk.id_le n
  have hmn : m ≤ n := le_max_right _ _
  have hcast : (m : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hmn.trans hnk
  linarith

end HartreeF.BilateralGraphBounds
