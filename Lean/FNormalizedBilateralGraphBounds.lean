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
  have hn := actualMaximalTrajectory_affine_norm hDensity hSob h0 hfree hret hefree heret hH
    (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) s s z
  dsimp only at hn
  simp only [sub_self, zero_div, hd] at hn
  intro b hb hI
  have hNs : Icc (timeAffine lambda⁻¹ s 0) (timeAffine lambda⁻¹ s b) ⊆ N.domain := by
    intro t ht
    apply hdom
    simpa only [mem_Ici, timeAffine, mul_zero, zero_add] using ht.1
  have hsb : s ≤ timeAffine lambda⁻¹ s b := by
    unfold timeAffine
    exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hb)
  have hNs' : Icc s (timeAffine lambda⁻¹ s b) ⊆ N.domain := by
    simpa only [timeAffine, mul_zero, zero_add] using hNs
  have hbound := hcap (timeAffine lambda⁻¹ s b) hsb hNs'
  have heq := hn 0 b hb hNs hI
  apply heq.trans_le
  simpa only [timeAffine, mul_zero, zero_add] using hbound

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
  have hn := actualMaximalTrajectory_affine_norm hDensity hSob h0 hfree hret hefree heret hH
    (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) s s z
  dsimp only at hn
  simp only [sub_self, zero_div, hd] at hn
  intro a ha hI
  have hNs : Icc (timeAffine lambda⁻¹ s a) (timeAffine lambda⁻¹ s 0) ⊆ N.domain := by
    intro t ht
    apply hdom
    simpa only [mem_Iic, timeAffine, mul_zero, zero_add] using ht.2
  have has : timeAffine lambda⁻¹ s a ≤ s := by
    unfold timeAffine
    exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ha)
  have hNs' : Icc (timeAffine lambda⁻¹ s a) s ⊆ N.domain := by
    simpa only [timeAffine, mul_zero, zero_add] using hNs
  have hbound := hcap (timeAffine lambda⁻¹ s a) has hNs'
  have heq := hn a 0 ha hNs hI
  apply heq.trans_le
  simpa only [timeAffine, mul_zero, zero_add] using hbound

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
