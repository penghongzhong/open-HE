import FWeakGradientEnergyDual
import CutoffGeometry
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch CutoffApproximation
attribute [local irreducible] energySubmodule

private instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private instance : ENNReal.HolderTriple 3 6 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num⟩
private instance : ENNReal.HolderTriple 6 3 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num⟩

/-- Finite-volume local scalar L2 follows from the original L6 value alone. -/
theorem energyValue_local_memLp_two (u : EnergyState) (R : ℝ) :
    MemLp (energyValue u : Space → ℂ) 2 (volume.restrict (Metric.ball 0 R)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact ((Lp.memLp (energyValue u)).restrict (Metric.ball 0 R)).mono_exponent (by norm_num)

/-- Literal real cutoffs as actual Lp classes. -/
def cutoffLp (p : ℝ≥0∞) (n : ℕ) : Lp ℝ p (volume : Measure Space) :=
  (WeakCutoffLp.cutoff_memLp (cutoff_smooth n).continuous (cutoff_compact n) p).toLp _

def cutoffGradientLp (n : ℕ) : Lp Space 3 (volume : Measure Space) :=
  (cutoff_gradient_L3 n).toLp _

/-- L3 times the actual L6 value, with no scalar L2 domain on the input. -/
def cutoffValue (n : ℕ) : EnergyState →L[ℝ] L2 :=
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).holderL
    volume 3 6 2) (cutoffLp 3 n)).comp (energyValue.restrictScalars ℝ)

theorem cutoffValue_ae (n : ℕ) (u : EnergyState) :
    (cutoffValue n u : Space → ℂ) =ᵐ[volume] fun x => cutoff n x • energyValue u x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).coeFn_holder (r := 2)
    (cutoffLp 3 n) (energyValue u),
    (WeakCutoffLp.cutoff_memLp (cutoff_smooth n).continuous (cutoff_compact n) 3).coeFn_toLp]
    with x hx hχ
  exact hx.trans (by rw [show cutoffLp 3 n x = cutoff n x from hχ]; rfl)

/-- The actual projected gradient is a bounded linear map into vector L2. -/
def projectedGradient (L : ℂ →L[ℝ] ℝ) :
    EnergyState →L[ℝ] Lp Space 2 (volume : Measure Space) :=
  ∑ j : Fin 3, (((ContinuousLinearMap.toSpanSingleton ℝ (coordinate j)).comp L).compLpL
    2 volume).comp ((energyGradient j).restrictScalars ℝ)

theorem projectedGradient_ae (L : ℂ →L[ℝ] ℝ) (u : EnergyState) :
    (projectedGradient L u : Space → Space) =ᵐ[volume] energyProjectedGradient L u := by
  have hh : ∀ j : Fin 3, (((ContinuousLinearMap.toSpanSingleton ℝ (coordinate j)).comp L).compLpL
      2 volume (energyGradient j u) : Space → Space) =ᵐ[volume]
      fun x => L (energyGradient j u x) • coordinate j := fun j =>
    ((ContinuousLinearMap.toSpanSingleton ℝ (coordinate j)).comp L).coeFn_compLpL _
  have hs := Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 =>
    ((ContinuousLinearMap.toSpanSingleton ℝ (coordinate j)).comp L).compLpL
      2 volume (energyGradient j u))
  filter_upwards [hs, ae_all_iff.mpr hh] with x hx hxs
  change (∑ j : Fin 3, ((ContinuousLinearMap.toSpanSingleton ℝ (coordinate j)).comp L).compLpL
    2 volume (energyGradient j u)) x = _ at hx ⊢
  rw [hx]
  simp only [Finset.sum_apply, energyProjectedGradient]
  exact Finset.sum_congr rfl (fun j _ => hxs j)

/-- The exact two product-rule terms as a bounded linear vector-L2 map. -/
def cutoffGradient (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    EnergyState →L[ℝ] Lp Space 2 (volume : Measure Space) :=
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).holderL
    volume ∞ 2 2) (cutoffLp ∞ n)).comp (projectedGradient L) +
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).holderL
    volume 6 3 2).flip (cutoffGradientLp n)).comp
      ((L.compLpL 6 volume).comp (energyValue.restrictScalars ℝ))

theorem cutoffGradient_ae (L : ℂ →L[ℝ] ℝ) (n : ℕ) (u : EnergyState) :
    (cutoffGradient L n u : Space → Space) =ᵐ[volume] fun x =>
      cutoff n x • energyProjectedGradient L u x + L (energyValue u x) • gradient (cutoff n) x := by
  let A := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space)
  filter_upwards [Lp.coeFn_add (A.holderL volume ∞ 2 2 (cutoffLp ∞ n) (projectedGradient L u))
      (A.holderL volume 6 3 2 (L.compLpL 6 volume (energyValue u)) (cutoffGradientLp n)),
    A.coeFn_holder (r := 2) (cutoffLp ∞ n) (projectedGradient L u),
    A.coeFn_holder (r := 2) (L.compLpL 6 volume (energyValue u)) (cutoffGradientLp n),
    (WeakCutoffLp.cutoff_memLp (cutoff_smooth n).continuous (cutoff_compact n) ∞).coeFn_toLp,
    projectedGradient_ae L u, L.coeFn_compLpL (energyValue u),
    (cutoff_gradient_L3 n).coeFn_toLp] with x hadd ha hb hχ hG hL hd
  change (A.holderL volume ∞ 2 2 (cutoffLp ∞ n) (projectedGradient L u) +
    A.holderL volume 6 3 2 (L.compLpL 6 volume (energyValue u)) (cutoffGradientLp n)) x = _
  rw [hadd, Pi.add_apply]
  simp only [ContinuousLinearMap.holderL_apply_apply]
  rw [ha, hb]
  change cutoffLp ∞ n x • projectedGradient L u x +
    (L.compLpL 6 volume (energyValue u)) x • cutoffGradientLp n x = _
  rw [show cutoffLp ∞ n x = cutoff n x from hχ, hG, hL,
    show cutoffGradientLp n x = gradient (cutoff n) x from hd]

/-- Uniform H1 bounds are operator bounds on the actual cutoff maps. -/
theorem cutoff_h1_uniform_bound (L : ℂ →L[ℝ] ℝ) (k : ℕ)
    {u : ℕ → EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B) :
    ∀ n, ‖L.compLpL 2 volume (cutoffValue k (u n))‖ + ‖cutoffGradient L k (u n)‖ ≤
      (‖(L.compLpL 2 volume).comp (cutoffValue k)‖ + ‖cutoffGradient L k‖) * B := by
  intro n
  calc
    _ ≤ ‖(L.compLpL 2 volume).comp (cutoffValue k)‖ * ‖u n‖ +
        ‖cutoffGradient L k‖ * ‖u n‖ :=
      add_le_add (((L.compLpL 2 volume).comp (cutoffValue k)).le_opNorm (u n))
        ((cutoffGradient L k).le_opNorm (u n))
    _ = (‖(L.compLpL 2 volume).comp (cutoffValue k)‖ + ‖cutoffGradient L k‖) * ‖u n‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB n) (by positivity)

#print axioms energyValue_local_memLp_two
#print axioms cutoffValue_ae
#print axioms projectedGradient_ae
#print axioms cutoffGradient_ae
#print axioms cutoff_h1_uniform_bound
end HartreeF.LocalRellich
