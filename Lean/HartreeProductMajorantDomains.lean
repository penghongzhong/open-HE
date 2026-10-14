import WeakProductCutoffDomains

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeProduct
open ForcingDomain GradientMajorants RieszWeakDerivative

def forcingMagnitude (α c : ℝ) (u : Space → ℂ) (x : Space) : ℝ :=
  ‖potential α c u x‖*‖u x‖^(2+α)

def firstGradientMagnitude (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) : ℝ :=
  ‖potential α c u x‖*‖u x‖^(1+α)*(‖U x‖+‖V x‖)

def fourthGradientMagnitude (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) : ℝ :=
  ‖u x‖^(2+α)*‖hartreePotentialGradient α c u U V x‖

theorem product_magnitudes_nonneg (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    0 ≤ forcingMagnitude α c u x ∧ 0 ≤ firstGradientMagnitude α c u U V x ∧
    0 ≤ fourthGradientMagnitude α c u U V x := by
  unfold forcingMagnitude firstGradientMagnitude fourthGradientMagnitude
  exact ⟨by positivity,by positivity,by positivity⟩

theorem forcingMagnitude_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} (hu6 : MemLp u 6 volume) :
    MemLp (forcingMagnitude α c u) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  obtain ⟨C,hC⟩ := forcing_energy_domain_bound hH
  have he : (fun x => ‖forcing α c u x‖) = forcingMagnitude α c u := by
    funext x
    change ‖potential α c u x • localFactor α u x‖ = _
    rw [norm_smul,ForcingDomain.norm_localFactor hH.order_pos]
    rfl
  rw [← he]
  exact (hC u hu6).1.norm

theorem firstGradientMagnitude_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (firstGradientMagnitude α c u U V) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hp := spatialBound_self (one_div_pos.mpr (potential_reciprocal_bounds hH).1)
    (hartreePotential_memLp_split hH hu6 hu10).norm
  have hS := spacetime_power_bound (fun x => norm_nonneg (u x)) hu10.norm (show 0 < 1+α by linarith [hH.order_pos])
  have hY := spatialBound_self (by norm_num : 0 < (30/13 : ℝ)) (hU.norm.add hV.norm)
  have hm := ((hp.mul hS).mul hY).memLp
  convert hm using 1
  · rfl
  · congr 1
    dsimp [reciprocalA]
    field_simp
    ring

theorem fourthGradientMagnitude_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (fourthGradientMagnitude α c u U V) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  have hpow := split_power_bound (fun x => norm_nonneg (u x)) hu6.norm hu10.norm
    (show 0 < 5*α/3 by positivity) (show 0 < 2-2*α/3 by linarith)
  have hg := spatialBound_self (one_div_pos.mpr (potential_reciprocal_bounds hH).2.2.1)
    (hartreePotentialGradient_domain hH hu6 hu10 hU hV).2.norm
  have hm := (hpow.mul hg).memLp
  convert hm using 1
  · funext x
    dsimp [fourthGradientMagnitude]
    congr 2
    ring
  · congr 1
    dsimp [reciprocalB]
    field_simp
    ring

#print axioms product_magnitudes_nonneg
#print axioms forcingMagnitude_memLp
#print axioms firstGradientMagnitude_memLp
#print axioms fourthGradientMagnitude_memLp
end HartreeF.WeakHartreeProduct
