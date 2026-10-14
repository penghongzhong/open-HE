import FCompatibleL1IntervalSource
import FIntervalLpRestriction

/-! Restriction of actual scalar time-L1 sources and their actual time-L2
spatial derivatives to a nested compact time interval. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
open IntervalTimeTransport EnergySpace Retarded CriticalPathRestriction

variable {a b c d : ℝ} (E : CompatibleL1IntervalSource a b)

/-- Restriction changes the time measure, preserving the scalar and derivative
representatives almost everywhere on the smaller interval. -/
def restrict (hac : a ≤ c) (hdb : d ≤ b) : CompatibleL1IntervalSource c d where
  value := shrinkLp 1 (localMeasure_mono hac hdb) E.value
  gradient := fun j => shrinkLp 2 (localMeasure_mono hac hdb) (E.gradient j)
  derivative := by
    have hg := ae_all_iff.mpr (fun j =>
      shrinkLp_coeFn 2 (localMeasure_mono hac hdb) (E.gradient j))
    filter_upwards [ae_mono (localMeasure_mono hac hdb) E.derivative,
      shrinkLp_coeFn 1 (localMeasure_mono hac hdb) E.value, hg] with t hE hv hg
    intro j
    rw [hv, hg j]
    exact hE j

@[simp] theorem restrict_value (hac : a ≤ c) (hdb : d ≤ b) :
    (E.restrict hac hdb).value = shrinkLp 1 (localMeasure_mono hac hdb) E.value := rfl

@[simp] theorem restrict_gradient (hac : a ≤ c) (hdb : d ≤ b) (j : Fin 3) :
    (E.restrict hac hdb).gradient j =
      shrinkLp 2 (localMeasure_mono hac hdb) (E.gradient j) := rfl

theorem restrict_value_coeFn (hac : a ≤ c) (hdb : d ≤ b) :
    ((E.restrict hac hdb).value : ℝ → SourceSpace) =ᵐ[localMeasure c d] E.value :=
  shrinkLp_coeFn 1 (localMeasure_mono hac hdb) E.value

theorem restrict_gradient_coeFn (hac : a ≤ c) (hdb : d ≤ b) (j : Fin 3) :
    ((E.restrict hac hdb).gradient j : ℝ → SourceSpace) =ᵐ[localMeasure c d]
      E.gradient j :=
  shrinkLp_coeFn 2 (localMeasure_mono hac hdb) (E.gradient j)

/-- The inherited spatial derivative is the original actual source gradient. -/
theorem restrict_derivative (hac : a ≤ c) (hdb : d ≤ b) :
    ∀ᵐ t ∂localMeasure c d, ∀ j : Fin 3,
      ∂_{coordinate j} (Lp.toTemperedDistribution ((E.restrict hac hdb).value t)) =
        Lp.toTemperedDistribution (E.gradient j t) := by
  filter_upwards [ae_mono (localMeasure_mono hac hdb) E.derivative,
    E.restrict_value_coeFn hac hdb] with t hE hv
  intro j
  rw [hv]
  exact hE j

theorem restrict_value_norm_le (hac : a ≤ c) (hdb : d ≤ b) :
    ‖(E.restrict hac hdb).value‖ ≤ ‖E.value‖ :=
  shrinkLp_norm_le 1 (localMeasure_mono hac hdb) E.value

theorem restrict_gradient_component_norm_le (hac : a ≤ c) (hdb : d ≤ b)
    (j : Fin 3) : ‖(E.restrict hac hdb).gradient j‖ ≤ ‖E.gradient j‖ :=
  shrinkLp_norm_le 2 (localMeasure_mono hac hdb) (E.gradient j)

/-- The actual three-component forcing norm does not increase on a subinterval. -/
theorem restrict_gradient_norm_le (hac : a ≤ c) (hdb : d ≤ b) :
    ‖(E.restrict hac hdb).gradient‖ ≤ ‖E.gradient‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact (E.restrict_gradient_component_norm_le hac hdb j).trans (norm_le_pi_norm _ j)

theorem ext_value_gradient {E F : CompatibleL1IntervalSource a b}
    (hv : E.value = F.value) (hg : E.gradient = F.gradient) : E = F := by
  cases E
  cases F
  cases hv
  cases hg
  rfl

@[simp] theorem restrict_self : E.restrict le_rfl le_rfl = E := by
  apply ext_value_gradient
  · exact Lp.ext (E.restrict_value_coeFn le_rfl le_rfl)
  · funext j
    exact Lp.ext (E.restrict_gradient_coeFn le_rfl le_rfl j)

@[simp] theorem restrict_trans {e f : ℝ}
    (hac : a ≤ c) (hdb : d ≤ b) (hce : c ≤ e) (hfd : f ≤ d) :
    (E.restrict hac hdb).restrict hce hfd = E.restrict (hac.trans hce) (hfd.trans hdb) := by
  apply ext_value_gradient
  · apply Lp.ext
    filter_upwards [(E.restrict hac hdb).restrict_value_coeFn hce hfd,
      ae_mono (localMeasure_mono hce hfd) (E.restrict_value_coeFn hac hdb),
      E.restrict_value_coeFn (hac.trans hce) (hfd.trans hdb)] with t h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  · funext j
    apply Lp.ext
    filter_upwards [(E.restrict hac hdb).restrict_gradient_coeFn hce hfd j,
      ae_mono (localMeasure_mono hce hfd) (E.restrict_gradient_coeFn hac hdb j),
      E.restrict_gradient_coeFn (hac.trans hce) (hfd.trans hdb) j] with t h1 h2 h3
    exact h1.trans (h2.trans h3.symm)

end HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
