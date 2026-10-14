import FIntervalLpRestriction
import FCriticalPathBall

/-! Restriction of the canonical complete E+W graph, with literal energy values
and a.e. identical Bochner gradient representatives. This supplies a time-domain
operation for later restart arguments, not a PDE uniqueness theorem. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace CriticalPathBall

variable {a b c d : ℝ}

/-- Restrict the actual canonical energy trajectory and all three actual gradients. -/
def restrictPath (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) : CriticalPath (intervalMeasure c d) := by
  let g : C(Set.Icc c d, EnergyState) :=
    ⟨fun t => energyPath (intervalMeasure a b) u (intervalInclusion hac hdb t),
      (energyPath (intervalMeasure a b) u).continuous.comp (intervalInclusion_continuous hac hdb)⟩
  let w (j : Fin 3) : CriticalGradient (intervalMeasure c d) := restrictIntervalLp 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u)
  refine ⟨(g, w), ?_⟩
  intro j
  filter_upwards [ae_intervalInclusion hac hcd hdb (u.property j),
    restrictIntervalLp_coeFn 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u)] with t hu hw
  change energyGradientDistribution j (energyPath (intervalMeasure a b) u (intervalInclusion hac hdb t)) =
    Lp.toTemperedDistribution (restrictIntervalLp 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u) t)
  rw [hw]
  exact hu

@[simp] theorem restrictPath_energy (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc c d) :
    energyPath (intervalMeasure c d) (restrictPath hac hcd hdb u) t =
      energyPath (intervalMeasure a b) u (intervalInclusion hac hdb t) := rfl

@[simp] theorem restrictPath_gradient (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    criticalGradient (intervalMeasure c d) j (restrictPath hac hcd hdb u) =
      restrictIntervalLp 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u) := rfl

theorem restrictPath_gradient_coeFn (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    criticalGradient (intervalMeasure c d) j (restrictPath hac hcd hdb u) =ᵐ[intervalMeasure c d]
      fun t => criticalGradient (intervalMeasure a b) j u (intervalInclusion hac hdb t) :=
  restrictIntervalLp_coeFn 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u)

/-- Representatives of the restricted path agree with the original actual energy gradients. -/
theorem restrictPath_actual_gradient_ae_eq (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ∀ᵐ t ∂intervalMeasure c d,
      (energyGradient j (energyPath (intervalMeasure a b) u (intervalInclusion hac hdb t)) : V → ℂ) =ᵐ[volume]
        (criticalGradient (intervalMeasure c d) j (restrictPath hac hcd hdb u) t : V → ℂ) :=
  criticalGradient_ae_eq _ (restrictPath hac hcd hdb u) j

theorem restrictPath_energy_norm_le (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖energyPath (intervalMeasure c d) (restrictPath hac hcd hdb u)‖ ≤ ‖energyPath (intervalMeasure a b) u‖ := by
  apply (ContinuousMap.norm_le (energyPath (intervalMeasure c d)
    (restrictPath hac hcd hdb u)) (C := ‖energyPath (intervalMeasure a b) u‖) (by positivity)).mpr
  intro t
  exact (energyPath (intervalMeasure a b) u).norm_coe_le_norm (intervalInclusion hac hdb t)

theorem restrictPath_gradient_norm_le (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient (intervalMeasure c d) j (restrictPath hac hcd hdb u)‖ ≤ ‖criticalGradient (intervalMeasure a b) j u‖ :=
  restrictIntervalLp_norm_le 10 hac hcd hdb (criticalGradient (intervalMeasure a b) j u)

theorem restrictPath_W_norm_le (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖gradientCoordinates (intervalMeasure c d) (restrictPath hac hcd hdb u)‖ ≤ ‖gradientCoordinates (intervalMeasure a b) u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact (restrictPath_gradient_norm_le hac hcd hdb u j).trans
    (norm_le_pi_norm (gradientCoordinates (intervalMeasure a b) u) j)

theorem restrictPath_norm_le (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) : ‖restrictPath hac hcd hdb u‖ ≤ ‖u‖ := by
  calc
    ‖restrictPath hac hcd hdb u‖ =
        max ‖energyPath (intervalMeasure c d) (restrictPath hac hcd hdb u)‖
          ‖gradientCoordinates (intervalMeasure c d) (restrictPath hac hcd hdb u)‖ :=
      path_norm_eq (intervalMeasure c d) (restrictPath hac hcd hdb u)
    _ ≤ max ‖energyPath (intervalMeasure a b) u‖
        ‖gradientCoordinates (intervalMeasure a b) u‖ :=
      max_le_max (restrictPath_energy_norm_le hac hcd hdb u)
        (restrictPath_W_norm_le hac hcd hdb u)
    _ = ‖u‖ := (path_norm_eq (intervalMeasure a b) u).symm

/-- The new initial value is the original path's value at the new left endpoint. -/
theorem restrictPath_initial (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    energyPath (intervalMeasure c d) (restrictPath hac hcd hdb u) ⟨c, le_rfl, hcd⟩ =
      energyPath (intervalMeasure a b) u ⟨c, hac, hcd.trans hdb⟩ := rfl

theorem restrictPath_initial_of_eq (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (u0 : EnergyState)
    (hu0 : energyPath (intervalMeasure a b) u ⟨c, hac, hcd.trans hdb⟩ = u0) :
    energyPath (intervalMeasure c d) (restrictPath hac hcd hdb u) ⟨c, le_rfl, hcd⟩ = u0 := hu0

@[simp] theorem restrictPath_self (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) :
    restrictPath le_rfl hab le_rfl u = u := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  rfl

@[simp] theorem restrictPath_trans {e f : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hce : c ≤ e) (hef : e ≤ f) (hfd : f ≤ d)
    (u : CriticalPath (intervalMeasure a b)) :
    restrictPath hce hef hfd (restrictPath hac hcd hdb u) =
      restrictPath (hac.trans hce) hef (hfd.trans hdb) u := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  rfl

/-- Restriction is linear on the actual compatible graph, hence respects differences. -/
def restrictPathLinear (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    CriticalPath (intervalMeasure a b) →ₗ[ℂ] CriticalPath (intervalMeasure c d) where
  toFun := restrictPath hac hcd hdb
  map_add' u v := by
    apply energyPath_injective
    apply ContinuousMap.ext
    intro t
    rfl
  map_smul' z u := by
    apply energyPath_injective
    apply ContinuousMap.ext
    intro t
    rfl

/-- E/W caps survive restriction, with the initial state updated to the restart time. -/
theorem restrictPath_mem_admissible (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) {B η : ℝ}
    (hE : ‖energyPath (intervalMeasure a b) u‖ ≤ B) (hW : ‖gradientCoordinates (intervalMeasure a b) u‖ ≤ η) :
    restrictPath hac hcd hdb u ∈ admissiblePaths (intervalMeasure c d)
      ⟨c, le_rfl, hcd⟩ (energyPath (intervalMeasure a b) u ⟨c, hac, hcd.trans hdb⟩) B η :=
  ⟨restrictPath_initial hac hcd hdb u,
    (restrictPath_energy_norm_le hac hcd hdb u).trans hE,
    (restrictPath_W_norm_le hac hcd hdb u).trans hW⟩

end HartreeF.CriticalPathRestriction
