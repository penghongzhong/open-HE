import FIntervalLpGluing
import FContinuousTimeJoin

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction

variable {a c b : ℝ}

theorem ae_adjacent_intervals (hac : a ≤ c) (hcb : c ≤ b)
    {P Q : ℝ → Prop} (hP : ∀ᵐ t ∂localMeasure a c, P t)
    (hQ : ∀ᵐ t ∂localMeasure c b, Q t) :
    ∀ᵐ t ∂localMeasure a b, (t ≤ c → P t) ∧ (c < t → Q t) := by
  have hL : ∀ᵐ t ∂(localMeasure a b).restrict (Set.Iic c), P t := by
    rw [localMeasure_restrict_left hcb]
    exact hP
  have hR : ∀ᵐ t ∂(localMeasure a b).restrict (Set.Iic c)ᶜ, Q t :=
    ae_mono (localMeasure_restrict_right_le hac) hQ
  rw [ae_restrict_iff' measurableSet_Iic] at hL
  rw [ae_restrict_iff' measurableSet_Iic.compl] at hR
  filter_upwards [hL, hR] with t htL htR
  exact ⟨htL, fun ht => htR (not_le.mpr ht)⟩

/-- Glue actual continuous energy trajectories at their identical endpoint value. -/
def gluedEnergyPath (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩) :
    C(ℝ, EnergyState) :=
  joinContinuous c (extendEnergyPath hac (energyPath _ u))
    (extendEnergyPath hcb (energyPath _ v))
    ((extendEnergyPath_val hac (energyPath _ u) ⟨c, hac, le_rfl⟩).trans
      (hm.trans (extendEnergyPath_val hcb (energyPath _ v) ⟨c, le_rfl, hcb⟩).symm))

theorem gluedEnergyPath_left (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (t : Set.Icc a c) :
    gluedEnergyPath hac hcb u v hm (t : ℝ) = energyPath _ u t := by
  change (if (t : ℝ) ≤ c then _ else _) = _
  rw [ite_eq_left t.property.2]
  exact extendEnergyPath_val hac (energyPath _ u) t

theorem gluedEnergyPath_right (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (t : Set.Icc c b) :
    gluedEnergyPath hac hcb u v hm (t : ℝ) = energyPath _ v t := by
  by_cases ht : (t : ℝ) ≤ c
  · have he : t = ⟨c, le_rfl, hcb⟩ := Subtype.ext (le_antisymm ht t.property.1)
    subst t
    exact (gluedEnergyPath_left hac hcb u v hm ⟨c, hac, le_rfl⟩).trans hm
  · change (if (t : ℝ) ≤ c then _ else _) = _
    rw [ite_eq_right ht]
    exact extendEnergyPath_val hcb (energyPath _ v) t

theorem local_gradient_compatible {d e : ℝ} (hde : d ≤ e)
    (u : CriticalPath (intervalMeasure d e)) (j : Fin 3) :
    ∀ᵐ t ∂localMeasure d e,
      energyGradientDistribution j (extendEnergyPath hde (energyPath _ u) t) =
        Lp.toTemperedDistribution (toLocalLp hde 10 (criticalGradient _ j u) t) := by
  filter_upwards [ae_clamp hde (u.property j),
    toLocalLp_coeFn hde 10 (criticalGradient _ j u)] with t hu ht
  rw [ht]
  exact hu

/-- Actual gluing in the unchanged canonical complete critical graph. -/
def gluePath (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩) :
    CriticalPath (intervalMeasure a b) := by
  let g : C(Set.Icc a b, EnergyState) :=
    ⟨fun t => gluedEnergyPath hac hcb u v hm (t : ℝ),
      (gluedEnergyPath hac hcb u v hm).continuous.comp continuous_subtype_val⟩
  let w (j : Fin 3) := glueIntervalLp 10 hac hcb (criticalGradient _ j u) (criticalGradient _ j v)
  refine ⟨(g, w), ?_⟩
  intro j
  have he : ∀ᵐ t ∂localMeasure a b,
      energyGradientDistribution j (gluedEnergyPath hac hcb u v hm t) =
        Lp.toTemperedDistribution (gluedRepresentative 10 hac hcb
          (criticalGradient _ j u) (criticalGradient _ j v) t) := by
    filter_upwards [ae_adjacent_intervals hac hcb
      (local_gradient_compatible hac u j) (local_gradient_compatible hcb v j)] with t ht
    by_cases hc : t ≤ c
    · have hE : gluedEnergyPath hac hcb u v hm t =
          extendEnergyPath hac (energyPath _ u) t := ite_eq_left hc
      have hW : gluedRepresentative 10 hac hcb (criticalGradient _ j u)
          (criticalGradient _ j v) t = toLocalLp hac 10 (criticalGradient _ j u) t :=
        ite_eq_left hc
      exact (congrArg (energyGradientDistribution j) hE).trans
        ((ht.1 hc).trans (congrArg Lp.toTemperedDistribution hW).symm)
    · have hE : gluedEnergyPath hac hcb u v hm t =
          extendEnergyPath hcb (energyPath _ v) t := ite_eq_right hc
      have hW : gluedRepresentative 10 hac hcb (criticalGradient _ j u)
          (criticalGradient _ j v) t = toLocalLp hcb 10 (criticalGradient _ j v) t :=
        ite_eq_right hc
      exact (congrArg (energyGradientDistribution j) hE).trans
        ((ht.2 (lt_of_not_ge hc)).trans (congrArg Lp.toTemperedDistribution hW).symm)
  have hi := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae he
  filter_upwards [hi, glueIntervalLp_coeFn 10 hac hcb
    (criticalGradient _ j u) (criticalGradient _ j v)] with t ht hw
  change energyGradientDistribution j (gluedEnergyPath hac hcb u v hm (t : ℝ)) =
    Lp.toTemperedDistribution (glueIntervalLp 10 hac hcb
      (criticalGradient _ j u) (criticalGradient _ j v) t)
  rw [hw]
  exact ht

@[simp] theorem gluePath_energy (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (t : Set.Icc a b) :
    energyPath _ (gluePath hac hcb u v hm) t =
      gluedEnergyPath hac hcb u v hm (t : ℝ) := rfl

@[simp] theorem gluePath_gradient (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (j : Fin 3) :
    criticalGradient _ j (gluePath hac hcb u v hm) =
      glueIntervalLp 10 hac hcb (criticalGradient _ j u) (criticalGradient _ j v) := rfl

end HartreeF.CriticalPathGluing
