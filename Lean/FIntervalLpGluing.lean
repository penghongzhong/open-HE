import FIntervalLpRestriction
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Piecewise

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction

variable {a c b : ℝ}

/-- The left half of the actual compact interval carries exactly its old measure. -/
theorem localMeasure_restrict_left (hcb : c ≤ b) :
    (localMeasure a b).restrict (Set.Iic c) = localMeasure a c := by
  rw [Measure.restrict_restrict measurableSet_Iic]
  congr 1
  ext t
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  constructor
  · rintro ⟨hc, ha, hb⟩
    exact ⟨ha, hc⟩
  · rintro ⟨ha, hc⟩
    exact ⟨hc, ha, hc.trans hcb⟩

/-- The right open half is dominated by the old right-interval measure. -/
theorem localMeasure_restrict_right_le (_hac : a ≤ c) :
    (localMeasure a b).restrict (Set.Iic c)ᶜ ≤ localMeasure c b := by
  rw [Measure.restrict_restrict measurableSet_Iic.compl]
  apply Measure.restrict_mono_set
  intro t ht
  exact ⟨(lt_of_not_ge (show ¬ t ≤ c from ht.1)).le, ht.2.2⟩

section Bochner
variable {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)

/-- The actual adjacent Lp representatives, glued using the same real time. -/
def gluedRepresentative (hac : a ≤ c) (hcb : c ≤ b)
    (f : Lp E p (intervalMeasure a c)) (g : Lp E p (intervalMeasure c b)) : ℝ → E :=
  (Set.Iic c).piecewise (toLocalLp hac p f) (toLocalLp hcb p g)

theorem gluedRepresentative_memLp (hac : a ≤ c) (hcb : c ≤ b)
    (f : Lp E p (intervalMeasure a c)) (g : Lp E p (intervalMeasure c b)) :
    MemLp (gluedRepresentative p hac hcb f g) p (localMeasure a b) := by
  apply MemLp.piecewise measurableSet_Iic.nullMeasurableSet
  · rw [localMeasure_restrict_left hcb]
    exact Lp.memLp _
  · exact (Lp.memLp (toLocalLp hcb p g)).mono_measure (localMeasure_restrict_right_le hac)

def glueIntervalLp (hac : a ≤ c) (hcb : c ≤ b)
    (f : Lp E p (intervalMeasure a c)) (g : Lp E p (intervalMeasure c b)) :
    Lp E p (intervalMeasure a b) :=
  toIntervalLp a b p ((gluedRepresentative_memLp p hac hcb f g).toLp
    (gluedRepresentative p hac hcb f g))

theorem glueIntervalLp_coeFn (hac : a ≤ c) (hcb : c ≤ b)
    (f : Lp E p (intervalMeasure a c)) (g : Lp E p (intervalMeasure c b)) :
    glueIntervalLp p hac hcb f g =ᵐ[intervalMeasure a b]
      fun t => gluedRepresentative p hac hcb f g (t : ℝ) := by
  have h := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae
    (MemLp.coeFn_toLp (gluedRepresentative_memLp p hac hcb f g))
  filter_upwards [toIntervalLp_coeFn a b p
    ((gluedRepresentative_memLp p hac hcb f g).toLp (gluedRepresentative p hac hcb f g)), h]
    with t ht hh
  exact ht.trans hh

end Bochner
end HartreeF.CriticalPathGluing
