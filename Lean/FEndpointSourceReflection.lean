import FRetardedScalarL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure

/-! Actual whole-line endpoint sources, restricted before taking the norm,
then reflected by a measure-preserving sign. No nonlinear time reversal. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.MassRecovery
open Retarded FreeFlow

abbrev OneSpace := Lp ℂ 1 (volume : Measure V)
abbrev EndpointOne := Lp OneSpace 2 (volume : Measure ℝ)

def timeSign (σ s : ℝ) : ℝ := σ * s

theorem timeSign_preserving {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    MeasurePreserving (timeSign σ) (volume : Measure ℝ) volume := by
  unfold timeSign
  rcases hσ with rfl | rfl
  · convert (MeasurePreserving.id (volume : Measure ℝ)) using 1
    funext s
    exact one_mul s
  · simpa only [neg_one_mul] using (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem timeSign_embedding {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    MeasurableEmbedding (timeSign σ) := by
  unfold timeSign
  rcases hσ with rfl | rfl
  · convert (MeasurableEmbedding.id (α := ℝ)) using 1
    funext s
    exact one_mul s
  · simpa only [neg_one_mul] using (measurableEmbedding_neg : MeasurableEmbedding (Neg.neg : ℝ → ℝ))

theorem timeSign_involution {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (s : ℝ) :
    timeSign σ (timeSign σ s) = s := by
  rcases hσ with rfl | rfl <;> simp [timeSign]

def physicalTail (σ t : ℝ) : Set ℝ := timeSign σ ⁻¹' Ici t

def physicalWindow (σ t T : ℝ) : Set ℝ := timeSign σ ⁻¹' Icc t T

theorem physicalTail_measurable (σ t : ℝ) : MeasurableSet (physicalTail σ t) :=
  measurableSet_Ici.preimage (by unfold timeSign; fun_prop)

theorem physicalWindow_measurable (σ t T : ℝ) : MeasurableSet (physicalWindow σ t T) :=
  measurableSet_Icc.preimage (by unfold timeSign; fun_prop)

def tailSource {E : Type*} [NormedAddCommGroup E] (t : ℝ)
    (Q : Lp E 2 (volume : Measure ℝ)) : Lp E 2 (volume : Measure ℝ) :=
  (MemLp.indicator measurableSet_Ici.nullMeasurableSet (Lp.memLp Q)).toLp
    ((Ici t).indicator Q)

theorem tailSource_coe {E : Type*} [NormedAddCommGroup E] (t : ℝ)
    (Q : Lp E 2 (volume : Measure ℝ)) :
    (tailSource t Q : ℝ → E) =ᵐ[volume] (Ici t).indicator Q :=
  (MemLp.indicator measurableSet_Ici.nullMeasurableSet (Lp.memLp Q)).coeFn_toLp

def tailNorm {E : Type*} [NormedAddCommGroup E] (t : ℝ)
    (Q : Lp E 2 (volume : Measure ℝ)) : ℝ := ‖tailSource t Q‖

theorem tailNorm_eq_restricted {E : Type*} [NormedAddCommGroup E] (t : ℝ)
    (Q : Lp E 2 (volume : Measure ℝ)) :
    tailNorm t Q = (eLpNorm (Q : ℝ → E) 2 (volume.restrict (Ici t))).toReal := by
  rw [tailNorm, tailSource, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici.nullMeasurableSet]

def reflectedTail {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ)
    (Q : EndpointSource) : EndpointSource :=
  Lp.compMeasurePreserving (timeSign σ) (timeSign_preserving hσ) (tailSource t Q)

theorem reflectedTail_norm {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ)
    (Q : EndpointSource) : ‖reflectedTail hσ t Q‖ = tailNorm t Q :=
  Lp.norm_compMeasurePreserving _ _

theorem reflectedTail_coe {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ)
    (Q : EndpointSource) :
    (reflectedTail hσ t Q : ℝ → SourceSpace) =ᵐ[volume]
      (fun y => (Ici t).indicator Q (timeSign σ y)) := by
  have htail := (timeSign_preserving hσ).quasiMeasurePreserving.tendsto_ae.eventually
    (tailSource_coe t Q)
  filter_upwards [Lp.coeFn_compMeasurePreserving (tailSource t Q) (timeSign_preserving hσ),
    htail] with y h1 h2
  exact h1.trans h2

theorem physicalWindow_mono (σ t : ℝ) : Monotone (fun n : ℕ => physicalWindow σ t (n + 1)) := by
  intro n m hnm y hy
  exact ⟨hy.1, hy.2.trans (by exact_mod_cast Nat.add_le_add_right hnm 1)⟩

theorem physicalWindow_union (σ t : ℝ) :
    (⋃ n : ℕ, physicalWindow σ t (n + 1)) = physicalTail σ t := by
  ext y
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact hn.1
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (timeSign σ y)
    exact mem_iUnion.mpr ⟨n, h, by linarith⟩

theorem scalar_window_tendsto {σ : ℝ} (t : ℝ) (f : ℝ → ℂ)
    (hf : IntegrableOn f (physicalTail σ t)) :
    Tendsto (fun n : ℕ => ∫ y in physicalWindow σ t (n + 1), f y) atTop
      (𝓝 (∫ y in physicalTail σ t, f y)) := by
  have h := tendsto_setIntegral_of_monotone
    (fun n : ℕ => physicalWindow_measurable σ t (n + 1)) (physicalWindow_mono σ t)
    (by simpa only [physicalWindow_union] using hf)
  simpa only [physicalWindow_union] using h

end HartreeF.MassRecovery
