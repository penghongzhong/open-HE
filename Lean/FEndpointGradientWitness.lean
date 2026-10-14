import FOrdinaryEndpointOutput
import FActualCriticalPathProducer
import FIntervalNestedLpTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded
open scoped ENNReal NNReal

instance endpointSpatial_ne_top : Fact ((6 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev EndpointGradient {T : Type*} [MeasurableSpace T] (μ : Measure T) :=
  Lp (Lp ℂ 6 (volume : Measure Space)) 2 μ

/-- A genuine L2_t L6_x coordinate of each actual L2 spatial derivative.
This witness is constructed below; it is not an analytic premise. -/
structure EndpointGradientWitness {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g : T → EnergyState) where
  field : Fin 3 → EndpointGradient μ
  agrees : ∀ j, ∀ᵐ t ∂μ, (field j t : Space → ℂ) =ᵐ[volume] energyGradient j (g t)

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} {g h : T → EnergyState}

theorem EndpointGradientWitness.mixedNorm_eq (W : EndpointGradientWitness μ g) (j : Fin 3) :
    mixedNorm μ volume 2 6 (fun t => energyGradient j (g t)) = ‖W.field j‖ₑ := by
  calc
    _ = eLpNorm (fun t => ‖W.field j t‖ₑ) 2 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [W.agrees j] with t ht
      exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
    _ = eLpNorm (W.field j) 2 μ := eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = _ := (Lp.enorm_def _).symm

theorem EndpointGradientWitness.mixedNorm_finite (W : EndpointGradientWitness μ g)
    (j : Fin 3) : mixedNorm μ volume 2 6 (fun t => energyGradient j (g t)) ≠ ∞ := by
  rw [W.mixedNorm_eq j]
  exact enorm_ne_top

theorem EndpointGradientWitness.spatial_memLp (W : EndpointGradientWitness μ g)
    (j : Fin 3) : ∀ᵐ t ∂μ, MemLp (energyGradient j (g t)) 6 volume := by
  filter_upwards [W.agrees j] with t ht
  exact (Lp.memLp (W.field j t)).ae_eq ht

theorem EndpointGradientWitness.norm_profile_memLp (W : EndpointGradientWitness μ g)
    (j : Fin 3) : MemLp (fun t => eLpNorm (energyGradient j (g t)) 6 volume) 2 μ := by
  have he : (fun t => eLpNorm (energyGradient j (g t)) 6 volume) =ᵐ[μ]
      (fun t => ‖W.field j t‖ₑ) := by
    filter_upwards [W.agrees j] with t ht
    exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
  exact (memLp_congr_ae he).mpr (Lp.memLp (W.field j)).enorm

def EndpointGradientWitness.add (Wg : EndpointGradientWitness μ g)
    (Wh : EndpointGradientWitness μ h) : EndpointGradientWitness μ (fun t => g t + h t) where
  field j := Wg.field j + Wh.field j
  agrees j := by
    filter_upwards [Wg.agrees j, Wh.agrees j, Lp.coeFn_add (Wg.field j) (Wh.field j)]
      with t hgt hht hadd
    rw [hadd, Pi.add_apply, map_add]
    filter_upwards [hgt, hht, Lp.coeFn_add (Wg.field j t) (Wh.field j t),
      Lp.coeFn_add (energyGradient j (g t)) (energyGradient j (h t))] with x hgx hhx hd hx
    simp only [Pi.add_apply] at hd hx
    rw [hd, hx, hgx, hhx]

def EndpointGradientWitness.smul (c : ℂ) (W : EndpointGradientWitness μ g) :
    EndpointGradientWitness μ (fun t => c • g t) where
  field j := c • W.field j
  agrees j := by
    filter_upwards [W.agrees j, Lp.coeFn_smul c (W.field j)] with t ht hc
    rw [hc, Pi.smul_apply, map_smul]
    filter_upwards [ht, Lp.coeFn_smul c (W.field j t),
      Lp.coeFn_smul c (energyGradient j (g t))] with x hx hd he
    simp only [Pi.smul_apply] at hd he
    rw [hd, he, hx]

/-- Realization of an already specified joint representative on a local interval. -/
def intervalEndpointField (a b : ℝ) (d : ℝ → Space → ℂ)
    (hd : StronglyMeasurable (fun z : ℝ × Space => d z.1 z.2))
    (hf : mixedNorm volume volume 2 6 d ≠ ∞) : EndpointGradient (intervalMeasure a b) :=
  jointLpRealization (intervalMeasure a b) volume 2 6 (fun z => d z.1 z.2)
    ((hd.comp_measurable (measurable_subtype_coe.comp measurable_fst |>.prodMk
      measurable_snd)).aestronglyMeasurable)
    (finite_mixedNorm_ae_slice_memLp (intervalMeasure a b) volume 2 6
      (by norm_num) (by norm_num) (fun t => d t)
      (ne_top_of_le_ne_top hf (interval_mixedNorm_le_global a b 2 6 d)))
    (ne_top_of_le_ne_top hf (interval_mixedNorm_le_global a b 2 6 d))

theorem intervalEndpointField_agrees (a b : ℝ) (d : ℝ → Space → ℂ)
    (hd : StronglyMeasurable (fun z : ℝ × Space => d z.1 z.2))
    (hf : mixedNorm volume volume 2 6 d ≠ ∞) :
    ∀ᵐ t ∂intervalMeasure a b, (intervalEndpointField a b d hd hf t : Space → ℂ) =ᵐ[volume] d t :=
  jointLpRealization_coeFn _ _ _ _ _ _ _ _

theorem intervalEndpointField_enorm_le (a b : ℝ) (d : ℝ → Space → ℂ)
    (hd : StronglyMeasurable (fun z : ℝ × Space => d z.1 z.2))
    (hf : mixedNorm volume volume 2 6 d ≠ ∞) :
    ‖intervalEndpointField a b d hd hf‖ₑ ≤ mixedNorm volume volume 2 6 d := by
  unfold intervalEndpointField
  rw [jointLpRealization_enorm]
  exact interval_mixedNorm_le_global a b 2 6 d

/-- Transfer the derivative agreement to subtype time, after constructing the
endpoint Bochner field from the same global representative. -/
def intervalEndpointWitness (a b : ℝ) (g : ℝ → EnergyState)
    (d : Fin 3 → ℝ → Space → ℂ)
    (hd : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (hf : ∀ j, mixedNorm volume volume 2 6 (d j) ≠ ∞)
    (he : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t)) :
    EndpointGradientWitness (intervalMeasure a b) (fun t => g t) where
  field j := intervalEndpointField a b (d j) (hd j) (hf j)
  agrees j := by
    have hei := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae
      (ae_restrict_of_ae (he j))
    filter_upwards [hei, intervalEndpointField_agrees a b (d j) (hd j) (hf j)]
      with t ht hdj
    exact hdj.trans ht

/-- Exact transport to Lebesgue measure restricted to the same closed interval. -/
def EndpointGradientWitness.toLocal {a b : ℝ} (hab : a ≤ b)
    {g : Set.Icc a b → EnergyState} (W : EndpointGradientWitness (intervalMeasure a b) g) :
    EndpointGradientWitness (localMeasure a b) (fun t => g (Set.projIcc a b hab t)) where
  field j := toLocalLp hab 2 (W.field j)
  agrees j := by
    filter_upwards [ae_clamp hab (W.agrees j), toLocalLp_nested_coeFn hab 2 6 volume
      (W.field j)] with t ht hd
    exact hd.trans ht

theorem EndpointGradientWitness.toLocal_norm {a b : ℝ} (hab : a ≤ b)
    {g : Set.Icc a b → EnergyState} (W : EndpointGradientWitness (intervalMeasure a b) g)
    (j : Fin 3) : ‖(W.toLocal hab).field j‖ = ‖W.field j‖ :=
  toLocalLp_norm hab 2 (W.field j)

theorem EndpointGradientWitness.local_mixedNorm_eq {a b : ℝ} (hab : a ≤ b)
    {g : Set.Icc a b → EnergyState} (W : EndpointGradientWitness (intervalMeasure a b) g)
    (j : Fin 3) :
    mixedNorm (localMeasure a b) volume 2 6
      (fun t => energyGradient j (g (Set.projIcc a b hab t))) =
      mixedNorm (intervalMeasure a b) volume 2 6 (fun t => energyGradient j (g t)) := by
  rw [(W.toLocal hab).mixedNorm_eq, W.mixedNorm_eq, ← ofReal_norm, ← ofReal_norm,
    W.toLocal_norm hab j]

end HartreeF.EndpointOutput
