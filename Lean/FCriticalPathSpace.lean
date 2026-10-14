import FEnergyBanach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! A genuine critical path graph over the canonical C43 energy state.
The three Bochner L10_t L(30/13)_x coordinates represent its distributional
gradients on one full-measure set, rather than a separate set for each test.
Completeness is proved from closedness in the explicit native Banach product. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathSpace
open EnergySpace

abbrev criticalExponent : ℝ≥0∞ := ENNReal.ofReal (30 / 13 : ℝ)
instance criticalExponent_one_le : Fact (1 ≤ criticalExponent) := ⟨by norm_num⟩
instance ten_one_le : Fact ((1 : ℝ≥0∞) ≤ 10) := ⟨by norm_num⟩

abbrev SpatialCritical := Lp ℂ criticalExponent (volume : Measure V)

/-- Actual Schwartz testing of an Lp class, with the ordinary integral formula. -/
def spatialTest (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : Test) :
    Lp ℂ p (volume : Measure V) →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)

theorem spatialTest_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : Test)
    (f : Lp ℂ p (volume : Measure V)) :
    spatialTest p φ f = ∫ x, φ x * f x := by
  change Lp.toTemperedDistribution f φ = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]

/-- Equality of actual distributions identifies representatives even when
their integrability exponents differ. -/
theorem spatial_ae_eq_of_distribution_eq {p q : ℝ≥0∞}
    [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (f : Lp ℂ p (volume : Measure V)) (g : Lp ℂ q (volume : Measure V))
    (h : Lp.toTemperedDistribution f = Lp.toTemperedDistribution g) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable hp.out) ((Lp.memLp g).locallyIntegrable hq.out)
  intro φ hφ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ φ) := by fun_prop
  have he := congrArg (fun D : TD => D (hc'.toSchwartzMap hφ')) h
  simpa using he

section Paths
variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
variable (μ : Measure T)

abbrev CriticalGradient := Lp SpatialCritical 10 μ
abbrev PathAmbient := C(T, EnergyState) × (Fin 3 → CriticalGradient μ)

/-- Distributional compatibility of each actual Bochner gradient coordinate
with the energy trajectory; the quantifier over tests is inside the a.e. set. -/
def Compatible (z : PathAmbient μ) : Prop :=
  ∀ j : Fin 3, ∀ᵐ t ∂μ,
    energyGradientDistribution j (z.1 t) = Lp.toTemperedDistribution (z.2 j t)

def criticalPathSubmodule : Submodule ℂ (PathAmbient μ) where
  carrier := Compatible μ
  zero_mem' := by
    intro j
    filter_upwards [Lp.coeFn_zero (E := SpatialCritical) (p := 10) (μ := μ)] with t ht
    change energyGradientDistribution j 0 = Lp.toTemperedDistribution ((0 : CriticalGradient μ) t)
    rw [ht]
    exact (map_zero _).trans (map_zero (Lp.toTemperedDistributionCLM ℂ volume criticalExponent)).symm
  add_mem' := by
    intro z w hz hw j
    filter_upwards [hz j, hw j, Lp.coeFn_add (z.2 j) (w.2 j)] with t hzt hwt ht
    change energyGradientDistribution j (z.1 t + w.1 t) =
      Lp.toTemperedDistribution ((z.2 j + w.2 j) t)
    rw [ht, map_add]
    change _ = (Lp.toTemperedDistributionCLM ℂ volume criticalExponent) (z.2 j t + w.2 j t)
    rw [map_add, hzt, hwt]
    rfl
  smul_mem' := by
    intro c z hz j
    filter_upwards [hz j, Lp.coeFn_smul c (z.2 j)] with t hzt ht
    change energyGradientDistribution j (c • z.1 t) =
      Lp.toTemperedDistribution ((c • z.2 j) t)
    rw [ht, map_smul]
    change _ = (Lp.toTemperedDistributionCLM ℂ volume criticalExponent) (c • z.2 j t)
    rw [map_smul, hzt]
    rfl

theorem criticalPathSubmodule_isClosed :
    IsClosed (criticalPathSubmodule μ : Set (PathAmbient μ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro z w hz hw
  change Compatible μ w
  intro j
  have hgrad : Tendsto (fun n => (z n).2 j) atTop (𝓝 (w.2 j)) :=
    ((continuous_apply j).comp continuous_snd).tendsto w |>.comp hw
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hgrad).exists_seq_tendsto_ae
  have hzall : ∀ᵐ t ∂μ, ∀ n : ℕ,
      energyGradientDistribution j ((z n).1 t) =
        Lp.toTemperedDistribution ((z n).2 j t) :=
    ae_all_iff.mpr (fun n => hz n j)
  filter_upwards [hae, hzall] with t ht hzt
  have henergy : Tendsto (fun n => energyGradientDistribution j ((z (ns n)).1 t))
      atTop (𝓝 (energyGradientDistribution j (w.1 t))) :=
    ((energyGradientDistribution j).continuous.comp
      ((ContinuousMap.evalCLM ℂ t).continuous.comp continuous_fst)).tendsto w
        |>.comp (hw.comp hns.tendsto_atTop)
  have hcritical : Tendsto (fun n => Lp.toTemperedDistribution ((z (ns n)).2 j t))
      atTop (𝓝 (Lp.toTemperedDistribution (w.2 j t))) :=
    (Lp.toTemperedDistributionCLM ℂ volume criticalExponent).continuous.tendsto _ |>.comp ht
  exact tendsto_nhds_unique (by simpa only [hzt] using henergy) hcritical

/-- The norm is the product maximum of the continuous energy sup norm and
the three actual Bochner critical-gradient norms. -/
abbrev CriticalPath := criticalPathSubmodule μ

instance criticalPath_complete : CompleteSpace (CriticalPath μ) :=
  (criticalPathSubmodule_isClosed μ).completeSpace_coe

def energyPath : CriticalPath μ →L[ℂ] C(T, EnergyState) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (criticalPathSubmodule μ).subtypeL

def criticalGradient (j : Fin 3) : CriticalPath μ →L[ℂ] CriticalGradient μ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (criticalPathSubmodule μ).subtypeL)

theorem energyPath_norm_le (u : CriticalPath μ) : ‖energyPath μ u‖ ≤ ‖u‖ :=
  le_max_left _ _

theorem criticalGradient_norm_le (u : CriticalPath μ) (j : Fin 3) :
    ‖criticalGradient μ j u‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.val.2 j).trans (le_max_right _ _)

theorem energyPath_value_norm_le (u : CriticalPath μ) (t : T) :
    ‖energyPath μ u t‖ ≤ ‖u‖ :=
  ((energyPath μ u).norm_coe_le_norm t).trans (energyPath_norm_le μ u)

omit [CompactSpace T] in
/-- Genuine representative agreement with C43's L2 gradients. -/
theorem criticalGradient_ae_eq (u : CriticalPath μ) (j : Fin 3) :
    ∀ᵐ t ∂μ, (energyGradient j (energyPath μ u t) : V → ℂ) =ᵐ[volume]
      (criticalGradient μ j u t : V → ℂ) := by
  filter_upwards [u.property j] with t ht
  exact spatial_ae_eq_of_distribution_eq _ _ ht

omit [CompactSpace T] in
theorem criticalGradient_memLp (u : CriticalPath μ) (j : Fin 3) :
    ∀ᵐ t ∂μ, MemLp (energyGradient j (energyPath μ u t)) criticalExponent volume := by
  filter_upwards [criticalGradient_ae_eq μ u j] with t ht
  exact (memLp_congr_ae ht).mpr (Lp.memLp (criticalGradient μ j u t))

omit [CompactSpace T] in
/-- The spacetime norm of the actual C43 gradient is exactly the norm of
its Bochner coordinate, so the graph supplies a genuine finite W norm. -/
theorem criticalGradient_eLpNorm (u : CriticalPath μ) (j : Fin 3) :
    eLpNorm (fun t => eLpNorm (energyGradient j (energyPath μ u t))
      criticalExponent volume) 10 μ = ‖criticalGradient μ j u‖ₑ := by
  calc
    _ = eLpNorm (fun t => ‖criticalGradient μ j u t‖ₑ) 10 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [criticalGradient_ae_eq μ u j] with t ht
      exact (eLpNorm_congr_ae ht).trans (Lp.enorm_def _).symm
    _ = eLpNorm (criticalGradient μ j u) 10 μ :=
      eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = _ := (Lp.enorm_def _).symm

omit [CompactSpace T] in
theorem criticalGradient_norm_profile_memLp (u : CriticalPath μ) (j : Fin 3) :
    MemLp (fun t => eLpNorm (energyGradient j (energyPath μ u t))
      criticalExponent volume) 10 μ := by
  have hnorm : (fun t => eLpNorm (energyGradient j (energyPath μ u t))
      criticalExponent volume) =ᵐ[μ] (fun t => ‖criticalGradient μ j u t‖ₑ) := by
    filter_upwards [criticalGradient_ae_eq μ u j] with t ht
    exact (eLpNorm_congr_ae ht).trans (Lp.enorm_def _).symm
  exact (memLp_congr_ae hnorm).mpr (Lp.memLp (criticalGradient μ j u)).enorm

omit [CompactSpace T] in
theorem criticalGradient_mixedNorm_ne_top (u : CriticalPath μ) (j : Fin 3) :
    eLpNorm (fun t => eLpNorm (energyGradient j (energyPath μ u t))
      criticalExponent volume) 10 μ ≠ ∞ := by
  rw [criticalGradient_eLpNorm]
  simpa only [Lp.enorm_def] using Lp.eLpNorm_ne_top (criticalGradient μ j u)

omit [CompactSpace T] in
theorem criticalGradient_distribution_derivative (u : CriticalPath μ) (j : Fin 3) :
    ∀ᵐ t ∂μ,
      LineDeriv.lineDerivOp (coordinate j) (energyDistribution (energyPath μ u t)) =
        Lp.toTemperedDistribution (criticalGradient μ j u t) := by
  filter_upwards [u.property j] with t ht
  exact (energyDistribution_derivative (energyPath μ u t) j).trans ht

omit [CompactSpace T] in
theorem criticalGradient_schwartz_test (u : CriticalPath μ) (j : Fin 3) :
    ∀ᵐ t ∂μ, ∀ φ : Test,
      (∫ x, φ x * energyGradient j (energyPath μ u t) x) =
        ∫ x, φ x * criticalGradient μ j u t x := by
  filter_upwards [u.property j] with t ht φ
  have he := congrArg (fun D : TD => D φ) ht
  simpa [energyGradientDistribution, energyPath, criticalGradient,
    Lp.toTemperedDistribution_apply, smul_eq_mul] using he

omit [CompactSpace T] in
/-- The Bochner coordinates cannot add arbitrary information: the continuous
energy trajectory uniquely determines every critical-gradient class. -/
theorem energyPath_injective : Function.Injective (energyPath μ) := by
  intro u v h
  change u.val.1 = v.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  funext j
  apply Lp.ext
  filter_upwards [u.property j, v.property j] with t hu hv
  rw [h] at hu
  exact Lp.ext (spatial_ae_eq_of_distribution_eq _ _ (hu.symm.trans hv))

omit [CompactSpace T] in
/-- Constructor from a continuous canonical energy path and actual Bochner
critical-gradient representatives, with their spatial class agreement. -/
def ofRepresentativeAgreement (g : C(T, EnergyState))
    (d : Fin 3 → CriticalGradient μ)
    (hd : ∀ j, ∀ᵐ t ∂μ,
      (energyGradient j (g t) : V → ℂ) =ᵐ[volume] (d j t : V → ℂ)) :
    CriticalPath μ := by
  refine ⟨(g, d), ?_⟩
  intro j
  filter_upwards [hd j] with t ht
  change Lp.toTemperedDistribution (energyGradient j (g t)) =
    Lp.toTemperedDistribution (d j t)
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]

theorem criticalPath_norm (u : CriticalPath μ) :
    ‖u‖ = max ‖energyPath μ u‖ ‖fun j => criticalGradient μ j u‖ := rfl

end Paths

/-- The concrete closed-interval time type is covered, including a degenerate
or empty interval; its natural measure is the pullback of Lebesgue measure. -/
abbrev intervalMeasure (a b : ℝ) : Measure (Set.Icc a b) :=
  Measure.comap ((↑) : Set.Icc a b → ℝ) volume

theorem closedInterval_criticalPath_complete (a b : ℝ) :
    CompleteSpace (CriticalPath (intervalMeasure a b)) := inferInstance

end HartreeF.CriticalPathSpace
