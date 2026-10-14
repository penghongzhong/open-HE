import FPaperStabilitySumNorm
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.EssentialEnergyCap
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open EndpointOutput TimeHolder HomogeneousStability ActualStrichartz
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient CriticalJointSources.jointFields

/-- The actual subtype interval measure has full support on a nondegenerate
closed interval. The closure of the open interior supplies both endpoints. -/
theorem intervalMeasure_isOpenPos {a b : ℝ} (hab : a < b) :
    (intervalMeasure a b).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, rfl⟩
  rcases hUne with ⟨x, hx⟩
  have hxcl : (x : ℝ) ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact x.property
  have hn : (V ∩ Ioo a b).Nonempty := mem_closure_iff.mp hxcl V hV hx
  have hp : 0 < (volume : Measure ℝ) (V ∩ Ioo a b) :=
    (hV.inter isOpen_Ioo).measure_pos volume hn
  change (Measure.comap ((↑) : Icc a b → ℝ) volume) _ ≠ 0
  rw [comap_subtype_coe_apply measurableSet_Icc]
  apply ne_of_gt (hp.trans_le (measure_mono ?_))
  intro y hy
  exact ⟨⟨y, hy.2.1.le, hy.2.2.le⟩, hy.1, rfl⟩

/-- A continuous real function on the actual positive closed interval obeys
its AE upper cap at every point, including the two endpoints. -/
theorem continuous_cap_of_ae {a b B : ℝ} (hab : a < b)
    (f : Icc a b → ℝ) (hf : Continuous f)
    (hcap : ∀ᵐ t ∂intervalMeasure a b, f t ≤ B) : ∀ t, f t ≤ B := by
  have : (intervalMeasure a b).IsOpenPosMeasure := intervalMeasure_isOpenPos hab
  exact (Measure.dense_of_ae hcap).induction (fun _ ht => ht)
    (isClosed_le hf continuous_const)

theorem pureGradient_energyPath_continuous {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) :
    Continuous (fun t => pureGradientNorm (energyPath _ u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact pureGradientNorm_tendsto
    (gradientTendsto_of_tendsto ((energyPath (intervalMeasure a b) u).continuous.tendsto t))

/-- The input is the literal paper essential-L-infinity, spatial L2 norm of
the actual complex Euclidean gradient, on the same path. -/
theorem pureGradient_ae_cap_of_actual_energy_cap {a b B : ℝ} (hB : 0 ≤ B)
    (u : CriticalPath (intervalMeasure a b))
    (hcap : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal B) :
    ∀ᵐ t ∂intervalMeasure a b, pureGradientNorm (energyPath _ u t) ≤ B := by
  have hm := spatial_lp_time_measurable (intervalMeasure a b) volume 2
    (by norm_num) (by norm_num) (jointComplexGradient u) (jointComplexGradient_joint u)
  have heq : (fun t => eLpNorm (jointComplexGradient u t) 2 volume) =ᵐ[intervalMeasure a b]
      (fun t => eLpNorm (energyComplexGradient (energyPath _ u t)) 2 volume) := by
    filter_upwards [jointComplexGradient_slice_eq u] with t ht
    exact eLpNorm_congr_ae ht
  have hmactual := hm.congr heq
  have hb : eLpNormEssSup
      (fun t => eLpNorm (energyComplexGradient (energyPath _ u t)) 2 volume)
      (intervalMeasure a b) ≤ ENNReal.ofReal B :=
    (eLpNorm_exponent_top hmactual).symm.le.trans hcap
  filter_upwards [ae_le_eLpNormEssSup (μ := intervalMeasure a b)
    (f := fun t => eLpNorm (energyComplexGradient (energyPath _ u t)) 2 volume)] with t ht
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  calc
    _ = eLpNorm (energyComplexGradient (energyPath _ u t)) 2 volume :=
      (energyComplexGradient_L2_eq_pure _).symm
    _ ≤ eLpNormEssSup
        (fun t => eLpNorm (energyComplexGradient (energyPath _ u t)) 2 volume)
        (intervalMeasure a b) := by simpa only [enorm_eq_self] using ht
    _ ≤ _ := hb

/-- This closes the positive-interval energy-input conversion. The strict
length hypothesis is essential: singleton existence is handled separately. -/
theorem pureGradient_cap_of_actual_energy_cap {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (u : CriticalPath (intervalMeasure a b))
    (hcap : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal B) :
    ∀ t, pureGradientNorm (energyPath _ u t) ≤ B :=
  continuous_cap_of_ae hab _ (pureGradient_energyPath_continuous u)
    (pureGradient_ae_cap_of_actual_energy_cap hB u hcap)

theorem actual_energy_cap_endpoints {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (u : CriticalPath (intervalMeasure a b))
    (hcap : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal B) :
    pureGradientNorm (energyPath _ u ⟨a, le_rfl, hab.le⟩) ≤ B ∧
    pureGradientNorm (energyPath _ u ⟨b, hab.le, le_rfl⟩) ≤ B :=
  ⟨pureGradient_cap_of_actual_energy_cap hab hB u hcap _,
    pureGradient_cap_of_actual_energy_cap hab hB u hcap _⟩

/-- The original graph-energy cap uses exactly the already established
Sobolev factor A = max(K^(1/6),1), now from the paper's actual essential cap. -/
theorem energyPath_norm_le_of_actual_energy_cap {K B a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a < b) (hB : 0 ≤ B)
    (u : CriticalPath (intervalMeasure a b))
    (hcap : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal B) :
    ‖energyPath (intervalMeasure a b) u‖ ≤ max (K^((6 : ℝ)⁻¹)) 1 * B :=
  energyPath_norm_le_of_pure_cap hSob hB u
    (pureGradient_cap_of_actual_energy_cap hab hB u hcap)

theorem criticalPath_norm_le_of_actual_energy_W_caps {K B R a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a < b) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (u : CriticalPath (intervalMeasure a b))
    (hE : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal B)
    (hW : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal R) :
    ‖u‖ ≤ max (max (K^((6 : ℝ)⁻¹)) 1 * B) R :=
  criticalPath_norm_le_of_paper_caps hSob hB hR u
    (pureGradient_cap_of_actual_energy_cap hab hB u hE) hW

end HartreeF.EssentialEnergyCap
