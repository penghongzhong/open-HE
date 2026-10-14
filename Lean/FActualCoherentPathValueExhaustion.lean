import FActualSValueRealization
import FCoherentL10Exhaustion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources CriticalPathRestriction
open CriticalSourceBounds TimeHolder SobolevStretch StationarySelfTest ActualSTail
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  pathValueLp globalPathValue

/-- Extension by zero retains the actual states of any compact path, without
requiring that the path solve an equation. -/
theorem globalPathValue_actual_curve (hDensity : OrdinaryH1Density)
    {K a b : ℝ} (hSob : OrdinarySobolev K) (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (q : ℝ → EnergyState)
    (hq : ∀ t : Icc a b, energyPath _ u t=q t) :
    ∀ᵐ t ∂localMeasure a b,
      (globalPathValue hDensity hSob hab u t : Space → ℂ) =ᵐ[volume] energyValue (q t) := by
  filter_upwards [extendValueLp_restrict_coeFn (toLocalLp hab 10 (pathValueLp hDensity hSob u)),
    toLocalLp_coeFn hab 10 (pathValueLp hDensity hSob u),
    ae_clamp hab (pathValueLp_coeFn hDensity hSob u), ae_restrict_mem measurableSet_Icc]
    with t he hl hv ht
  unfold globalPathValue
  rw [he, hl]
  have hs : energyPath _ u (Set.projIcc a b hab t)=q t := by
    exact (hq (Set.projIcc a b hab t)).trans
      (congrArg (fun v : Icc a b => q v) (Set.projIcc_of_mem hab ht))
  exact hv.trans (Eventually.of_forall fun x => congrArg (fun z : EnergyState => energyValue z x) hs)

/-- Uniform actual S bounds on nested compact restrictions produce one global
L10_t L10_x function of precisely the original states on their whole union.
Neither a global Lp witness nor coherence of chosen Lp representatives is an
input: representative coherence follows from the common actual energy states. -/
theorem exists_actual_global_value_of_coherent_paths (hDensity : OrdinaryH1Density)
    {K M : ℝ} (hSob : OrdinarySobolev K) (hM : 0 ≤ M)
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b) (hab : ∀ n, a n ≤ b n)
    (q : ℝ → EnergyState) (Q : ∀ n, CriticalPath (intervalMeasure (a n) (b n)))
    (hQ : ∀ n (t : Icc (a n) (b n)), energyPath _ (Q n) t=q t)
    (hS : ∀ n, pathValueSize (intervalMeasure (a n) (b n)) (Q n) ≤ ENNReal.ofReal M) :
    ∃ F : GlobalValueSpace, ‖F‖ ≤ M ∧
      (∀ᵐ t ∂volume.restrict (⋃ n, Icc (a n) (b n)),
        (F t : Space → ℂ) =ᵐ[volume] energyValue (q t)) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  let f : ℕ → GlobalValueSpace := fun n => globalPathValue hDensity hSob (hab n) (Q n)
  have hfbound : ∀ n, ‖f n‖ ≤ M := by
    intro n
    change ‖globalPathValue hDensity hSob (hab n) (Q n)‖ ≤ M
    rw [globalPathValue_norm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hS n)).trans_eq
      (ENNReal.toReal_ofReal hM)
  have hfsupport : ∀ n, ∀ᵐ t ∂volume, t ∉ Icc (a n) (b n) → f n t=0 :=
    fun n => globalPathValue_support hDensity hSob (hab n) (Q n)
  have hfactual : ∀ n, ∀ᵐ t ∂localMeasure (a n) (b n),
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (q t) :=
    fun n => globalPathValue_actual_curve hDensity hSob (hab n) (Q n) q (hQ n)
  have hfcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂volume,
      t ∈ Icc (a n) (b n) → f m t=f n t := by
    intro n m hnm
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hfactual n,
      ae_mono (localMeasure_mono (ha hnm) (hb hnm)) (hfactual m)] with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F,hFM,hFlocal,hFzero⟩ := FEndpoint.exists_coherent_L10_exhaustion
    (fun n => Icc (a n) (b n)) f M hfbound hfsupport hfcoherent
  have hactual : ∀ᵐ t ∂volume, ∀ n, t ∈ Icc (a n) (b n) →
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (q t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hfactual n)
  have hlocal : ∀ᵐ t ∂volume, ∀ n, t ∈ Icc (a n) (b n) → F t=f n t :=
    ae_all_iff.mpr hFlocal
  refine ⟨F,hFM,?_,hFzero⟩
  filter_upwards [ae_restrict_of_ae hactual,ae_restrict_of_ae hlocal,
    ae_restrict_mem (MeasurableSet.iUnion fun _ => measurableSet_Icc)] with t ht hl hm
  obtain ⟨n,hn⟩ := mem_iUnion.mp hm
  rw [hl n hn]
  exact ht n hn

#print axioms globalPathValue_actual_curve
#print axioms exists_actual_global_value_of_coherent_paths
end HartreeF.IntervalNormExhaustion
