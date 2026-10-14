import FRetardedLinearity
import Mathlib.MeasureTheory.Function.UniformIntegrable

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology symmDiff
namespace HartreeF.Retarded

/-- Multiplication by a measurable time indicator in the endpoint source space. -/
def endpointCutoff (J : Set ℝ) (hJ : MeasurableSet J) (F : EndpointSource) :
    EndpointSource :=
  ((Lp.memLp F).indicator hJ.nullMeasurableSet).toLp (J.indicator F)

theorem endpointCutoff_coe (J : Set ℝ) (hJ : MeasurableSet J) (F : EndpointSource) :
    ⇑(endpointCutoff J hJ F) =ᵐ[volume] J.indicator F :=
  MemLp.coeFn_toLp _

/-- Strong convergence of cutoffs when the symmetric difference has vanishing measure. -/
theorem endpointCutoff_tendsto {ι : Type*} {l : Filter ι}
    (J : ι → Set ℝ) (hJ : ∀ i, MeasurableSet (J i))
    (K : Set ℝ) (hK : MeasurableSet K) (F : EndpointSource)
    (hm : Tendsto (fun i => volume (J i ∆ K)) l (𝓝 0)) :
    Tendsto (fun i => endpointCutoff (J i) (hJ i) F) l (𝓝 (endpointCutoff K hK F)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := (Lp.memLp F).eLpNorm_indicator_le (by norm_num) (by simp) hε
  filter_upwards [(tendsto_order.1 hm).2 δ hδ] with i hi
  rw [eLpNorm_congr_ae ((endpointCutoff_coe (J i) (hJ i) F).sub
    (endpointCutoff_coe K hK F)),
    eLpNorm_indicator_sub_indicator F (hJ i).nullMeasurableSet hK.nullMeasurableSet]
  exact hsmall _ ((hJ i).symmDiff hK).nullMeasurableSet hi.le

/-- A moving endpoint interval has symmetric difference of arbitrarily small measure. -/
private theorem tendsto_volume_symmDiff_of_subset (J : ℝ → Set ℝ) (t : ℝ)
    (hJ : ∀ s, J s ∆ J t ⊆ Icc (min s t) (max s t)) :
    Tendsto (fun s => volume (J s ∆ J t)) (𝓝 t) (𝓝 0) := by
  have hm : Tendsto (fun s : ℝ => ENNReal.ofReal (max s t - min s t)) (𝓝 t) (𝓝 0) := by
    convert (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((continuous_id.max continuous_const).sub
        (continuous_id.min continuous_const)).tendsto t)) using 1 <;> first | rfl | simp
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hm) ε hε] with s hs
  exact (measure_mono (hJ s)).trans (by simpa using hs)

theorem endpointCutoff_Iio_continuous (F : EndpointSource) :
    Continuous (fun t : ℝ => endpointCutoff (Iio t) measurableSet_Iio F) := by
  apply continuous_iff_continuousAt.2
  intro t
  apply endpointCutoff_tendsto (fun s => Iio s) (fun _ => measurableSet_Iio)
  apply tendsto_volume_symmDiff_of_subset
  intro s x hx
  simp only [mem_symmDiff, mem_Iio, mem_Icc] at *
  grind

theorem endpointCutoff_Ioc_continuous (a : ℝ) (F : EndpointSource) :
    Continuous (fun t : ℝ => endpointCutoff (Ioc a t) measurableSet_Ioc F) := by
  apply continuous_iff_continuousAt.2
  intro t
  apply endpointCutoff_tendsto (fun s => Ioc a s) (fun _ => measurableSet_Ioc)
  apply tendsto_volume_symmDiff_of_subset
  intro s x hx
  simp only [mem_symmDiff, mem_Ioc, mem_Icc] at *
  grind

end HartreeF.Retarded
