import ForcingDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain SobolevStretch ComplexIMS DotH1Topology

/-- The actual spatial forcing is in L^(6/5) from L6 alone. -/
theorem forcing_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} (hu : MemLp u 6 volume) :
    MemLp (forcing α c u) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  obtain ⟨C,hC⟩ := forcing_energy_domain_bound hH
  exact (hC u hu).1

/-- Arbitrary-filter strong continuity of the literal Hartree forcing L6→L^(6/5). -/
theorem strong_forcing_tendsto {ι : Type*} {l : Filter ι} {α c : ℝ}
    (hH : OrdinaryHLS α c) {u : ι → Space → ℂ} {v : Space → ℂ}
    (hu : ∀ i, MemLp (u i) 6 volume) (hv : MemLp v 6 volume)
    (ht : Tendsto (fun i => (eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0)) :
    Tendsto (fun i => (eLpNorm (forcing α c (u i)-forcing α c v)
      (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) l (𝓝 0) := by
  have htLp : Tendsto (fun i => (hu i).toLp (u i)) l (𝓝 (hv.toLp v)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [toLp_distance, Pi.sub_def] using ht
  have hnorm : Tendsto (fun i => (eLpNorm (u i) 6 volume).toReal)
      l (𝓝 (eLpNorm v 6 volume).toReal) := by
    simpa only [Lp.norm_toLp] using htLp.norm
  have hpow := hnorm.rpow_const (Or.inr (show 0 ≤ 2+α by linarith [hH.order_pos]))
  have htp := strong_potential_tendsto hH hu hv ht
  have htl := strong_localFactor_tendsto hH.order_pos hH.order_lt_three hu hv ht
  have hbound := (htp.mul hpow).add ((tendsto_const_nhds (x := (eLpNorm (potential α c v) (ENNReal.ofReal (potentialExponent α)) volume).toReal)).mul htl)
  simp only [zero_mul, mul_zero, zero_add] at hbound
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun i => forcing_difference_product_bound hH (hu i) hv) hbound

/-- Actual forcing continuity in the topology of the two weak L2 gradients alone. -/
theorem gradient_strong_forcing_tendsto {ι : Type*} {l : Filter ι} {α c : ℝ}
    (hH : OrdinaryHLS α c) (hS : SharpOrdinary.SharpOrdinarySobolev)
    {u : ι → HomogeneousData} {v : HomogeneousData}
    (ht : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => (eLpNorm (forcing α c (u i).u-forcing α c v.u)
      (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) l (𝓝 0) := by
  have htlp := ((lpData_continuous hS).tendsto v).comp ht
  have ht6 : Tendsto (fun i => (eLpNorm ((u i).u-v.u) 6 volume).toReal) l (𝓝 0) := by
    simpa only [Function.comp_apply, function_data_distance_eq, Pi.sub_def] using
      tendsto_iff_dist_tendsto_zero.mp htlp.fst_nhds
  exact strong_forcing_tendsto hH (fun i => (u i).domain.function_L6) v.domain.function_L6 ht6

local instance forcingExponent_ge_one : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) :=
  ⟨by norm_num⟩

/-- The actual forcing's L^(6/5) class associated to homogeneous data. -/
def forcingData {α c : ℝ} (hH : OrdinaryHLS α c) (u : HomogeneousData) :
    Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space) :=
  (forcing_memLp hH u.domain.function_L6).toLp (forcing α c u.u)

/-- Distance is exactly the finite real norm of the literal forcing difference. -/
theorem forcingData_distance {α c : ℝ} (hH : OrdinaryHLS α c) (u v : HomogeneousData) :
    dist (forcingData hH u) (forcingData hH v) =
      (eLpNorm (forcing α c u.u-forcing α c v.u)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal := by
  exact toLp_distance (forcing_memLp hH u.domain.function_L6) (forcing_memLp hH v.domain.function_L6)

/-- Genuine topological continuity; no target nonlinearity continuity hypothesis. -/
theorem forcingData_continuous {α c : ℝ} (hH : OrdinaryHLS α c)
    (hS : SharpOrdinary.SharpOrdinarySobolev) : Continuous (forcingData hH) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [forcingData_distance, id_eq] using
    gradient_strong_forcing_tendsto hH hS (u := id) (v := u) tendsto_id

#print axioms forcing_memLp
#print axioms strong_forcing_tendsto
#print axioms gradient_strong_forcing_tendsto
#print axioms forcingData_distance
#print axioms forcingData_continuous
end HartreeF.ForcingContinuity
