import LocalFactorDifference
import PotentialDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain

/-- Bilinear decomposition of the actual complex forcing difference. -/
theorem forcing_sub (α c : ℝ) (u v : Space → ℂ) :
    forcing α c u-forcing α c v =
      (potential α c u-potential α c v) • localFactor α u +
        potential α c v • (localFactor α u-localFactor α v) := by
  ext x
  change (potential α c u x) • localFactor α u x - (potential α c v x) • localFactor α v x =
    (potential α c u x-potential α c v x) • localFactor α u x +
    (potential α c v x) • (localFactor α u x-localFactor α v x)
  module

/-- Exact Holder exponents yield a finite real-norm forcing difference bound. -/
theorem forcing_difference_product_bound {α c : ℝ} (hH : OrdinaryHLS α c)
    {u v : Space → ℂ} (hu : MemLp u 6 volume) (hv : MemLp v 6 volume) :
    (eLpNorm (forcing α c u-forcing α c v) (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
      (eLpNorm (potential α c u-potential α c v)
        (ENNReal.ofReal (potentialExponent α)) volume).toReal *
      (eLpNorm u 6 volume).toReal^(2+α) +
      (eLpNorm (potential α c v) (ENNReal.ofReal (potentialExponent α)) volume).toReal *
      (eLpNorm (localFactor α u-localFactor α v)
        (ENNReal.ofReal (energyOuterExponent α)) volume).toReal := by
  let r := ENNReal.ofReal (potentialExponent α)
  let s := ENNReal.ofReal (energyOuterExponent α)
  let q := ENNReal.ofReal (6/5 : ℝ)
  let : ENNReal.HolderTriple r s q := (energy_holder hH.order_pos hH.order_lt_three).ennrealOfReal
  obtain ⟨C,hC⟩ := potential_domain_bound hH
  have hpu : MemLp (potential α c u) r volume := (hC u hu).2.1
  have hpv : MemLp (potential α c v) r volume := (hC v hv).2.1
  have hlu : MemLp (localFactor α u) s volume :=
    localFactor_memLp (p := 6) hH.order_pos (by simpa using hu)
  have hlv : MemLp (localFactor α v) s volume :=
    localFactor_memLp (p := 6) hH.order_pos (by simpa using hv)
  have he : eLpNorm (forcing α c u-forcing α c v) q volume ≤
      eLpNorm (potential α c u-potential α c v) r volume * eLpNorm (localFactor α u) s volume +
      eLpNorm (potential α c v) r volume * eLpNorm (localFactor α u-localFactor α v) s volume := by
    rw [forcing_sub]
    refine (eLpNorm_add_le (by norm_num [q])).trans (add_le_add ?_ ?_)
    · exact eLpNorm_smul_le_mul_eLpNorm (hpu.sub hpv).aestronglyMeasurable hlu.aestronglyMeasurable
    · exact eLpNorm_smul_le_mul_eLpNorm hpv.aestronglyMeasurable (hlu.sub hlv).aestronglyMeasurable
  have hn1 : eLpNorm (potential α c u-potential α c v) r volume *
      eLpNorm (localFactor α u) s volume ≠ ∞ :=
    ENNReal.mul_ne_top (hpu.sub hpv).eLpNorm_ne_top hlu.eLpNorm_ne_top
  have hn2 : eLpNorm (potential α c v) r volume *
      eLpNorm (localFactor α u-localFactor α v) s volume ≠ ∞ :=
    ENNReal.mul_ne_top hpv.eLpNorm_ne_top (hlu.sub hlv).eLpNorm_ne_top
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hn1,hn2⟩) he
  rw [ENNReal.toReal_add hn1 hn2, ENNReal.toReal_mul, ENNReal.toReal_mul] at ht
  have hluNorm : eLpNorm (localFactor α u) s volume = eLpNorm u 6 volume^(2+α) := by
    simpa only [s, energyOuterExponent, ENNReal.ofReal_ofNat] using
      localFactor_eLpNorm (p := 6) hH.order_pos hu.aestronglyMeasurable
  rw [hluNorm, ← ENNReal.toReal_rpow] at ht
  exact ht

/-- Explicit finite real-norm local Lipschitz estimate, valid for all 0<alpha<3. -/
theorem forcing_difference_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ u v : Space → ℂ, MemLp u 6 volume → MemLp v 6 volume →
      (eLpNorm (forcing α c u-forcing α c v) (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
      (C : ℝ) * ((3+α)*((eLpNorm u 6 volume).toReal^(2+α)+
          (eLpNorm v 6 volume).toReal^(2+α))*(eLpNorm u 6 volume).toReal^(2+α) +
        (eLpNorm v 6 volume).toReal^(3+α)*(2+α)*
          ((eLpNorm u 6 volume).toReal^(1+α)+(eLpNorm v 6 volume).toReal^(1+α))) *
        (eLpNorm (u-v) 6 volume).toReal := by
  obtain ⟨C,hC⟩ := potential_difference_domain_bound hH
  refine ⟨C,fun u v hu hv => ?_⟩
  have hpd := (hC u v hu hv).2.1
  have hpv := (hC u v hu hv).2.2
  have hdd := EnergyContinuity.powerDensity_difference_bound hH.order_pos hH.order_lt_three hu hv
  have hld := localFactor_difference_bound hH.order_pos hH.order_lt_three hu hv
  have hddC := mul_le_mul_of_nonneg_left hdd C.coe_nonneg
  have hpd' := hpd.trans hddC
  have h1 := mul_le_mul_of_nonneg_right hpd'
    (Real.rpow_nonneg (show 0 ≤ (eLpNorm u 6 volume).toReal from ENNReal.toReal_nonneg) (2+α))
  have h2 := mul_le_mul hpv hld ENNReal.toReal_nonneg
    (mul_nonneg C.coe_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg (3+α)))
  exact (forcing_difference_product_bound hH hu hv).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- On every L6 ball the literal forcing has a finite Lipschitz constant. -/
theorem forcing_difference_bound_on_ball {α c : ℝ} (hH : OrdinaryHLS α c)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : Space → ℂ,
      MemLp u 6 volume → MemLp v 6 volume →
      (eLpNorm u 6 volume).toReal ≤ R → (eLpNorm v 6 volume).toReal ≤ R →
      (eLpNorm (forcing α c u-forcing α c v) (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
        L*(eLpNorm (u-v) 6 volume).toReal := by
  obtain ⟨C,hC⟩ := forcing_difference_bound hH
  refine ⟨(C : ℝ)*((3+α)*(R^(2+α)+R^(2+α))*R^(2+α)+
    R^(3+α)*(2+α)*(R^(1+α)+R^(1+α))), ?_, ?_⟩
  · have hα := hH.order_pos
    positivity
  · intro u v hu hv hRu hRv
    refine (hC u v hu hv).trans ?_
    have ha1 : 0 ≤ 1+α := by linarith [hH.order_pos]
    have ha2 : 0 ≤ 2+α := by linarith [hH.order_pos]
    have ha3 : 0 ≤ 3+α := by linarith [hH.order_pos]
    gcongr

#print axioms forcing_sub
#print axioms forcing_difference_product_bound
#print axioms forcing_difference_bound
#print axioms forcing_difference_bound_on_ball
end HartreeF.ForcingContinuity
