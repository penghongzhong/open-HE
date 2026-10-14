import HartreeGradientSingle
import DirectionalPotentialEnvelopes
import DirectionalCandidateAlgebra

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2Difference
open ForcingDomain GradientMajorants DerivativeMajorization

/-- The density difference allocation retains a positive power of each input
norm throughout the complete range 0 < alpha < 3. -/
theorem difference_density_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {V D : Space → ℝ} (hV : ∀ x, 0 ≤ V x) (hD : ∀ x, 0 ≤ D x)
    (hV6 : MemLp V 6 volume) (hV10 : MemLp V 10 volume)
    (hD6 : MemLp D 6 volume) (hD10 : MemLp D 10 volume) :
    SpatialBound (fun x => V x ^ (2+α) * D x) (reciprocalA α)
      ((spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (2-2*α/3)) *
        (spatialNorm 6 D ^ (α/3) * spatialNorm 10 D ^ (1-α/3))) := by
  have hv := split_power_bound hV hV6 hV10 (show 0 < 5*α/3 by positivity)
    (show 0 < 2-2*α/3 by linarith)
  have hd := split_power_bound hD hD6 hD10 (show 0 < α/3 by positivity)
    (show 0 < 1-α/3 by linarith)
  convert hv.mul hd using 1
  · ext x
    rw [show α/3+(1-α/3) = 1 by ring, Real.rpow_one]
    congr 2
    ring
  · dsimp [reciprocalA]
    ring

/-- Both literal forcing difference majorants have actual integral domains
and finite spatial L2 norms. Only ordinary strong HLS is assumed. -/
theorem pair_domain_bounds {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V D : Space → ℝ), (∀ x, 0 ≤ V x) → (∀ x, 0 ≤ D x) →
      MemLp V 6 volume → MemLp V 10 volume →
      MemLp D 6 volume → MemLp D 10 volume →
      RieszDomain α c (fun x => V x ^ (3+α)) ∧
      RieszDomain α c (fun x => V x ^ (2+α) * D x) ∧
      SpatialBound (majorant1 α c V D) (1/2)
        ((C : ℝ) * spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (4 : ℝ) *
          spatialNorm 10 D) ∧
      SpatialBound (majorant4 α c V D) (1/2)
        ((C : ℝ) * spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (4+α/3) *
          spatialNorm 6 D ^ (α/3) * spatialNorm 10 D ^ (1-α/3)) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  obtain ⟨ha,ha1,_,_⟩ := gradient_hls_ranges hα hα3
  obtain ⟨C,hC⟩ := convolution_bound hH ha ha1
  refine ⟨C, fun V D hV hD hV6 hV10 hD6 hD10 => ?_⟩
  obtain ⟨hi1,hp1⟩ := hC _ _ (first_density_bound hα hα3 hV hV6 hV10)
  obtain ⟨hi4,hp4⟩ := hC _ _ (difference_density_bound hα hα3 hV hD hV6 hV10 hD6 hD10)
  have ho1 := spacetime_power_bound hV hV10 (show 0 < 1+α by linarith)
  have ho4 := spacetime_power_bound hV hV10 (show 0 < 2+α by linarith)
  have hd := spatialBound_self (by norm_num : 0 < (10 : ℝ)) (by simpa using hD10)
  refine ⟨hi1,hi4,?_,?_⟩
  · convert (hp1.mul ho1).mul hd using 1
    · rfl
    · dsimp [reciprocalA]
      ring
    · symm
      calc
        _ = (C : ℝ) * spatialNorm 6 V ^ (2*α) *
            (spatialNorm 10 V ^ (3-α) * spatialNorm 10 V ^ (1+α)) * spatialNorm 10 D := by ring
        _ = _ := by
          rw [← Real.rpow_add' (spatialNorm_nonneg 10 V) (show 3-α+(1+α) ≠ 0 by ring_nf; norm_num)]
          congr 3
          ring
  · convert hp4.mul ho4 using 1
    · rfl
    · dsimp [reciprocalA]
      ring
    · symm
      calc
        _ = (C : ℝ) * spatialNorm 6 V ^ (5*α/3) *
            (spatialNorm 10 V ^ (2-2*α/3) * spatialNorm 10 V ^ (2+α)) *
            spatialNorm 6 D ^ (α/3) * spatialNorm 10 D ^ (1-α/3) := by ring
        _ = _ := by
          rw [← Real.rpow_add' (spatialNorm_nonneg 10 V) (show 2-2*α/3+(2+α) ≠ 0 by linarith)]
          congr 3
          ring

/-- Positive scalar multiplication preserves a finite real spatial bound. -/
theorem const_mul_bound {f : Space → ℝ} {s B a : ℝ}
    (hf : SpatialBound f s B) (ha : 0 ≤ a) :
    SpatialBound (fun x => a*f x) s (a*B) := by
  refine ⟨hf.reciprocal_pos, hf.memLp.const_mul a, ?_⟩
  have he : eLpNorm (fun x => a*f x) (ENNReal.ofReal (1/s)) volume =
      ENNReal.ofReal a * eLpNorm f (ENNReal.ofReal (1/s)) volume := by
    simpa only [Pi.smul_def, smul_eq_mul, Real.enorm_eq_ofReal ha] using
      (eLpNorm_const_smul (c := a) (f := f) (p := ENNReal.ofReal (1/s)) (μ := volume))
  unfold spatialNorm
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  exact mul_le_mul_of_nonneg_left hf.bound ha

/-- A literal nonnegative function that dominates the complex forcing difference. -/
def forcingMajorant (α c : ℝ) (V D : Space → ℝ) (x : Space) : ℝ :=
  (2+α)*majorant1 α c V D x+(3+α)*majorant4 α c V D x

/-- The sum of the two ordinary HLS/Holder estimates, without an abstract
Hartree estimate in its assumptions. -/
theorem majorant_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V D : Space → ℝ), (∀ x, 0 ≤ V x) → (∀ x, 0 ≤ D x) →
      MemLp V 6 volume → MemLp V 10 volume →
      MemLp D 6 volume → MemLp D 10 volume →
      RieszDomain α c (fun x => V x ^ (3+α)) ∧
      RieszDomain α c (fun x => V x ^ (2+α) * D x) ∧
      MemLp (forcingMajorant α c V D) 2 volume ∧
      spatialNorm 2 (forcingMajorant α c V D) ≤
        (C : ℝ) * (spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (4 : ℝ) * spatialNorm 10 D +
          spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (4+α/3) *
          spatialNorm 6 D ^ (α/3) * spatialNorm 10 D ^ (1-α/3)) := by
  obtain ⟨C,hC⟩ := pair_domain_bounds hH
  let K : ℝ≥0 := ⟨3+α, by linarith [hH.order_pos]⟩
  refine ⟨K*C, fun V D hV hD hV6 hV10 hD6 hD10 => ?_⟩
  obtain ⟨hi1,hi4,h1,h4⟩ := hC V D hV hD hV6 hV10 hD6 hD10
  have h1' := const_mul_bound h1 (by linarith [hH.order_pos] : 0 ≤ 2+α)
  have h4' := const_mul_bound h4 (by linarith [hH.order_pos] : 0 ≤ 3+α)
  have hb := h1'.add h4' (by norm_num)
  refine ⟨hi1,hi4,?_,?_⟩
  · change MemLp (fun x => (2+α)*majorant1 α c V D x+(3+α)*majorant4 α c V D x) 2 volume
    simpa only [show (1 : ℝ)/(1/2)=2 by norm_num, ENNReal.ofReal_ofNat] using hb.memLp
  · have hb' : spatialNorm 2 (forcingMajorant α c V D) ≤
        (2+α)*((C : ℝ)*spatialNorm 6 V^(2*α)*spatialNorm 10 V^(4 : ℝ)*spatialNorm 10 D) +
        (3+α)*((C : ℝ)*spatialNorm 6 V^(5*α/3)*spatialNorm 10 V^(4+α/3)*
          spatialNorm 6 D^(α/3)*spatialNorm 10 D^(1-α/3)) := by
      change spatialNorm 2 (fun x => (2+α)*majorant1 α c V D x+(3+α)*majorant4 α c V D x) ≤ _
      simpa only [show (1 : ℝ)/(1/2)=2 by norm_num] using hb.bound
    apply hb'.trans
    have hn : 0 ≤ (C : ℝ)*spatialNorm 6 V^(2*α)*spatialNorm 10 V^(4 : ℝ)*spatialNorm 10 D := by
      exact mul_nonneg (mul_nonneg (mul_nonneg C.coe_nonneg (Real.rpow_nonneg (spatialNorm_nonneg _ _) _))
        (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)) (spatialNorm_nonneg _ _)
    have he := add_le_add_right (mul_le_mul_of_nonneg_right (show 2+α ≤ 3+α by linarith) hn)
      ((3+α)*((C : ℝ)*spatialNorm 6 V^(5*α/3)*spatialNorm 10 V^(4+α/3)*
        spatialNorm 6 D^(α/3)*spatialNorm 10 D^(1-α/3)))
    rw [NNReal.coe_mul]
    change _ ≤ ((3+α)*(C : ℝ)) * _
    convert he using 1 <;> ring

/-- Actual complex forcing differences obey the literal majorant pointwise
where its two defining Riesz integrals are absolutely integrable. -/
theorem forcing_difference_pointwise {α c : ℝ} (ha : 0 < α) (hc : 0 ≤ c)
    {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (x : Space)
    (hbase : Integrable (fun y => rieszKernel α c (x-y)*sumAmplitude u v y^(3+α)) volume)
    (hdiff : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*differenceAmplitude u v y)) volume) :
    ‖forcing α c u x-forcing α c v x‖ ≤
      forcingMajorant α c (sumAmplitude u v) (differenceAmplitude u v) x := by
  obtain ⟨_,_,hA,hAB⟩ := potential_pair_envelopes ha hc hu hv x hbase hdiff
  have hloc : ‖localFactor α u x-localFactor α v x‖ ≤
      (2+α)*sumAmplitude u v x^(1+α)*differenceAmplitude u v x := by
    simpa only [localFactor, WeakHartreeChain.localFactor, sumAmplitude, differenceAmplitude,
      show 1+α+1=2+α by ring] using
      WeakHartreeChain.localFactor_difference_bound (by linarith : 1 < 1+α) (u x) (v x)
  have hvloc : ‖localFactor α v x‖ ≤ sumAmplitude u v x^(2+α) := by
    rw [norm_localFactor ha]
    exact Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) (by linarith)
  have ht := smul_difference_bound (potential α c u x) (potential α c v x)
    (localFactor α u x) (localFactor α v x)
  have he := ht.trans (add_le_add
    (mul_le_mul hA hloc (norm_nonneg _) ((norm_nonneg _).trans hA))
    (mul_le_mul hAB hvloc (norm_nonneg _) ((norm_nonneg _).trans hAB)))
  change ‖potential α c u x • localFactor α u x-potential α c v x • localFactor α v x‖ ≤ _
  apply he.trans_eq
  dsimp only [forcingMajorant,majorant1,majorant4]
  ring

/-- Full spatial L2 difference estimate for the actual complex forcing, retaining
membership. No L2 hypothesis is imposed on either input. -/
theorem actual_forcing_difference_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u v : Space → ℂ),
      MemLp u 6 volume → MemLp v 6 volume →
      MemLp u 10 volume → MemLp v 10 volume →
      MemLp (forcing α c u-forcing α c v) 2 volume ∧
      (eLpNorm (forcing α c u-forcing α c v) 2 volume).toReal ≤
        (C : ℝ) *
          (spatialNorm 6 (sumAmplitude u v) ^ (2*α) *
            spatialNorm 10 (sumAmplitude u v) ^ (4 : ℝ) * spatialNorm 10 (differenceAmplitude u v) +
          spatialNorm 6 (sumAmplitude u v) ^ (5*α/3) *
            spatialNorm 10 (sumAmplitude u v) ^ (4+α/3) *
            spatialNorm 6 (differenceAmplitude u v) ^ (α/3) *
            spatialNorm 10 (differenceAmplitude u v) ^ (1-α/3)) := by
  obtain ⟨C,hC⟩ := majorant_domain_bound hH
  obtain ⟨C0,h0⟩ := forcing_energy_domain_bound hH
  refine ⟨C, fun u v hu6 hv6 hu10 hv10 => ?_⟩
  have hV (x : Space) : 0 ≤ sumAmplitude u v x := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD (x : Space) : 0 ≤ differenceAmplitude u v x := norm_nonneg _
  have hV6 : MemLp (sumAmplitude u v) 6 volume := hu6.norm.add hv6.norm
  have hV10 : MemLp (sumAmplitude u v) 10 volume := hu10.norm.add hv10.norm
  have hD6 : MemLp (differenceAmplitude u v) 6 volume := (hu6.sub hv6).norm
  have hD10 : MemLp (differenceAmplitude u v) 10 volume := (hu10.sub hv10).norm
  obtain ⟨hi1,hi4,hm,hb⟩ := hC _ _ hV hD hV6 hV10 hD6 hD10
  have hfm := ((h0 u hu6).1.sub (h0 v hv6).1).aestronglyMeasurable
  have hae : ∀ᵐ x ∂volume, ‖(forcing α c u-forcing α c v) x‖ ≤
      forcingMajorant α c (sumAmplitude u v) (differenceAmplitude u v) x := by
    filter_upwards [hi1,hi4] with x hx hy
    exact forcing_difference_pointwise hH.order_pos hH.normalization_pos.le
      hu6.aestronglyMeasurable hv6.aestronglyMeasurable x hx hy
  refine ⟨hm.mono' hfm hae, ?_⟩
  have hen := eLpNorm_mono_ae (p := 2) (g := forcingMajorant α c (sumAmplitude u v) (differenceAmplitude u v))
    hfm (hae.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self _))
  have ht := ENNReal.toReal_mono hm.eLpNorm_ne_top hen
  exact ht.trans (by simpa only [spatialNorm, ENNReal.ofReal_ofNat] using hb)

#print axioms difference_density_bound
#print axioms pair_domain_bounds
#print axioms majorant_domain_bound
#print axioms forcing_difference_pointwise
#print axioms actual_forcing_difference_bound
end HartreeF.ForcingL2Difference
