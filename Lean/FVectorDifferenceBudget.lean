import FDirectionalDifferenceQuantitative
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The same three monomials as C29, on six explicit extended inputs. -/
def criticalBudget (alpha : ℝ) (M N D E Y Z : ℝ≥0∞) : ℝ≥0∞ :=
  M ^ (2 * alpha) * N ^ (4 : ℝ) * Z +
  M ^ (2 * alpha) * N ^ (3 : ℝ) * Y * E +
  M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y * D ^ (alpha / 3) * E ^ theta alpha

/-- A vector budget that retains the actual function and gradient differences. -/
def vectorDifferenceBudget {T : Type*} [MeasurableSpace T] (alpha : ℝ)
    (mu : Measure T) (u v : T → Space → ℂ) (U V P Q : T → Space → Space) : ℝ≥0∞ :=
  criticalBudget alpha
    (mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v)
    (mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v)
    (mixedNorm mu volume ∞ 6 (fun t => u t - v t))
    (mixedNorm mu volume 10 10 (fun t => u t - v t))
    (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q)
    (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => U t - P t) +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => V t - Q t))

theorem threeWeightBudget_le_criticalBudget {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (V W Y Z : T → Space → ℝ)
    (M N D E A B : ℝ≥0∞)
    (hM : eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ≤ M)
    (hN : eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ≤ N)
    (hD : eLpNorm (fun t => spatialNorm 6 (W t)) ∞ mu ≤ D)
    (hE : eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu ≤ E)
    (hY : eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu ≤ A)
    (hZ : eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 mu ≤ B) :
    threeWeightBudget alpha mu V W Y Z ≤ criticalBudget alpha M N D E A B := by
  have h2 := ENNReal.rpow_le_rpow hM (by positivity : 0 ≤ 2 * alpha)
  have h5 := ENNReal.rpow_le_rpow hM (by positivity : 0 ≤ 5 * alpha / 3)
  have h4 := ENNReal.rpow_le_rpow hN (by norm_num : (0 : ℝ) ≤ 4)
  have h3 := ENNReal.rpow_le_rpow hN (by norm_num : (0 : ℝ) ≤ 3)
  have h4t := ENNReal.rpow_le_rpow hN (by dsimp [theta]; linarith : 0 ≤ 4 - theta alpha)
  have ht := ENNReal.rpow_le_rpow hE (by dsimp [theta]; linarith : 0 ≤ theta alpha)
  have hd := ENNReal.rpow_le_rpow hD (by positivity : 0 ≤ alpha / 3)
  exact add_le_add
    (add_le_add (mul_le_mul' (mul_le_mul' h2 h4) hZ)
      (mul_le_mul' (mul_le_mul' (mul_le_mul' h2 h3) hY) hE))
    (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' h5 h4t) hY) hd) ht)

/-- Every unit-direction literal budget is bounded by one vector-difference budget. -/
theorem directional_budget_le_vector {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hSlices : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hP : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (mu.prod volume))
    (hQ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume))
    (e : Space) (he : ‖e‖ = 1) :
    threeWeightBudget alpha mu
      (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
      (fun t x => ‖directionalField (P t) (Q t) e x‖)
      (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) ≤
    vectorDifferenceBudget alpha mu u v U V P Q := by
  let A : T → Space → ℝ := fun t => sumAmplitude (u t) (v t)
  let B : T → Space → ℝ := fun t => differenceAmplitude (u t) (v t)
  let G : T → Space → ℂ := fun t => directionalField (U t) (V t) e
  let K : T → Space → ℂ := fun t => directionalField (P t) (Q t) e
  have jA : AEStronglyMeasurable (fun z : T × Space => A z.1 z.2) (mu.prod volume) := hu.norm.add hv.norm
  have jB : AEStronglyMeasurable (fun z : T × Space => B z.1 z.2) (mu.prod volume) := (hu.sub hv).norm
  have jG : AEStronglyMeasurable (fun z : T × Space => G z.1 z.2) (mu.prod volume) :=
    directional_field_joint_measurable mu U V e hU hV
  have jK : AEStronglyMeasurable (fun z : T × Space => K z.1 z.2) (mu.prod volume) :=
    directional_field_joint_measurable mu P Q e hP hQ
  have sA6 : ∀ᵐ t ∂mu, MemLp (A t) 6 volume :=
    hSlices.mono fun _ ht => ht.1.function_L6.norm.add ht.2.1.function_L6.norm
  have sA10 : ∀ᵐ t ∂mu, MemLp (A t) 10 volume :=
    hSlices.mono fun _ ht => ht.2.2.1.norm.add ht.2.2.2.1.norm
  have sB6 : ∀ᵐ t ∂mu, MemLp (B t) 6 volume :=
    hSlices.mono fun _ ht => (ht.1.function_L6.sub ht.2.1.function_L6).norm
  have sB10 : ∀ᵐ t ∂mu, MemLp (B t) 10 volume :=
    hSlices.mono fun _ ht => (ht.2.2.1.sub ht.2.2.2.1).norm
  have sY : ∀ᵐ t ∂mu, MemLp (fun x => ‖K t x‖) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [hSlices] with t ht
    exact (directionalField_memLp ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2 e).norm
  have sZ : ∀ᵐ t ∂mu, MemLp (fun x => ‖G t x - K t x‖) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [hSlices] with t ht
    exact ((directionalField_memLp ht.2.2.2.2.1 ht.2.2.2.2.2.1 e).sub
      (directionalField_memLp ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2 e)).norm
  have bM := (real_slice_mixed_eq mu ∞ 6 (by norm_num) (by norm_num) A jA sA6).le.trans
    (sum_amplitude_mixed_le mu ∞ 6 (by norm_num) (by norm_num) (by norm_num) u v hu hv)
  have bN := (real_slice_mixed_eq mu 10 10 (by norm_num) (by norm_num) A jA sA10).le.trans
    (sum_amplitude_mixed_le mu 10 10 (by norm_num) (by norm_num) (by norm_num) u v hu hv)
  have bD := (real_slice_mixed_eq mu ∞ 6 (by norm_num) (by norm_num) B jB sB6).trans
    (mixed_norm_norm_eq mu ∞ 6 (fun t => u t - v t) (hu.sub hv))
  have bE := (real_slice_mixed_eq mu 10 10 (by norm_num) (by norm_num) B jB sB10).trans
    (mixed_norm_norm_eq mu 10 10 (fun t => u t - v t) (hu.sub hv))
  have bY := (real_slice_mixed_eq mu 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num)
    ENNReal.ofReal_ne_top (fun t x => ‖K t x‖) jK.norm sY).le.trans
    ((mixed_norm_norm_eq mu 10 (ENNReal.ofReal (30/13 : ℝ)) K jK).le.trans
      (unit_directional_mixed_le mu 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num)
        (by norm_num) ENNReal.ofReal_ne_top P Q e he hP hQ))
  have bZ := (real_slice_mixed_eq mu 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num)
    ENNReal.ofReal_ne_top (fun t x => ‖G t x - K t x‖) (jG.sub jK).norm sZ).le.trans
    ((mixed_norm_norm_eq mu 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => G t - K t) (jG.sub jK)).le.trans
      (unit_directional_difference_mixed_le mu 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num)
        (by norm_num) ENNReal.ofReal_ne_top U V P Q e he hU hV hP hQ))
  unfold vectorDifferenceBudget
  apply threeWeightBudget_le_criticalBudget ha ha3
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat, A] using bM
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat, A] using bN
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat, B] using bD.le
  · simpa only [spatialNorm, ENNReal.ofReal_ofNat, B] using bE.le
  · exact bY
  · exact bZ

end HartreeF.TimeHolder
