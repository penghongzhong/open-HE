import FActualResidualDomains
import FCriticalPathQuantitativeNorms

/-! Uniform full-X continuity for one genuine first spatial derivative.
The constant precedes the small block and its cap. Zero caps and zero Sobolev
normalization are multiplication-only cases. Author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FullResidual
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ForcingDomain
  GradientMajorants WeakHartreeProduct CriticalTimeSobolev ProfileApproximation
  GeneralProfileCross FiniteProfileWeakGradient FreeValueGradient R2Global R2TailForcing

private theorem projected_sub_ae (L : ℂ →L[ℝ] ℝ) (u v : EnergyState) :
    energyProjectedGradient L (u-v) =ᵐ[volume]
      fun x => energyProjectedGradient L u x-energyProjectedGradient L v x :=
  CriticalSourceBounds.projectedGradient_sub_ae L u v

/-- Literal differences are chosen joint fields for the actual difference
EnergyState curve; quotient-selected representatives are only identified AE. -/
def differenceJointFields {q v : ℝ → EnergyState}
    (rq : EnergyJointFields volume q) (rv : EnergyJointFields volume v) :
    EnergyJointFields volume (q-v) where
  u := rq.u-rv.u
  U := rq.U-rv.U
  V := rq.V-rv.V
  joint_u := rq.joint_u.sub rv.joint_u
  joint_U := rq.joint_U.sub rv.joint_U
  joint_V := rq.joint_V.sub rv.joint_V
  slice_eq := by
    filter_upwards [rq.slice_eq, rv.slice_eq] with t hq hv
    refine ⟨?_, ?_, ?_⟩
    · exact (hq.1.sub hv.1).trans (CriticalSourceBounds.energyValue_sub_ae (q t) (v t)).symm
    · exact (hq.2.1.sub hv.2.1).trans (projected_sub_ae Complex.reCLM (q t) (v t)).symm
    · exact (hq.2.2.sub hv.2.2).trans (projected_sub_ae Complex.imCLM (q t) (v t)).symm

private theorem projected_norm_le_packed (U V : Space → Space) (x : Space) :
    ‖U x‖ ≤ ‖complexGradient U V x‖ ∧ ‖V x‖ ≤ ‖complexGradient U V x‖ := by
  have h := complexGradient_norm_sq U V x
  constructor <;> nlinarith [norm_nonneg (U x), norm_nonneg (V x),
    norm_nonneg (complexGradient U V x), sq_nonneg ‖U x‖, sq_nonneg ‖V x‖]

/-- Projection bounds use the actual Euclidean packed gradient. -/
theorem joint_projected_W_le_curveW {q : ℝ → EnergyState}
    (r : EnergyJointFields volume q) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U ≤ curveW q ∧
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V ≤ curveW q := by
  have he := R2Global.joint_gradient_norm q r 10 (ENNReal.ofReal (30/13 : ℝ))
  constructor
  · exact (ProfileApproximation.mixed_mono (by norm_num) ENNReal.ofReal_ne_top
      r.joint_U.aestronglyMeasurable
      (fun t x => (projected_norm_le_packed (r.U t) (r.V t) x).1)).trans_eq he
  · exact (ProfileApproximation.mixed_mono (by norm_num) ENNReal.ofReal_ne_top
      r.joint_V.aestronglyMeasurable
      (fun t x => (projected_norm_le_packed (r.U t) (r.V t) x).2)).trans_eq he

private theorem joint_caps {K : ℝ} (hSob : OrdinarySobolev K)
    {q : ℝ → EnergyState} (hq : CurveFinite q) (r : EnergyJointFields volume q)
    {D : ℝ} (_hD : 0 ≤ D) (hx : xNorm q ≤ D) :
    mixedNorm volume volume ∞ 6 r.u ≤ ENNReal.ofReal (K^((6:ℝ)⁻¹)*D) ∧
    mixedNorm volume volume 10 10 r.u ≤ ENNReal.ofReal D ∧
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U ≤ ENNReal.ofReal D ∧
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V ≤ ENNReal.ofReal D := by
  have hX : curveX q ≤ ENNReal.ofReal D := by
    rw [← ofReal_xNorm hq]
    exact ENNReal.ofReal_le_ofReal hx
  have hE := (curveEnergy_le_curveX q).trans hX
  have hW := (curveW_le_curveX q).trans hX
  refine ⟨?_, ?_, (joint_projected_W_le_curveW r).1.trans hW,
    (joint_projected_W_le_curveW r).2.trans hW⟩
  · exact (jointFields_value_sobolev_bound hSob q r).trans
      ((mul_le_mul' le_rfl hE).trans_eq
        (ENNReal.ofReal_mul (Real.rpow_nonneg hSob.nonneg _)).symm)
  · rw [R2Global.joint_value_norm]
    exact (curveS_le_curveX q).trans hX

private theorem criticalBudget_mono {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {A N D E Y Z A' N' D' E' Y' Z' : ℝ≥0∞}
    (hA : A ≤ A') (hN : N ≤ N') (hD : D ≤ D') (hE : E ≤ E')
    (hY : Y ≤ Y') (hZ : Z ≤ Z') :
    criticalBudget α A N D E Y Z ≤ criticalBudget α A' N' D' E' Y' Z' := by
  have h2 := ENNReal.rpow_le_rpow hA (by positivity : 0 ≤ 2*α)
  have h5 := ENNReal.rpow_le_rpow hA (by positivity : 0 ≤ 5*α/3)
  have h4 := ENNReal.rpow_le_rpow hN (by norm_num : (0:ℝ) ≤ 4)
  have h3 := ENNReal.rpow_le_rpow hN (by norm_num : (0:ℝ) ≤ 3)
  have h4t := ENNReal.rpow_le_rpow hN (by dsimp [theta]; linarith : 0 ≤ 4-theta α)
  have ht := ENNReal.rpow_le_rpow hE (by dsimp [theta]; linarith : 0 ≤ theta α)
  have hd := ENNReal.rpow_le_rpow hD (by positivity : 0 ≤ α/3)
  exact add_le_add
    (add_le_add (mul_le_mul' (mul_le_mul' h2 h4) hZ)
      (mul_le_mul' (mul_le_mul' (mul_le_mul' h2 h3) hY) hE))
    (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' h5 h4t) hY) hd) ht)

private theorem criticalBudget_ofReal {α A N D E Y Z : ℝ}
    (hα : 0 < α) (hα3 : α < 3) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    criticalBudget α (ENNReal.ofReal A) (ENNReal.ofReal N)
      (ENNReal.ofReal D) (ENNReal.ofReal E) (ENNReal.ofReal Y) (ENNReal.ofReal Z) =
    ENNReal.ofReal (A^(2*α)*N^(4:ℝ)*Z + A^(2*α)*N^(3:ℝ)*Y*E +
      A^(5*α/3)*N^(4-theta α)*Y*D^(α/3)*E^(theta α)) := by
  have ht : 0 ≤ theta α := by dsimp [theta]; linarith
  have h4t : 0 ≤ 4-theta α := by dsimp [theta]; linarith
  have h1 : ENNReal.ofReal A^(2*α)*ENNReal.ofReal N^(4:ℝ)*ENNReal.ofReal Z =
      ENNReal.ofReal (A^(2*α)*N^(4:ℝ)*Z) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hN (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hN _))]
  have h2 : ENNReal.ofReal A^(2*α)*ENNReal.ofReal N^(3:ℝ)*ENNReal.ofReal Y*ENNReal.ofReal E =
      ENNReal.ofReal (A^(2*α)*N^(3:ℝ)*Y*E) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hN (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hN _)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hN _)) hY)]
  have h3 : ENNReal.ofReal A^(5*α/3)*ENNReal.ofReal N^(4-theta α)*ENNReal.ofReal Y*
      ENNReal.ofReal D^(α/3)*ENNReal.ofReal E^(theta α) =
      ENNReal.ofReal (A^(5*α/3)*N^(4-theta α)*Y*D^(α/3)*E^(theta α)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hN h4t, ENNReal.ofReal_rpow_of_nonneg hD (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hE ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hN _)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hN _)) hY),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hN _)) hY) (Real.rpow_nonneg hD _))]
  rw [criticalBudget, h1, h2, h3, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The exact three-monomial coefficient from the accepted full-X estimate. -/
def tailCoefficient (α K M : ℝ) : ℝ :=
  let K6 := K^((6:ℝ)⁻¹)
  let A := K6*(2*M+1)
  let N := 2*M+1
  let Y := 2*(M+1)
  2*A^(2*α)*N^(4:ℝ) + A^(2*α)*N^(3:ℝ)*Y +
    A^(5*α/3)*N^(4-theta α)*Y*K6^(α/3)

theorem tailCoefficient_nonneg {K M : ℝ} (hK : 0 ≤ K) (hM : 1 ≤ M) (α : ℝ) :
    0 ≤ tailCoefficient α K M := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  dsimp [tailCoefficient]
  positivity

private theorem tail_budget_eq {α K M d : ℝ}
    (hα : 0 < α) (hα3 : α < 3) (hK : 0 ≤ K) (hM : 1 ≤ M) (hd : 0 ≤ d) :
    criticalBudget α (ENNReal.ofReal (K^((6:ℝ)⁻¹)*(2*M+1)))
      (ENNReal.ofReal (2*M+1)) (ENNReal.ofReal (K^((6:ℝ)⁻¹)*d))
      (ENNReal.ofReal d) (ENNReal.ofReal (2*(M+1))) (ENNReal.ofReal (2*d)) =
        ENNReal.ofReal (tailCoefficient α K M*d) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hK6 : 0 ≤ K^((6:ℝ)⁻¹) := Real.rpow_nonneg hK _
  rw [criticalBudget_ofReal hα hα3 (by positivity) (by positivity)
    (mul_nonneg hK6 hd) hd (by positivity) (by positivity)]
  congr 1
  rw [Real.mul_rpow hK6 hd]
  have hp : d^(α/3)*d^(theta α) = d := by
    rw [← Real.rpow_add_of_nonneg hd (by positivity) (by dsimp [theta]; linarith)]
    have he : α/3+theta α=1 := by dsimp [theta]; ring
    rw [he, Real.rpow_one]
  dsimp [tailCoefficient]
  calc
    _ = (2*(K^((6:ℝ)⁻¹)*(2*M+1))^(2*α)*(2*M+1)^(4:ℝ) +
        (K^((6:ℝ)⁻¹)*(2*M+1))^(2*α)*(2*M+1)^(3:ℝ)*(2*(M+1)))*d +
      ((K^((6:ℝ)⁻¹)*(2*M+1))^(5*α/3)*(2*M+1)^(4-theta α)*(2*(M+1))*
        (K^((6:ℝ)⁻¹))^(α/3))*(d^(α/3)*d^(theta α)) := by ring
    _ = _ := by rw [hp]; ring

/-- Both source packets are produced before raw-to-candidate transport.
The two raw zero-state terms cancel algebraically; neither is erased. -/
theorem sourceCandidate_difference_norm_eq_actual (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    {q v : ℝ → EnergyState} (hq : CurveFinite q) (hv : CurveFinite v)
    (rq : EnergyJointFields volume q) (rv : EnergyJointFields volume v) :
    vectorForcingNorm (fun t x => sourceCandidate α c rq t x-sourceCandidate α c rv t x) =
      vectorForcingNorm (fun t x => actualFullGradient α c (rq.u t) (rq.U t) (rq.V t) x-
        actualFullGradient α c (rv.u t) (rv.U t) (rv.V t) x) := by
  have hqD := source_domains hDensity hSob hH hq rq
  have hvD := source_domains hDensity hSob hH hv rv
  apply mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5:ℝ))
  filter_upwards [hqD.actual_ae_candidate, hvD.actual_ae_candidate] with t hqA hvA
  filter_upwards [hqA, hvA] with x hqx hvx
  change sourceGradient α c rq t x = sourceCandidate α c rq t x at hqx
  change sourceGradient α c rv t x = sourceCandidate α c rv t x at hvx
  rw [← hqx, ← hvx]
  simp only [sourceGradient, actualGradient, zero_add, Pi.zero_apply]
  abel

/-- The full-X constant is fixed before d, q, the tail block, and every choice
of compatible representatives. This is not a value-only S continuity claim. -/
theorem exists_full_x_gradient_difference_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ Ktail : ℝ, 0 ≤ Ktail ∧
      ∀ (q T : ℝ → EnergyState) (_hq : CurveFinite q) (_hT : CurveFinite T)
        (rq : EnergyJointFields volume q) (rminus : EnergyJointFields volume (q-T))
        (d : ℝ), 0 ≤ d → d ≤ 1 → xNorm q ≤ M → xNorm T ≤ d →
      vectorForcingNorm (fun t x => sourceCandidate α c rq t x-
        sourceCandidate α c rminus t x) ≤ ENNReal.ofReal (Ktail*d) := by
  obtain ⟨C, hC⟩ := actual_full_gradient_vector_difference_bound hH
  let Ktail : ℝ := (C:ℝ)*tailCoefficient α K M
  have hKtail : 0 ≤ Ktail := mul_nonneg C.coe_nonneg (tailCoefficient_nonneg hSob.nonneg hM α)
  refine ⟨Ktail, hKtail, ?_⟩
  intro q T hq hT rq rminus d hd hd1 hqM hTd
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hK6 : 0 ≤ K^((6:ℝ)⁻¹) := Real.rpow_nonneg hSob.nonneg _
  have hminus : CurveFinite (q-T) := hq.sub hT
  have hminusM : xNorm (q-T) ≤ M+1 :=
    (xNorm_sub_le hq hT).trans (add_le_add hqM (hTd.trans hd1))
  have hdiff : CurveFinite (q-(q-T)) := by simpa only [sub_sub_cancel] using hT
  have hdiffD : xNorm (q-(q-T)) ≤ d := by simpa only [sub_sub_cancel] using hTd
  let rd := differenceJointFields rq rminus
  have hqc := joint_caps hSob hq rq hM0 hqM
  have hmc := joint_caps hSob hminus rminus (by linarith : 0 ≤ M+1) hminusM
  have hdc := joint_caps hSob hdiff rd hd hdiffD
  -- Domain production occurs before the actual analytic vector estimate.
  have hqD := source_domains hDensity hSob hH hq rq
  have hmD := source_domains hDensity hSob hH hminus rminus
  have hs : ∀ᵐ t ∂volume,
      InDotH1 (rq.u t) (rq.U t) (rq.V t) ∧
      InDotH1 (rminus.u t) (rminus.U t) (rminus.V t) ∧
      MemLp (rq.u t) 10 volume ∧ MemLp (rminus.u t) 10 volume ∧
      MemLp (rq.U t) (ENNReal.ofReal (30/13:ℝ)) volume ∧
      MemLp (rq.V t) (ENNReal.ofReal (30/13:ℝ)) volume ∧
      MemLp (rminus.U t) (ENNReal.ofReal (30/13:ℝ)) volume ∧
      MemLp (rminus.V t) (ENNReal.ofReal (30/13:ℝ)) volume := by
    filter_upwards [hqD.source_slices, hmD.source_slices] with t hqt hmt
    simp only [Pi.zero_apply, zero_add] at hqt hmt
    exact ⟨hqt.1, hmt.1, hqt.2.2.1, hmt.2.2.1,
      hqt.2.2.2.2.1, hqt.2.2.2.2.2.1, hmt.2.2.2.2.1, hmt.2.2.2.2.2.1⟩
  have hraw := hC volume rq.u rminus.u rq.U rq.V rminus.U rminus.V hs
    rq.joint_u.aestronglyMeasurable rminus.joint_u.aestronglyMeasurable
    rq.joint_U.aestronglyMeasurable rq.joint_V.aestronglyMeasurable
    rminus.joint_U.aestronglyMeasurable rminus.joint_V.aestronglyMeasurable
  have hA : mixedNorm volume volume ∞ 6 rq.u + mixedNorm volume volume ∞ 6 rminus.u ≤
      ENNReal.ofReal (K^((6:ℝ)⁻¹)*(2*M+1)) := by
    apply (add_le_add hqc.1 hmc.1).trans_eq
    rw [← ENNReal.ofReal_add (mul_nonneg hK6 hM0) (mul_nonneg hK6 (by linarith))]
    congr 1
    ring
  have hN : mixedNorm volume volume 10 10 rq.u + mixedNorm volume volume 10 10 rminus.u ≤
      ENNReal.ofReal (2*M+1) := by
    apply (add_le_add hqc.2.1 hmc.2.1).trans_eq
    rw [← ENNReal.ofReal_add hM0 (by linarith)]
    congr 1
    ring
  have hY : mixedNorm volume volume 10 (ENNReal.ofReal (30/13:ℝ)) rminus.U +
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13:ℝ)) rminus.V ≤
      ENNReal.ofReal (2*(M+1)) := by
    apply (add_le_add hmc.2.2.1 hmc.2.2.2).trans_eq
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ M+1) (by linarith : 0 ≤ M+1)]
    congr 1
    ring
  have hZ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13:ℝ)) (fun t => rq.U t-rminus.U t) +
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13:ℝ)) (fun t => rq.V t-rminus.V t) ≤
      ENNReal.ofReal (2*d) := by
    apply (add_le_add hdc.2.2.1 hdc.2.2.2).trans_eq
    rw [← ENNReal.ofReal_add hd hd]
    congr 1
    ring
  have hb : vectorDifferenceBudget α volume rq.u rminus.u rq.U rq.V rminus.U rminus.V ≤
      ENNReal.ofReal (tailCoefficient α K M*d) := by
    unfold vectorDifferenceBudget
    exact (criticalBudget_mono hH.order_pos hH.order_lt_three hA hN hdc.1 hdc.2.1 hY hZ).trans_eq
      (tail_budget_eq hH.order_pos hH.order_lt_three hSob.nonneg hM hd)
  have hnum : (C:ℝ≥0∞)*ENNReal.ofReal (tailCoefficient α K M*d) = ENNReal.ofReal (Ktail*d) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    congr 1
    dsimp [Ktail]
    ring
  rw [sourceCandidate_difference_norm_eq_actual hDensity hSob hH hq hminus rq rminus]
  exact hraw.trans ((mul_le_mul' le_rfl hb).trans_eq hnum)

end HartreeF.FullResidual
