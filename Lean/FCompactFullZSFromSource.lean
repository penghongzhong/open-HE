import FActualFullZForcingPerturbation
import FBackwardForcedEndpointDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HartreeF.CompactFullZS
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder CriticalSourceBounds
open ActualBackwardLocalFixedPoint BackwardPerturbation ActualPerturbation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient freeCriticalPath freeEnergyState
  hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource intervalRetardedCriticalPath intervalAdvancedCriticalPath
  intervalRetardedCriticalPath_endpointWitness intervalAdvancedCriticalPath_endpointWitness

section Abstract
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
theorem correction_add_sub (q p : X) : q+Complex.I • p-q=Complex.I • p := by abel
theorem correction_sub_sub (q p : X) : q-Complex.I • p-q=(-Complex.I) • p := by
  rw [neg_smul]
  abel
theorem unit_smul_enorm (z : ℂ) (hz : ‖z‖ₑ=1) (p : X) : ‖z • p‖ₑ=‖p‖ₑ := by
  rw [enorm_smul,hz,one_mul]
end Abstract

def scalarSConstant (K : ℝ) : ℝ := (5/3 : ℝ)*K^(1/6 : ℝ)*6

theorem scalarSConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K) :
    0 ≤ scalarSConstant K := by
  have hK := hSob.nonneg
  unfold scalarSConstant
  positivity

/-- Arithmetic assembly for the same literal path difference. The endpoint
estimate is supplied below by the actual linear Duhamel operator. -/
theorem fullZS_le_of_graph_endpoint (hDensity : OrdinaryH1Density)
    {K a b R Z : ℝ} (hSob : OrdinarySobolev K)
    (u q : CriticalPath (intervalMeasure a b)) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hgraph : ‖u-q‖ ≤ R)
    (hz : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤ ENNReal.ofReal Z) :
    fullZSDifferenceSize u q ≤ ENNReal.ofReal ((1+scalarSConstant K)*R+Z) := by
  have hS := scalarSConstant_nonneg hSob
  have hs := (actual_scalar_difference_S_bound hDensity hSob u q).trans
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hgraph))
  have hs' : mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) ≤
      ENNReal.ofReal (scalarSConstant K*R) :=
    hs.trans_eq (ENNReal.ofReal_mul hS).symm
  unfold fullZSDifferenceSize
  apply (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hgraph) hz) hs').trans
    ((ofReal_sum_three hR hZ (mul_nonneg hS hR)).le.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_rfl

theorem complex_endpoint_le_three_of_coordinate {a b D : ℝ}
    (u : CriticalPath (intervalMeasure a b)) (_hD : 0 ≤ D)
    (hcoord : ∀ j : Fin 3, mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ u t)) ≤ ENNReal.ofReal D) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal (3*D) := by
  apply (criticalPath_complex_endpoint_le_sum u).trans
  calc
    _ ≤ ∑ _j : Fin 3, ENNReal.ofReal D := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = 3*ENNReal.ofReal D := by simp
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha c)

include hefree heret in
/-- Uniform graph and internally produced source bounds give all four compact
norms for the very same forward mild path. -/
theorem forward_fullZS_of_graph_source (hab : a ≤ b)
    (f : EnergyState) (u : CriticalPath (intervalMeasure a b))
    {A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u)
    (hu : ‖u‖ ≤ A)
    (hsource : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ F) :
    fullZSDifferenceSize u 0 ≤ ENNReal.ofReal
      ((1+scalarSConstant K+3*Che)*A+3*Cre*F) := by
  have hinit := hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hab f u
  rw [hfix] at hinit
  have hf : ‖f‖ ≤ A := by
    rw [← hinit]
    exact ((energyPath _ u).norm_coe_le_norm ⟨a,le_rfl,hab⟩).trans
      ((energyPath_norm_le _ u).trans hu)
  have hc (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ u t)) ≤ ENNReal.ofReal (Che*A+Cre*F) := by
    have hj := hartreeDuhamelMap_endpoint_bound
      hDensity hSob h0 hfree hret hefree heret hH hab f u j
    rw [hfix] at hj
    apply hj.trans ((add_le_add
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        ((energyState_gradient_norm_le f j).trans hf) hefree.1))
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm _ j).trans hsource) heret.1))).trans_eq ?_)
    exact (ENNReal.ofReal_add (mul_nonneg hefree.1 hA) (mul_nonneg heret.1 hF)).symm
  have hzero : u-(0 : CriticalPath (intervalMeasure a b))=u := sub_zero u
  have hD : 0 ≤ Che*A+Cre*F := add_nonneg (mul_nonneg hefree.1 hA) (mul_nonneg heret.1 hF)
  have hz : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ (0 : CriticalPath (intervalMeasure a b)) t) x)
      ≤ ENNReal.ofReal (3*(Che*A+Cre*F)) := by
    rw [actual_complex_difference_mixedNorm_eq]
    rw [hzero]
    exact complex_endpoint_le_three_of_coordinate u hD hc
  have hh := fullZS_le_of_graph_endpoint hDensity hSob u 0 hA
    (mul_nonneg (by norm_num) hD) ((congrArg norm hzero).le.trans hu) hz
  exact hh.trans_eq (congrArg ENNReal.ofReal (by ring))

include heret in
/-- The forward correction is the actual retarded source, so its endpoint norm
has no spurious linear free-wave term. -/
theorem forward_correction_fullZS_of_source (hab : a ≤ b)
    (f : EnergyState) (u : CriticalPath (intervalMeasure a b))
    {R F : ℝ} (hR : 0 ≤ R) (hF : 0 ≤ F)
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u)
    (hgraph : ‖u-freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-a) f)‖ ≤ R)
    (hsource : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ F) :
    fullZSDifferenceSize u
      (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f)) ≤
      ENNReal.ofReal ((1+scalarSConstant K)*R+3*Cre*F) := by
  let q := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f)
  let G := criticalPathIntervalSource hDensity hSob hH hab u 0
  let P := intervalRetardedCriticalPath hDensity hSob h0 hret G
  let W := intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret G
  have hmap : q + Complex.I • P = u := by
    unfold hartreeDuhamelMap at hfix
    exact hfix
  have hcor : u-q = Complex.I • P :=
    (congrArg (fun w : CriticalPath (intervalMeasure a b) => w-q) hmap.symm).trans (correction_add_sub q P)
  have hcoord (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (u-q) t)) ≤ ENNReal.ofReal (Cre*F) := by
    have he : mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (energyPath _ (u-q) t)) =
        mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (Complex.I • energyPath _ P t)) := by
      apply congrArg (mixedNorm (intervalMeasure a b) volume 2 6)
      funext t
      exact congrArg (fun v : EnergyState => (energyGradient j v : Space → ℂ))
        ((congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath _ p t) hcor).trans
          (criticalPath_energy_smul_apply Complex.I P t))
    have hi : ‖Complex.I‖ₑ = 1 := by simp [← ofReal_norm]
    apply le_trans (le_of_eq (he.trans ((W.smul Complex.I).mixedNorm_eq j)))
    change ‖Complex.I • W.field j‖ₑ ≤ _
    rw [unit_smul_enorm Complex.I hi]
    exact (intervalRetardedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hret heret G j).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm G.gradient j).trans hsource) heret.1))
  have hz : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x-energyComplexGradient (energyPath _ q t) x)
      ≤ ENNReal.ofReal (3*(Cre*F)) := by
    rw [actual_complex_difference_mixedNorm_eq]
    exact complex_endpoint_le_three_of_coordinate (u-q) (mul_nonneg heret.1 hF) hcoord
  have hh := fullZS_le_of_graph_endpoint hDensity hSob u q hR
    (mul_nonneg (by norm_num) (mul_nonneg heret.1 hF)) hgraph hz
  exact hh.trans_eq (congrArg ENNReal.ofReal (by ring))

include hefree heret in
/-- The backward correction is the actual negative-i advanced source. -/
theorem backward_correction_fullZS_of_source (hab : a ≤ b)
    (f : EnergyState) (u : CriticalPath (intervalMeasure a b))
    {R F : ℝ} (hR : 0 ≤ R) (hF : 0 ≤ F)
    (hfix : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u)
    (hgraph : ‖u-freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-b) f)‖ ≤ R)
    (hsource : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ F) :
    fullZSDifferenceSize u
      (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) f)) ≤
      ENNReal.ofReal ((1+scalarSConstant K)*R+3*(Che*C0+Cre)*F) := by
  let q := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) f)
  let G := criticalPathIntervalSource hDensity hSob hH hab u 0
  let P := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret G
  let W := intervalAdvancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret G
  have hmap : q - Complex.I • P = u := by
    unfold backwardHartreeDuhamelMap at hfix
    exact hfix
  have hcor : u-q = (-Complex.I) • P :=
    (congrArg (fun w : CriticalPath (intervalMeasure a b) => w-q) hmap.symm).trans
      (correction_sub_sub q P)
  have hCe : 0 ≤ Che*C0+Cre := add_nonneg (mul_nonneg hefree.1 h0.1) heret.1
  have hcoord (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (u-q) t)) ≤ ENNReal.ofReal ((Che*C0+Cre)*F) := by
    have he : mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j (energyPath _ (u-q) t)) =
        mixedNorm (intervalMeasure a b) volume 2 6
        (fun t => energyGradient j ((-Complex.I) • energyPath _ P t)) := by
      apply congrArg (mixedNorm (intervalMeasure a b) volume 2 6)
      funext t
      exact congrArg (fun v : EnergyState => (energyGradient j v : Space → ℂ))
        ((congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath _ p t) hcor).trans
          (criticalPath_energy_smul_apply (-Complex.I) P t))
    have hi : ‖-Complex.I‖ₑ = 1 := by simp [← ofReal_norm]
    apply le_trans (le_of_eq (he.trans ((W.smul (-Complex.I)).mixedNorm_eq j)))
    change ‖(-Complex.I) • W.field j‖ₑ ≤ _
    rw [unit_smul_enorm (-Complex.I) hi]
    exact (intervalAdvanced_endpoint_enorm_bound hDensity hSob h0 hfree hret hefree heret G j).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm G.gradient j).trans hsource) hCe))
  have hz : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x-energyComplexGradient (energyPath _ q t) x)
      ≤ ENNReal.ofReal (3*((Che*C0+Cre)*F)) := by
    rw [actual_complex_difference_mixedNorm_eq]
    exact complex_endpoint_le_three_of_coordinate (u-q) (mul_nonneg hCe hF) hcoord
  have hh := fullZS_le_of_graph_endpoint hDensity hSob u q hR
    (mul_nonneg (by norm_num) (mul_nonneg hCe hF)) hgraph hz
  exact hh.trans_eq (congrArg ENNReal.ofReal (by ring))

end HartreeF.CompactFullZS
