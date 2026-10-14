import FHartreeMapOutputRestriction
import FPathGluingReconstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath gluePath

/-- Adjacent actual Hartree fixed points concatenate to an actual whole-interval
fixed point. The right datum is the left solution's actual terminal state.
The whole fixed-point equation is concluded solely from the two piece equations. -/
theorem gluePath_hartree_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a c b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hac : a ≤ c) (hcb : c ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hac u0 u = u)
    (hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
      (energyPath _ u ⟨c, hac, le_rfl⟩) v = v) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH (hac.trans hcb)
      u0 (gluePath hac hcb u v hm) = gluePath hac hcb u v hm := by
  let w := gluePath hac hcb u v hm
  let P := hartreeDuhamelMap hDensity hSob h0 hfree hret hH (hac.trans hcb) u0 w
  have hwl : restrictPath le_rfl hac hcb w = u := restrict_gluePath_left hac hcb u v hm
  have hwr : restrictPath hac hcb le_rfl w = v := restrict_gluePath_right hac hcb u v hm
  have hPa : energyPath _ P ⟨a, le_rfl, hac.trans hcb⟩ = u0 :=
    hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH (hac.trans hcb) u0 w
  have hPl : restrictPath le_rfl hac hcb P = u := by
    have he := restrictPath_hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      le_rfl hac hcb u0 w
    change hartreeDuhamelMap hDensity hSob h0 hfree hret hH hac
      (energyPath _ P ⟨a, le_rfl, hac.trans hcb⟩)
      (restrictPath le_rfl hac hcb w) = restrictPath le_rfl hac hcb P at he
    let D : EnergyState → CriticalPath (intervalMeasure a c) →
        CriticalPath (intervalMeasure a c) :=
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hac
    have hdata : D (energyPath _ P ⟨a, le_rfl, hac.trans hcb⟩)
        (restrictPath le_rfl hac hcb w) = D u0 u := congrArg₂ D hPa hwl
    exact he.symm.trans (hdata.trans hu)
  have hPc : energyPath _ P ⟨c, hac, hcb⟩ = energyPath _ u ⟨c, hac, le_rfl⟩ := by
    have he := congrArg (fun z : CriticalPath (intervalMeasure a c) =>
      energyPath _ z ⟨c, hac, le_rfl⟩) hPl
    exact (restrictPath_energy le_rfl hac hcb P ⟨c, hac, le_rfl⟩).symm.trans he
  have hPr : restrictPath hac hcb le_rfl P = v := by
    have he := restrictPath_hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      hac hcb le_rfl u0 w
    change hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
      (energyPath _ P ⟨c, hac, hcb⟩)
      (restrictPath hac hcb le_rfl w) = restrictPath hac hcb le_rfl P at he
    let D : EnergyState → CriticalPath (intervalMeasure c b) →
        CriticalPath (intervalMeasure c b) :=
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
    have hdata : D (energyPath _ P ⟨c, hac, hcb⟩)
        (restrictPath hac hcb le_rfl w) = D (energyPath _ u ⟨c, hac, le_rfl⟩) v :=
      congrArg₂ D hPc hwr
    exact he.symm.trans (hdata.trans hv)
  have hmP : energyPath _ (restrictPath le_rfl hac hcb P) ⟨c, hac, le_rfl⟩ =
      energyPath _ (restrictPath hac hcb le_rfl P) ⟨c, le_rfl, hcb⟩ :=
    (restrictPath_energy le_rfl hac hcb P ⟨c, hac, le_rfl⟩).trans
      (restrictPath_energy hac hcb le_rfl P ⟨c, le_rfl, hcb⟩).symm
  have hglue : gluePath hac hcb (restrictPath le_rfl hac hcb P)
      (restrictPath hac hcb le_rfl P) hmP = w := by
    dsimp only [w]
    congr 1
  exact (gluePath_restrictions hac hcb P).symm.trans hglue

end HartreeF.CriticalPathGluing
