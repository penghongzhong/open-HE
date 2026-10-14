import FCriticalPathBackwardSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
namespace HartreeF.CriticalPathRestriction
open CriticalPathSpace CriticalPathBall

/-- Two given actual critical paths share a positive backward subinterval with both W norms
arbitrarily small. The construction only uses their own finite critical coordinates. -/
theorem exists_backward_pair_restriction_W_small {a b t0 : ℝ}
    (hat : a < t0) (htb : t0 ≤ b)
    (u v : CriticalPath (intervalMeasure a b)) (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, ∃ had : a ≤ d, ∃ hdt : d < t0,
      ‖gradientCoordinates (intervalMeasure d t0) (restrictPath had hdt.le htb u)‖ ≤ eta ∧
      ‖gradientCoordinates (intervalMeasure d t0) (restrictPath had hdt.le htb v)‖ ≤ eta := by
  let locu := exists_backward_restriction_W_small hat htb u eta heta
  let locv := exists_backward_restriction_W_small hat htb v eta heta
  let du : ℝ := Classical.choose locu
  let dv : ℝ := Classical.choose locv
  have hau : a ≤ du := Classical.choose (Classical.choose_spec locu)
  have hav : a ≤ dv := Classical.choose (Classical.choose_spec locv)
  have hut : du < t0 := Classical.choose (Classical.choose_spec (Classical.choose_spec locu))
  have hvt : dv < t0 := Classical.choose (Classical.choose_spec (Classical.choose_spec locv))
  have hu : ‖gradientCoordinates (intervalMeasure du t0) (restrictPath hau hut.le htb u)‖ ≤ eta :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec locu))).1
  have hv : ‖gradientCoordinates (intervalMeasure dv t0) (restrictPath hav hvt.le htb v)‖ ≤ eta :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec locv))).1
  let d : ℝ := max du dv
  have had : a ≤ d := hau.trans (le_max_left du dv)
  have hdt : d < t0 := max_lt hut hvt
  have hud : du ≤ d := le_max_left du dv
  have hvd : dv ≤ d := le_max_right du dv
  refine ⟨d, had, hdt, ?_, ?_⟩
  · calc
      ‖gradientCoordinates (intervalMeasure d t0) (restrictPath had hdt.le htb u)‖ =
          ‖gradientCoordinates (intervalMeasure d t0)
            (restrictPath hud hdt.le le_rfl (restrictPath hau hut.le htb u))‖ :=
        congrArg (fun w : CriticalPath (intervalMeasure d t0) =>
          ‖gradientCoordinates (intervalMeasure d t0) w‖)
          (restrictPath_trans hau hut.le htb hud hdt.le le_rfl u).symm
      _ ≤ ‖gradientCoordinates (intervalMeasure du t0) (restrictPath hau hut.le htb u)‖ :=
        restrictPath_W_norm_le hud hdt.le le_rfl (restrictPath hau hut.le htb u)
      _ ≤ eta := hu
  · calc
      ‖gradientCoordinates (intervalMeasure d t0) (restrictPath had hdt.le htb v)‖ =
          ‖gradientCoordinates (intervalMeasure d t0)
            (restrictPath hvd hdt.le le_rfl (restrictPath hav hvt.le htb v))‖ :=
        congrArg (fun w : CriticalPath (intervalMeasure d t0) =>
          ‖gradientCoordinates (intervalMeasure d t0) w‖)
          (restrictPath_trans hav hvt.le htb hvd hdt.le le_rfl v).symm
      _ ≤ ‖gradientCoordinates (intervalMeasure dv t0) (restrictPath hav hvt.le htb v)‖ :=
        restrictPath_W_norm_le hvd hdt.le le_rfl (restrictPath hav hvt.le htb v)
      _ ≤ eta := hv

end HartreeF.CriticalPathRestriction
