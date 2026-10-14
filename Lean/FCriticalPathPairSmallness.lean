import FCriticalPathLocalSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.CriticalPathRestriction
open CriticalPathSpace CriticalPathBall

/-- Two given actual critical paths share a positive forward subinterval with both W norms
arbitrarily small. The construction only uses their own finite critical coordinates. -/
theorem exists_forward_pair_restriction_W_small {a b t0 : ℝ}
    (hat : a ≤ t0) (htb : t0 < b)
    (u v : CriticalPath (intervalMeasure a b)) (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, ∃ htd : t0 < d, ∃ hdb : d ≤ b,
      ‖gradientCoordinates (intervalMeasure t0 d) (restrictPath hat htd.le hdb u)‖ ≤ eta ∧
      ‖gradientCoordinates (intervalMeasure t0 d) (restrictPath hat htd.le hdb v)‖ ≤ eta := by
  let locu := exists_forward_restriction_W_small hat htb u eta heta
  let locv := exists_forward_restriction_W_small hat htb v eta heta
  let du : ℝ := Classical.choose locu
  let dv : ℝ := Classical.choose locv
  have htu : t0 < du := Classical.choose (Classical.choose_spec locu)
  have htv : t0 < dv := Classical.choose (Classical.choose_spec locv)
  have hub : du ≤ b := Classical.choose (Classical.choose_spec (Classical.choose_spec locu))
  have hvb : dv ≤ b := Classical.choose (Classical.choose_spec (Classical.choose_spec locv))
  have hu : ‖gradientCoordinates (intervalMeasure t0 du) (restrictPath hat htu.le hub u)‖ ≤ eta :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec locu))).1
  have hv : ‖gradientCoordinates (intervalMeasure t0 dv) (restrictPath hat htv.le hvb v)‖ ≤ eta :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec locv))).1
  let d : ℝ := min du dv
  have htd : t0 < d := lt_min htu htv
  have hdu : d ≤ du := min_le_left du dv
  have hdv : d ≤ dv := min_le_right du dv
  have hdb : d ≤ b := hdu.trans hub
  refine ⟨d, htd, hdb, ?_, ?_⟩
  · calc
      ‖gradientCoordinates (intervalMeasure t0 d) (restrictPath hat htd.le hdb u)‖ =
          ‖gradientCoordinates (intervalMeasure t0 d)
            (restrictPath le_rfl htd.le hdu (restrictPath hat htu.le hub u))‖ :=
        congrArg (fun w : CriticalPath (intervalMeasure t0 d) =>
          ‖gradientCoordinates (intervalMeasure t0 d) w‖)
          (restrictPath_trans hat htu.le hub le_rfl htd.le hdu u).symm
      _ ≤ ‖gradientCoordinates (intervalMeasure t0 du) (restrictPath hat htu.le hub u)‖ :=
        restrictPath_W_norm_le le_rfl htd.le hdu (restrictPath hat htu.le hub u)
      _ ≤ eta := hu
  · calc
      ‖gradientCoordinates (intervalMeasure t0 d) (restrictPath hat htd.le hdb v)‖ =
          ‖gradientCoordinates (intervalMeasure t0 d)
            (restrictPath le_rfl htd.le hdv (restrictPath hat htv.le hvb v))‖ :=
        congrArg (fun w : CriticalPath (intervalMeasure t0 d) =>
          ‖gradientCoordinates (intervalMeasure t0 d) w‖)
          (restrictPath_trans hat htv.le hvb le_rfl htd.le hdv v).symm
      _ ≤ ‖gradientCoordinates (intervalMeasure t0 dv) (restrictPath hat htv.le hvb v)‖ :=
        restrictPath_W_norm_le le_rfl htd.le hdv (restrictPath hat htv.le hvb v)
      _ ≤ eta := hv

end HartreeF.CriticalPathRestriction
