/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartCell
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Finite gap estimate up to 7849341184 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell7817341184 :
    ThetaLowerSegment 7817341184 7817373952 (156316020818271 / 20000) (6252667020159 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817341184 33 20 (56949 / 2500)
        (2277963 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817341184 7817373952 88415 _ _ (56949 / 2500) (111327 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817341184 7817373952 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817373952 :
    ThetaLowerSegment 7817373952 7817406720 (6252667020159 / 800) (31263468133659 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817373952 33 20 (56949 / 2500)
        (2277963 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817373952 7817406720 88415 _ _ (56949 / 2500) (111327 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817373952 7817406720 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817406720 :
    ThetaLowerSegment 7817406720 7817439488 (31263468133659 / 4000) (31263598432971 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817406720 33 20 (56949 / 2500)
        (2277963 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817406720 7817439488 88416 _ _ (56949 / 2500) (111327 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817406720 7817439488 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817439488 :
    ThetaLowerSegment 7817439488 7817472256 (31263598432971 / 4000) (390796587513623 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817439488 33 20 (2277961 / 100000)
        (569491 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817439488 7817472256 88416 _ _ (2277961 / 100000) (890617 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817439488 7817472256 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817472256 :
    ThetaLowerSegment 7817472256 7817505024 (390796587513623 / 50000)
      (781596434789437 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817472256 33 20 (2277961 / 100000)
        (569491 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817472256 7817505024 88416 _ _ (2277961 / 100000) (890617 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817472256 7817505024 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817505024 :
    ThetaLowerSegment 7817505024 7817537792 (781596434789437 / 100000)
      (156319940277389 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817505024 33 20 (1138981 / 50000)
        (455593 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817505024 7817537792 88416 _ _ (1138981 / 50000) (356247 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817505024 7817537792 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817537792 :
    ThetaLowerSegment 7817537792 7817570560 (156319940277389 / 20000)
      (781603043157199 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817537792 33 20 (1138981 / 50000)
        (455593 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817537792 7817570560 88416 _ _ (1138981 / 50000) (356247 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817537792 7817570560 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817570560 :
    ThetaLowerSegment 7817570560 7817603328 (781603043157199 / 100000)
      (781606350758023 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817570560 33 20 (1138981 / 50000)
        (455593 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817570560 7817603328 88417 _ _ (1138981 / 50000) (356247 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817570560 7817603328 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817603328 :
    ThetaLowerSegment 7817603328 7817636096 (781606350758023 / 100000)
      (781609699363633 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817603328 33 20 (2277963 / 100000)
        (1138983 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817603328 7817636096 88417 _ _ (2277963 / 100000) (1781237 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817603328 7817636096 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817636096 :
    ThetaLowerSegment 7817636096 7817668864 (781609699363633 / 100000)
      (390806497788047 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817636096 33 20 (2277963 / 100000)
        (1138983 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817636096 7817668864 88417 _ _ (2277963 / 100000) (1781237 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817636096 7817668864 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817668864 :
    ThetaLowerSegment 7817668864 7817701632 (390806497788047 / 50000)
      (390808121976379 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817668864 33 20 (569491 / 25000)
        (2277967 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817668864 7817701632 88417 _ _ (569491 / 25000) (1781239 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817668864 7817701632 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817701632 :
    ThetaLowerSegment 7817701632 7817734400 (390808121976379 / 50000)
      (390809745025729 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817701632 33 20 (569491 / 25000)
        (2277967 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817701632 7817734400 88417 _ _ (569491 / 25000) (1781239 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817701632 7817734400 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817734400 :
    ThetaLowerSegment 7817734400 7817767168 (390809745025729 / 50000)
      (781622731595653 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817734400 33 20 (455593 / 20000)
        (142373 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817734400 7817767168 88417 _ _ (455593 / 20000) (44531 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817734400 7817767168 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817767168 :
    ThetaLowerSegment 7817767168 7817799936 (781622731595653 / 100000)
      (195406500118857 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817767168 33 20 (455593 / 20000)
        (142373 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817767168 7817799936 88418 _ _ (455593 / 20000) (44531 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817767168 7817799936 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817799936 :
    ThetaLowerSegment 7817799936 7817832704 (195406500118857 / 25000)
      (195407288294747 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817799936 33 20 (455593 / 20000)
        (142373 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817799936 7817832704 88418 _ _ (455593 / 20000) (44531 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817799936 7817832704 12 1384 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817832704 :
    ThetaLowerSegment 7817832704 7817865472 (195407288294747 / 25000) (19540810950149 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817832704 33 20 (1138983 / 50000)
        (2277969 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817832704 7817865472 88418 _ _ (1138983 / 50000) (890621 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817832704 7817865472 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817865472 :
    ThetaLowerSegment 7817865472 7817898240 (19540810950149 / 2500) (390817844331721 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817865472 33 20 (1138983 / 50000)
        (2277969 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817865472 7817898240 88418 _ _ (1138983 / 50000) (890621 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817865472 7817898240 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817898240 :
    ThetaLowerSegment 7817898240 7817931008 (390817844331721 / 50000)
      (781638984881691 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817898240 33 20 (2277967 / 100000)
        (227797 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817898240 7817931008 88418 _ _ (2277967 / 100000) (1781243 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817898240 7817931008 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817931008 :
    ThetaLowerSegment 7817931008 7817963776 (781638984881691 / 100000)
      (390821079044861 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817931008 33 20 (2277967 / 100000)
        (227797 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817931008 7817963776 88419 _ _ (2277967 / 100000) (1781243 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817931008 7817963776 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817963776 :
    ThetaLowerSegment 7817963776 7817980160 (390821079044861 / 50000)
      (195410948417507 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817963776 33 20 (2277967 / 100000)
        (227797 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817963776 7817980160 88419 _ _ (2277967 / 100000) (1781243 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817963776 7817980160 11 718 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817980160 :
    ThetaLowerSegment 7817980160 7817996544 (195410948417507 / 25000)
      (195411361299207 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817980160 33 20 (142373 / 6250)
        (2277971 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817980160 7817996544 88419 _ _ (142373 / 6250) (356249 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817980160 7817996544 11 725 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7817996544 :
    ThetaLowerSegment 7817996544 7818029312 (195411361299207 / 25000) (39082433881671 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7817996544 33 20 (142373 / 6250)
        (2277971 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7817996544 7818029312 88419 _ _ (142373 / 6250) (356249 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7817996544 7818029312 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818029312 :
    ThetaLowerSegment 7818029312 7818045696 (39082433881671 / 5000) (195412582859547 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818029312 33 20 (142373 / 6250)
        (2277971 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818029312 7818045696 88419 _ _ (142373 / 6250) (356249 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818029312 7818045696 11 726 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818045696 :
    ThetaLowerSegment 7818045696 7818062080 (195412582859547 / 25000)
      (390825978954027 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818045696 33 20 (2277969 / 100000)
        (569493 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818045696 7818062080 88419 _ _ (2277969 / 100000) (1781247 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818045696 7818062080 11 714 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818062080 :
    ThetaLowerSegment 7818062080 7818078464 (390825978954027 / 50000)
      (156330723709491 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818062080 33 20 (2277969 / 100000)
        (569493 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818062080 7818078464 88419 _ _ (2277969 / 100000) (1781247 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818062080 7818078464 11 729 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818078464 :
    ThetaLowerSegment 7818078464 7818094848 (156330723709491 / 20000)
      (781655217681693 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818078464 33 20 (2277969 / 100000)
        (569493 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818078464 7818094848 88419 _ _ (2277969 / 100000) (1781247 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818078464 7818094848 11 702 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818094848 :
    ThetaLowerSegment 7818094848 7818111232 (781655217681693 / 100000) (39082845510633 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818094848 33 20 (2277969 / 100000)
        (569493 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818094848 7818111232 88419 _ _ (2277969 / 100000) (1781247 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818094848 7818111232 11 743 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818111232 :
    ThetaLowerSegment 7818111232 7818144000 (39082845510633 / 5000) (156332022151821 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818111232 33 20 (2277969 / 100000)
        (569493 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818111232 7818144000 88420 _ _ (2277969 / 100000) (1781247 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818111232 7818144000 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818144000 :
    ThetaLowerSegment 7818144000 7818160384 (156332022151821 / 20000)
      (156332347445937 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818144000 33 20 (227797 / 10000)
        (2277973 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818144000 7818160384 88420 _ _ (227797 / 10000) (55664 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818144000 7818160384 11 714 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818160384 :
    ThetaLowerSegment 7818160384 7818176768 (156332347445937 / 20000) (31266534365773 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818160384 33 20 (227797 / 10000)
        (2277973 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818160384 7818176768 88420 _ _ (227797 / 10000) (55664 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818160384 7818176768 11 712 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818176768 :
    ThetaLowerSegment 7818176768 7818193152 (31266534365773 / 4000) (156332998489763 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818176768 33 20 (227797 / 10000)
        (2277973 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818176768 7818193152 88420 _ _ (227797 / 10000) (55664 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818176768 7818193152 11 717 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818193152 :
    ThetaLowerSegment 7818193152 7818209536 (156332998489763 / 20000)
      (156333337451699 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818193152 33 20 (227797 / 10000)
        (2277973 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818193152 7818209536 88420 _ _ (227797 / 10000) (55664 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818193152 7818209536 11 744 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818209536 :
    ThetaLowerSegment 7818209536 7818225920 (156333337451699 / 20000)
      (390834196729387 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818209536 33 20 (2277971 / 100000)
        (1138987 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818209536 7818225920 88420 _ _ (2277971 / 100000) (285 / 16) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818209536 7818225920 11 749 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818225920 :
    ThetaLowerSegment 7818225920 7818258688 (390834196729387 / 50000)
      (781671625899623 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818225920 33 20 (2277971 / 100000)
        (1138987 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818225920 7818258688 88420 _ _ (2277971 / 100000) (285 / 16) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818225920 7818258688 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818258688 :
    ThetaLowerSegment 7818258688 7818275072 (781671625899623 / 100000)
      (78167325920483 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818258688 33 20 (2277971 / 100000)
        (1138987 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818258688 7818275072 88420 _ _ (2277971 / 100000) (285 / 16) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818258688 7818275072 11 717 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818275072 :
    ThetaLowerSegment 7818275072 7818291456 (78167325920483 / 10000) (390837463339801 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818275072 33 20 (2277971 / 100000)
        (1138987 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818275072 7818291456 88421 _ _ (2277971 / 100000) (285 / 16) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818275072 7818291456 11 732 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818291456 :
    ThetaLowerSegment 7818291456 7818324224 (390837463339801 / 50000)
      (390839048808313 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818291456 33 20 (569493 / 25000) (91119 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818291456 7818324224 88421 _ _ (569493 / 25000) (445313 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818291456 7818324224 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818324224 :
    ThetaLowerSegment 7818324224 7818340608 (390839048808313 / 50000)
      (390839857488373 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818324224 33 20 (569493 / 25000) (91119 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818324224 7818340608 88421 _ _ (569493 / 25000) (445313 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818324224 7818340608 11 710 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818340608 :
    ThetaLowerSegment 7818340608 7818356992 (390839857488373 / 50000)
      (390840660473503 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818340608 33 20 (569493 / 25000) (91119 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818340608 7818356992 88421 _ _ (569493 / 25000) (445313 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818340608 7818356992 11 705 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818356992 :
    ThetaLowerSegment 7818356992 7818373376 (390840660473503 / 50000)
      (195420730021013 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818356992 33 20 (2277973 / 100000)
        (284747 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818356992 7818373376 88421 _ _ (2277973 / 100000) (1781253 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818356992 7818373376 11 702 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818373376 :
    ThetaLowerSegment 7818373376 7818389760 (195420730021013 / 25000)
      (195421140056153 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818373376 33 20 (2277973 / 100000)
        (284747 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818373376 7818389760 88421 _ _ (2277973 / 100000) (1781253 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818373376 7818389760 11 720 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818389760 :
    ThetaLowerSegment 7818389760 7818406144 (195421140056153 / 25000) (3908431411861 / 500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818389760 33 20 (2277973 / 100000)
        (284747 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818389760 7818406144 88421 _ _ (2277973 / 100000) (1781253 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818389760 7818406144 11 756 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818406144 :
    ThetaLowerSegment 7818406144 7818422528 (3908431411861 / 500) (24427748148017 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818406144 33 20 (2277973 / 100000)
        (284747 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818406144 7818422528 88421 _ _ (2277973 / 100000) (1781253 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818406144 7818422528 11 728 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818422528 :
    ThetaLowerSegment 7818422528 7818438912 (24427748148017 / 3125) (781689601378861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818422528 33 20 (2277973 / 100000)
        (284747 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818422528 7818438912 88421 _ _ (2277973 / 100000) (1781253 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818422528 7818438912 11 729 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818438912 :
    ThetaLowerSegment 7818438912 7818455296 (781689601378861 / 100000)
      (781691275689751 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818438912 33 20 (1138987 / 50000)
        (2277977 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818438912 7818455296 88421 _ _ (1138987 / 50000) (356251 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818438912 7818455296 11 735 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818455296 :
    ThetaLowerSegment 7818455296 7818471680 (781691275689751 / 100000)
      (781692854325733 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818455296 33 20 (1138987 / 50000)
        (2277977 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818455296 7818471680 88422 _ _ (1138987 / 50000) (356251 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818455296 7818471680 11 693 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818471680 :
    ThetaLowerSegment 7818471680 7818488064 (781692854325733 / 100000)
      (781694487633091 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818471680 33 20 (1138987 / 50000)
        (2277977 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818471680 7818488064 88422 _ _ (1138987 / 50000) (356251 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818471680 7818488064 11 717 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818488064 :
    ThetaLowerSegment 7818488064 7818504448 (781694487633091 / 100000)
      (781696111828553 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818488064 33 20 (1138987 / 50000)
        (2277977 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818488064 7818504448 88422 _ _ (1138987 / 50000) (356251 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818488064 7818504448 11 713 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818504448 :
    ThetaLowerSegment 7818504448 7818520832 (781696111828553 / 100000)
      (156339551760751 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818504448 33 20 (1138987 / 50000)
        (2277977 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818504448 7818520832 88422 _ _ (1138987 / 50000) (356251 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818504448 7818520832 11 723 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818520832 :
    ThetaLowerSegment 7818520832 7818537216 (156339551760751 / 20000)
      (156339877966771 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818520832 33 20 (91119 / 4000)
        (1138989 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818520832 7818537216 88422 _ _ (91119 / 4000) (1781257 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818520832 7818537216 11 716 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818537216 :
    ThetaLowerSegment 7818537216 7818553600 (156339877966771 / 20000)
      (156340212373501 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818537216 33 20 (91119 / 4000)
        (1138989 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818537216 7818553600 88422 _ _ (91119 / 4000) (1781257 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818537216 7818553600 11 734 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818553600 :
    ThetaLowerSegment 7818553600 7818569984 (156340212373501 / 20000)
      (156340552247371 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818553600 33 20 (91119 / 4000)
        (1138989 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818553600 7818569984 88422 _ _ (91119 / 4000) (1781257 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818553600 7818569984 11 746 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818569984 :
    ThetaLowerSegment 7818569984 7818586368 (156340552247371 / 20000) (78170444921633 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818569984 33 20 (91119 / 4000)
        (1138989 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818569984 7818586368 88422 _ _ (91119 / 4000) (1781257 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818569984 7818586368 11 741 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818586368 :
    ThetaLowerSegment 7818586368 7818619136 (78170444921633 / 10000) (78170772950033 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818586368 33 20 (91119 / 4000)
        (1138989 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818586368 7818619136 88422 _ _ (91119 / 4000) (1781257 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818586368 7818619136 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818619136 :
    ThetaLowerSegment 7818619136 7818651904 (78170772950033 / 10000) (390855517421753 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818619136 33 20 (284747 / 12500)
        (2277979 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818619136 7818651904 88422 _ _ (284747 / 12500) (890629 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818619136 7818651904 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818651904 :
    ThetaLowerSegment 7818651904 7818684672 (390855517421753 / 50000)
      (390857117699893 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818651904 33 20 (284747 / 12500)
        (2277979 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818651904 7818684672 88423 _ _ (284747 / 12500) (890629 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818651904 7818684672 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818684672 :
    ThetaLowerSegment 7818684672 7818701056 (390857117699893 / 50000)
      (781715927936697 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818684672 33 20 (2277977 / 100000)
        (113899 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818684672 7818701056 88423 _ _ (2277977 / 100000) (89063 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818684672 7818701056 11 743 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818701056 :
    ThetaLowerSegment 7818701056 7818733824 (781715927936697 / 100000)
      (156343884470683 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818701056 33 20 (2277977 / 100000)
        (113899 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818701056 7818733824 88423 _ _ (2277977 / 100000) (89063 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818701056 7818733824 12 1534 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818733824 :
    ThetaLowerSegment 7818733824 7818766592 (156343884470683 / 20000)
      (781722752755789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818733824 33 20 (2277977 / 100000)
        (113899 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818733824 7818766592 88423 _ _ (2277977 / 100000) (89063 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818733824 7818766592 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818766592 :
    ThetaLowerSegment 7818766592 7818799360 (781722752755789 / 100000)
      (781725905477341 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818766592 33 20 (1138989 / 50000)
        (2277981 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818766592 7818799360 88423 _ _ (1138989 / 50000) (890631 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818766592 7818799360 12 1384 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818799360 :
    ThetaLowerSegment 7818799360 7818832128 (781725905477341 / 100000)
      (781729172097793 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818799360 33 20 (1138989 / 50000)
        (2277981 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818799360 7818832128 88423 _ _ (1138989 / 50000) (890631 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818799360 7818832128 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818832128 :
    ThetaLowerSegment 7818832128 7818864896 (781729172097793 / 100000)
      (781732461499469 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818832128 33 20 (2277979 / 100000)
        (1138991 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818832128 7818864896 88424 _ _ (2277979 / 100000) (1781263 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818832128 7818864896 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818864896 :
    ThetaLowerSegment 7818864896 7818897664 (781732461499469 / 100000)
      (390867919871163 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818864896 33 20 (2277979 / 100000)
        (1138991 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818864896 7818897664 88424 _ _ (2277979 / 100000) (1781263 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818864896 7818897664 12 1483 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818897664 :
    ThetaLowerSegment 7818897664 7818930432 (390867919871163 / 50000)
      (390869537236253 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818897664 33 20 (2277979 / 100000)
        (1138991 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818897664 7818930432 88424 _ _ (2277979 / 100000) (1781263 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818897664 7818930432 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818930432 :
    ThetaLowerSegment 7818930432 7818963200 (390869537236253 / 50000)
      (390871143212153 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818930432 33 20 (113899 / 5000)
        (2277983 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818930432 7818963200 88424 _ _ (113899 / 5000) (356253 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818930432 7818963200 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818963200 :
    ThetaLowerSegment 7818963200 7818995968 (390871143212153 / 50000)
      (390872779940783 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818963200 33 20 (113899 / 5000)
        (2277983 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818963200 7818995968 88424 _ _ (113899 / 5000) (356253 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818963200 7818995968 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7818995968 :
    ThetaLowerSegment 7818995968 7819028736 (390872779940783 / 50000)
      (781748901679693 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7818995968 33 20 (2277981 / 100000)
        (71187 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7818995968 7819028736 88425 _ _ (2277981 / 100000) (1781267 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7818995968 7819028736 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819028736 :
    ThetaLowerSegment 7819028736 7819061504 (781748901679693 / 100000)
      (390876083013233 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819028736 33 20 (2277981 / 100000)
        (71187 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819028736 7819061504 88425 _ _ (2277981 / 100000) (1781267 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819028736 7819061504 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819061504 :
    ThetaLowerSegment 7819061504 7819094272 (390876083013233 / 50000) (39087768557357 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819061504 33 20 (1138991 / 50000)
        (455597 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819061504 7819094272 88425 _ _ (1138991 / 50000) (445317 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819061504 7819094272 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819094272 :
    ThetaLowerSegment 7819094272 7819127040 (39087768557357 / 5000) (390879338249511 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819094272 33 20 (1138991 / 50000)
        (455597 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819094272 7819127040 88425 _ _ (1138991 / 50000) (445317 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819094272 7819127040 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819127040 :
    ThetaLowerSegment 7819127040 7819159808 (390879338249511 / 50000)
      (195440519381537 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819127040 33 20 (1138991 / 50000)
        (455597 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819127040 7819159808 88425 _ _ (1138991 / 50000) (445317 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819127040 7819159808 12 1493 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819159808 :
    ThetaLowerSegment 7819159808 7819192576 (195440519381537 / 25000)
      (195441312119621 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819159808 33 20 (2277983 / 100000)
        (1138993 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819159808 7819192576 88426 _ _ (2277983 / 100000) (178127 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819159808 7819192576 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819192576 :
    ThetaLowerSegment 7819192576 7819225344 (195441312119621 / 25000)
      (781768490048293 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819192576 33 20 (2277983 / 100000)
        (1138993 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819192576 7819225344 88426 _ _ (2277983 / 100000) (178127 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819192576 7819225344 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819225344 :
    ThetaLowerSegment 7819225344 7819258112 (781768490048293 / 100000)
      (781771681503877 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819225344 33 20 (71187 / 3125)
        (2277987 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819225344 7819258112 88426 _ _ (71187 / 3125) (222659 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819225344 7819258112 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819258112 :
    ThetaLowerSegment 7819258112 7819290880 (781771681503877 / 100000) (31271001387853 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819258112 33 20 (71187 / 3125)
        (2277987 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819258112 7819290880 88426 _ _ (71187 / 3125) (222659 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819258112 7819290880 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819290880 :
    ThetaLowerSegment 7819290880 7819323648 (31271001387853 / 4000) (781778346885061 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819290880 33 20 (71187 / 3125)
        (2277987 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819290880 7819323648 88426 _ _ (71187 / 3125) (222659 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819290880 7819323648 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819323648 :
    ThetaLowerSegment 7819323648 7819356416 (781778346885061 / 100000)
      (390890769171023 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819323648 33 20 (455597 / 20000)
        (569497 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819323648 7819356416 88426 _ _ (455597 / 20000) (1781273 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819323648 7819356416 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819356416 :
    ThetaLowerSegment 7819356416 7819389184 (390890769171023 / 50000)
      (781784875590071 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819356416 33 20 (455597 / 20000)
        (569497 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819356416 7819389184 88427 _ _ (455597 / 20000) (1781273 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819356416 7819389184 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819389184 :
    ThetaLowerSegment 7819389184 7819421952 (781784875590071 / 100000)
      (156357644390301 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819389184 33 20 (1138993 / 50000)
        (2277989 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819389184 7819421952 88427 _ _ (1138993 / 50000) (71251 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819389184 7819421952 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819421952 :
    ThetaLowerSegment 7819421952 7819454720 (156357644390301 / 20000)
      (781791511363289 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819421952 33 20 (1138993 / 50000)
        (2277989 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819421952 7819454720 88427 _ _ (1138993 / 50000) (71251 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819421952 7819454720 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819454720 :
    ThetaLowerSegment 7819454720 7819487488 (781791511363289 / 100000)
      (195448698485639 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819454720 33 20 (2277987 / 100000)
        (227799 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819454720 7819487488 88427 _ _ (2277987 / 100000) (445319 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819454720 7819487488 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819487488 :
    ThetaLowerSegment 7819487488 7819520256 (195448698485639 / 25000)
      (195449532228881 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819487488 33 20 (2277987 / 100000)
        (227799 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819487488 7819520256 88427 _ _ (2277987 / 100000) (445319 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819487488 7819520256 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819520256 :
    ThetaLowerSegment 7819520256 7819553024 (195449532228881 / 25000)
      (781801411494791 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819520256 33 20 (2277987 / 100000)
        (227799 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819520256 7819553024 88428 _ _ (2277987 / 100000) (445319 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819520256 7819553024 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819553024 :
    ThetaLowerSegment 7819553024 7819585792 (781801411494791 / 100000)
      (781804655349703 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819553024 33 20 (569497 / 25000)
        (2277991 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819553024 7819585792 88428 _ _ (569497 / 25000) (890639 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819553024 7819585792 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819585792 :
    ThetaLowerSegment 7819585792 7819618560 (781804655349703 / 100000) (31272315512587 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819585792 33 20 (569497 / 25000)
        (2277991 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819585792 7819618560 88428 _ _ (569497 / 25000) (890639 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819585792 7819618560 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819618560 :
    ThetaLowerSegment 7819618560 7819651328 (31272315512587 / 4000) (781811131671011 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819618560 33 20 (2277989 / 100000)
        (284749 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819618560 7819651328 88428 _ _ (2277989 / 100000) (11133 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819618560 7819651328 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819651328 :
    ThetaLowerSegment 7819651328 7819684096 (781811131671011 / 100000)
      (78181452815261 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819651328 33 20 (2277989 / 100000)
        (284749 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819651328 7819684096 88428 _ _ (2277989 / 100000) (11133 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819651328 7819684096 12 1491 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819684096 :
    ThetaLowerSegment 7819684096 7819716864 (78181452815261 / 10000)
      (781817769730957 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819684096 33 20 (2277989 / 100000)
        (284749 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819684096 7819716864 88428 _ _ (2277989 / 100000) (11133 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819684096 7819716864 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819716864 :
    ThetaLowerSegment 7819716864 7819749632 (781817769730957 / 100000)
      (781820990808817 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819716864 33 20 (227799 / 10000)
        (2277993 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819716864 7819749632 88429 _ _ (227799 / 10000) (1781281 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819716864 7819749632 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819749632 :
    ThetaLowerSegment 7819749632 7819782400 (781820990808817 / 100000)
      (781824236944567 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819749632 33 20 (227799 / 10000)
        (2277993 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819749632 7819782400 88429 _ _ (227799 / 10000) (1781281 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819749632 7819782400 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819782400 :
    ThetaLowerSegment 7819782400 7819815168 (781824236944567 / 100000)
      (390913805324619 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819782400 33 20 (2277991 / 100000)
        (1138997 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819782400 7819815168 88429 _ _ (2277991 / 100000) (1781283 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819782400 7819815168 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819815168 :
    ThetaLowerSegment 7819815168 7819847936 (390913805324619 / 50000)
      (781830920570161 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819815168 33 20 (2277991 / 100000)
        (1138997 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819815168 7819847936 88429 _ _ (2277991 / 100000) (1781283 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819815168 7819847936 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819847936 :
    ThetaLowerSegment 7819847936 7819880704 (781830920570161 / 100000)
      (781834191766673 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819847936 33 20 (284749 / 12500)
        (455599 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819847936 7819880704 88429 _ _ (284749 / 12500) (356257 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819847936 7819880704 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819880704 :
    ThetaLowerSegment 7819880704 7819913472 (781834191766673 / 100000)
      (781837412847361 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819880704 33 20 (284749 / 12500)
        (455599 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819880704 7819913472 88430 _ _ (284749 / 12500) (356257 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819880704 7819913472 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819913472 :
    ThetaLowerSegment 7819913472 7819946240 (781837412847361 / 100000)
      (781840649873993 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819913472 33 20 (284749 / 12500)
        (455599 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819913472 7819946240 88430 _ _ (284749 / 12500) (356257 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819913472 7819946240 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819946240 :
    ThetaLowerSegment 7819946240 7819979008 (781840649873993 / 100000)
      (97730484154261 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819946240 33 20 (2277993 / 100000)
        (569499 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819946240 7819979008 88430 _ _ (2277993 / 100000) (890643 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819946240 7819979008 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7819979008 :
    ThetaLowerSegment 7819979008 7820011776 (97730484154261 / 12500) (195461786108009 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7819979008 33 20 (2277993 / 100000)
        (569499 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7819979008 7820011776 88430 _ _ (2277993 / 100000) (890643 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7819979008 7820011776 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820011776 :
    ThetaLowerSegment 7820011776 7820044544 (195461786108009 / 25000) (24432825061358 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820011776 33 20 (1138997 / 50000)
        (2277997 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820011776 7820044544 88430 _ _ (1138997 / 50000) (222661 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820011776 7820044544 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820044544 :
    ThetaLowerSegment 7820044544 7820077312 (24432825061358 / 3125) (195463449043629 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820044544 33 20 (1138997 / 50000)
        (2277997 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820044544 7820077312 88431 _ _ (1138997 / 50000) (222661 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820044544 7820077312 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820077312 :
    ThetaLowerSegment 7820077312 7820110080 (195463449043629 / 25000)
      (781857074209321 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820077312 33 20 (455599 / 20000)
        (1138999 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820077312 7820110080 88431 _ _ (455599 / 20000) (178129 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820077312 7820110080 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820110080 :
    ThetaLowerSegment 7820110080 7820142848 (781857074209321 / 100000) (24433131878763 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820110080 33 20 (455599 / 20000)
        (1138999 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820110080 7820142848 88431 _ _ (455599 / 20000) (178129 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820110080 7820142848 12 1381 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820142848 :
    ThetaLowerSegment 7820142848 7820175616 (24433131878763 / 3125) (390931738826633 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820142848 33 20 (455599 / 20000)
        (1138999 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820142848 7820175616 88431 _ _ (455599 / 20000) (178129 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820142848 7820175616 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820175616 :
    ThetaLowerSegment 7820175616 7820208384 (390931738826633 / 50000)
      (390933375566759 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820175616 33 20 (569499 / 25000)
        (2277999 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820175616 7820208384 88431 _ _ (569499 / 25000) (1781291 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820175616 7820208384 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820208384 :
    ThetaLowerSegment 7820208384 7820241152 (390933375566759 / 50000)
      (390935025974861 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820208384 33 20 (569499 / 25000)
        (2277999 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820208384 7820241152 88431 _ _ (569499 / 25000) (1781291 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820208384 7820241152 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820241152 :
    ThetaLowerSegment 7820241152 7820273920 (390935025974861 / 50000)
      (390936720804629 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820241152 33 20 (2277997 / 100000) (1139 / 50) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820241152 7820273920 88432 _ _ (2277997 / 100000) (1781293 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820241152 7820273920 12 1488 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820273920 :
    ThetaLowerSegment 7820273920 7820306688 (390936720804629 / 50000) (48867294835559 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820273920 33 20 (2277997 / 100000) (1139 / 50) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820273920 7820306688 88432 _ _ (2277997 / 100000) (1781293 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820273920 7820306688 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820306688 :
    ThetaLowerSegment 7820306688 7820339456 (48867294835559 / 6250) (390939941892387 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820306688 33 20 (2277997 / 100000) (1139 / 50) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820306688 7820339456 88432 _ _ (2277997 / 100000) (1781293 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820306688 7820339456 12 1390 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820339456 :
    ThetaLowerSegment 7820339456 7820372224 (390939941892387 / 50000) (19547079501197 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820339456 33 20 (1138999 / 50000)
        (2278001 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820339456 7820372224 88432 _ _ (1138999 / 50000) (356259 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820339456 7820372224 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820372224 :
    ThetaLowerSegment 7820372224 7820404992 (19547079501197 / 2500) (9773580185063 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820372224 33 20 (1138999 / 50000)
        (2278001 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820372224 7820404992 88432 _ _ (1138999 / 50000) (356259 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820372224 7820404992 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820404992 :
    ThetaLowerSegment 7820404992 7820437760 (9773580185063 / 1250) (390944827059809 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820404992 33 20 (2277999 / 100000)
        (1139001 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820404992 7820437760 88433 _ _ (2277999 / 100000) (111331 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820404992 7820437760 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820437760 :
    ThetaLowerSegment 7820437760 7820470528 (390944827059809 / 50000)
      (781892977720159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820437760 33 20 (2277999 / 100000)
        (1139001 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820437760 7820470528 88433 _ _ (2277999 / 100000) (111331 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820437760 7820470528 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820470528 :
    ThetaLowerSegment 7820470528 7820503296 (781892977720159 / 100000)
      (781896203368159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820470528 33 20 (1139 / 50) (2278003 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820470528 7820503296 88433 _ _ (1139 / 50) (890649 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820470528 7820503296 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820503296 :
    ThetaLowerSegment 7820503296 7820536064 (781896203368159 / 100000)
      (781899481410159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820503296 33 20 (1139 / 50) (2278003 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820503296 7820536064 88433 _ _ (1139 / 50) (890649 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820503296 7820536064 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820536064 :
    ThetaLowerSegment 7820536064 7820568832 (781899481410159 / 100000)
      (781902896132159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820536064 33 20 (1139 / 50) (2278003 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820536064 7820568832 88433 _ _ (1139 / 50) (890649 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820536064 7820568832 12 1499 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820568832 :
    ThetaLowerSegment 7820568832 7820601600 (781902896132159 / 100000)
      (390953036971777 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820568832 33 20 (2278001 / 100000)
        (569501 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820568832 7820601600 88433 _ _ (2278001 / 100000) (17813 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820568832 7820601600 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820601600 :
    ThetaLowerSegment 7820601600 7820634368 (390953036971777 / 50000)
      (156381866752597 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820601600 33 20 (2278001 / 100000)
        (569501 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820601600 7820634368 88434 _ _ (2278001 / 100000) (17813 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820601600 7820634368 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820634368 :
    ThetaLowerSegment 7820634368 7820667136 (156381866752597 / 20000)
      (781912595861849 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820634368 33 20 (1139001 / 50000)
        (455601 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820634368 7820667136 88434 _ _ (1139001 / 50000) (1781301 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820634368 7820667136 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820667136 :
    ThetaLowerSegment 7820667136 7820699904 (781912595861849 / 100000)
      (156383176603747 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820667136 33 20 (1139001 / 50000)
        (455601 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820667136 7820699904 88434 _ _ (1139001 / 50000) (1781301 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820667136 7820699904 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820699904 :
    ThetaLowerSegment 7820699904 7820732672 (156383176603747 / 20000)
      (781919145117599 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820699904 33 20 (1139001 / 50000)
        (455601 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820699904 7820732672 88434 _ _ (1139001 / 50000) (1781301 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820699904 7820732672 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820732672 :
    ThetaLowerSegment 7820732672 7820765440 (781919145117599 / 100000)
      (390961159187889 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820732672 33 20 (2278003 / 100000)
        (1139003 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820732672 7820765440 88434 _ _ (2278003 / 100000) (1781303 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820732672 7820765440 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820765440 :
    ThetaLowerSegment 7820765440 7820798208 (390961159187889 / 50000)
      (156385114728413 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820765440 33 20 (2278003 / 100000)
        (1139003 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820765440 7820798208 88435 _ _ (2278003 / 100000) (1781303 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820765440 7820798208 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820798208 :
    ThetaLowerSegment 7820798208 7820830976 (156385114728413 / 20000)
      (781928885859881 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820798208 33 20 (569501 / 25000)
        (2278007 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820798208 7820830976 88435 _ _ (569501 / 25000) (356261 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820798208 7820830976 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820830976 :
    ThetaLowerSegment 7820830976 7820863744 (781928885859881 / 100000)
      (156386429136721 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820830976 33 20 (569501 / 25000)
        (2278007 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820830976 7820863744 88435 _ _ (569501 / 25000) (356261 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820830976 7820863744 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820863744 :
    ThetaLowerSegment 7820863744 7820896512 (156386429136721 / 20000) (78193539184073 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820863744 33 20 (455601 / 20000)
        (284751 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820863744 7820896512 88435 _ _ (455601 / 20000) (890653 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820863744 7820896512 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820896512 :
    ThetaLowerSegment 7820896512 7820912896 (78193539184073 / 10000) (125109919289 / 16) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820896512 33 20 (455601 / 20000)
        (284751 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820896512 7820912896 88435 _ _ (455601 / 20000) (890653 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820896512 7820912896 11 704 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820912896 :
    ThetaLowerSegment 7820912896 7820929280 (125109919289 / 16) (9774233345149 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820912896 33 20 (455601 / 20000)
        (284751 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820912896 7820929280 88435 _ _ (455601 / 20000) (890653 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820912896 7820929280 11 734 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820929280 :
    ThetaLowerSegment 7820929280 7820945664 (9774233345149 / 1250) (156388072033927 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820929280 33 20 (455601 / 20000)
        (284751 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820929280 7820945664 88436 _ _ (455601 / 20000) (890653 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820929280 7820945664 11 743 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820945664 :
    ThetaLowerSegment 7820945664 7820978432 (156388072033927 / 20000)
      (156388748601709 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820945664 33 20 (1139003 / 50000)
        (2278009 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820945664 7820978432 88436 _ _ (1139003 / 50000) (445327 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820945664 7820978432 12 1485 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7820978432 :
    ThetaLowerSegment 7820978432 7821011200 (156388748601709 / 20000)
      (156389390999401 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7820978432 33 20 (1139003 / 50000)
        (2278009 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7820978432 7821011200 88436 _ _ (1139003 / 50000) (445327 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7820978432 7821011200 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821011200 :
    ThetaLowerSegment 7821011200 7821043968 (156389390999401 / 20000)
      (781950182931507 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821011200 33 20 (1139003 / 50000)
        (2278009 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821011200 7821043968 88436 _ _ (1139003 / 50000) (445327 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821011200 7821043968 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821043968 :
    ThetaLowerSegment 7821043968 7821076736 (781950182931507 / 100000)
      (781953513377741 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821043968 33 20 (2278007 / 100000)
        (227801 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821043968 7821076736 88436 _ _ (2278007 / 100000) (178131 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821043968 7821076736 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821076736 :
    ThetaLowerSegment 7821076736 7821109504 (781953513377741 / 100000)
      (781956811931877 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821076736 33 20 (2278007 / 100000)
        (227801 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821076736 7821109504 88436 _ _ (2278007 / 100000) (178131 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821076736 7821109504 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821109504 :
    ThetaLowerSegment 7821109504 7821142272 (781956811931877 / 100000)
      (781960169715669 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821109504 33 20 (284751 / 12500)
        (2278011 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821109504 7821142272 88437 _ _ (284751 / 12500) (1781311 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821109504 7821142272 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821142272 :
    ThetaLowerSegment 7821142272 7821175040 (781960169715669 / 100000)
      (781963297420653 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821142272 33 20 (284751 / 12500)
        (2278011 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821142272 7821175040 88437 _ _ (284751 / 12500) (1781311 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821142272 7821175040 12 1373 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821175040 :
    ThetaLowerSegment 7821175040 7821207808 (781963297420653 / 100000)
      (156393314639519 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821175040 33 20 (2278009 / 100000)
        (569503 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821175040 7821207808 88437 _ _ (2278009 / 100000) (1781313 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821175040 7821207808 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821207808 :
    ThetaLowerSegment 7821207808 7821240576 (156393314639519 / 20000)
      (781969880866663 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821207808 33 20 (2278009 / 100000)
        (569503 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821207808 7821240576 88437 _ _ (2278009 / 100000) (1781313 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821207808 7821240576 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821240576 :
    ThetaLowerSegment 7821240576 7821273344 (781969880866663 / 100000) (48873320439343 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821240576 33 20 (2278009 / 100000)
        (569503 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821240576 7821273344 88437 _ _ (2278009 / 100000) (1781313 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821240576 7821273344 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821273344 :
    ThetaLowerSegment 7821273344 7821306112 (48873320439343 / 6250) (390988241269109 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821273344 33 20 (227801 / 10000)
        (2278013 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821273344 7821306112 88437 _ _ (227801 / 10000) (890657 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821273344 7821306112 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821306112 :
    ThetaLowerSegment 7821306112 7821338880 (390988241269109 / 50000) (24436870366094 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821306112 33 20 (227801 / 10000)
        (2278013 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821306112 7821338880 88438 _ _ (227801 / 10000) (890657 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821306112 7821338880 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821338880 :
    ThetaLowerSegment 7821338880 7821371648 (24436870366094 / 3125) (781983116104771 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821338880 33 20 (2278011 / 100000)
        (1139007 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821338880 7821371648 88438 _ _ (2278011 / 100000) (445329 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821338880 7821371648 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821371648 :
    ThetaLowerSegment 7821371648 7821404416 (781983116104771 / 100000)
      (97748290158281 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821371648 33 20 (2278011 / 100000)
        (1139007 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821371648 7821404416 88438 _ _ (2278011 / 100000) (445329 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821371648 7821404416 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821404416 :
    ThetaLowerSegment 7821404416 7821437184 (97748290158281 / 12500) (156397923509633 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821404416 33 20 (2278011 / 100000)
        (1139007 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821404416 7821437184 88438 _ _ (2278011 / 100000) (445329 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821404416 7821437184 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821437184 :
    ThetaLowerSegment 7821437184 7821469952 (156397923509633 / 20000)
      (781993050512249 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821437184 33 20 (569503 / 25000)
        (455603 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821437184 7821469952 88438 _ _ (569503 / 25000) (890659 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821437184 7821469952 12 1507 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821469952 :
    ThetaLowerSegment 7821469952 7821502720 (781993050512249 / 100000)
      (781996358185673 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821469952 33 20 (569503 / 25000)
        (455603 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821469952 7821502720 88439 _ _ (569503 / 25000) (890659 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821469952 7821502720 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821502720 :
    ThetaLowerSegment 7821502720 7821535488 (781996358185673 / 100000)
      (195499895393517 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821502720 33 20 (2278013 / 100000)
        (71188 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821502720 7821535488 88439 _ _ (2278013 / 100000) (1781319 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821502720 7821535488 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821535488 :
    ThetaLowerSegment 7821535488 7821568256 (195499895393517 / 25000)
      (782002800406437 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821535488 33 20 (2278013 / 100000)
        (71188 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821535488 7821568256 88439 _ _ (2278013 / 100000) (1781319 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821535488 7821568256 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821568256 :
    ThetaLowerSegment 7821568256 7821601024 (782002800406437 / 100000)
      (782006133140919 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821568256 33 20 (1139007 / 50000)
        (2278017 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821568256 7821601024 88439 _ _ (1139007 / 50000) (1781321 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821568256 7821601024 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821601024 :
    ThetaLowerSegment 7821601024 7821633792 (782006133140919 / 100000)
      (156401918688837 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821601024 33 20 (1139007 / 50000)
        (2278017 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821601024 7821633792 88439 _ _ (1139007 / 50000) (1781321 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821601024 7821633792 12 1519 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821633792 :
    ThetaLowerSegment 7821633792 7821666560 (156401918688837 / 20000)
      (782012750771589 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821633792 33 20 (1139007 / 50000)
        (2278017 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821633792 7821666560 88440 _ _ (1139007 / 50000) (1781321 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821633792 7821666560 12 1386 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821666560 :
    ThetaLowerSegment 7821666560 7821699328 (782012750771589 / 100000)
      (97752007590923 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821666560 33 20 (455603 / 20000)
        (1139009 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821666560 7821699328 88440 _ _ (455603 / 20000) (1781323 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821666560 7821699328 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821699328 :
    ThetaLowerSegment 7821699328 7821732096 (97752007590923 / 12500) (391009677368537 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821699328 33 20 (455603 / 20000)
        (1139009 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821699328 7821732096 88440 _ _ (455603 / 20000) (1781323 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821699328 7821732096 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821732096 :
    ThetaLowerSegment 7821732096 7821764864 (391009677368537 / 50000)
      (391011311845017 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821732096 33 20 (71188 / 3125)
        (2278019 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821732096 7821764864 88440 _ _ (71188 / 3125) (445331 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821732096 7821764864 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821764864 :
    ThetaLowerSegment 7821764864 7821797632 (391011311845017 / 50000)
      (391012939487449 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821764864 33 20 (71188 / 3125)
        (2278019 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821764864 7821797632 88440 _ _ (71188 / 3125) (445331 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821764864 7821797632 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821797632 :
    ThetaLowerSegment 7821797632 7821830400 (391012939487449 / 50000) (48876822172709 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821797632 33 20 (2278017 / 100000)
        (113901 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821797632 7821830400 88440 _ _ (2278017 / 100000) (890663 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821797632 7821830400 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821830400 :
    ThetaLowerSegment 7821830400 7821863168 (48876822172709 / 6250) (78203243055179 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821830400 33 20 (2278017 / 100000)
        (113901 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821830400 7821863168 88441 _ _ (2278017 / 100000) (890663 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821830400 7821863168 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821863168 :
    ThetaLowerSegment 7821863168 7821895936 (78203243055179 / 10000)
      (782035763290661 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821863168 33 20 (2278017 / 100000)
        (113901 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821863168 7821895936 88441 _ _ (2278017 / 100000) (890663 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821863168 7821895936 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821895936 :
    ThetaLowerSegment 7821895936 7821928704 (782035763290661 / 100000)
      (782039034524509 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821895936 33 20 (1139009 / 50000)
        (2278021 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821895936 7821928704 88441 _ _ (1139009 / 50000) (111333 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821895936 7821928704 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821928704 :
    ThetaLowerSegment 7821928704 7821961472 (782039034524509 / 100000)
      (782042248807907 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821928704 33 20 (1139009 / 50000)
        (2278021 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821928704 7821961472 88441 _ _ (1139009 / 50000) (111333 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821928704 7821961472 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821961472 :
    ThetaLowerSegment 7821961472 7821994240 (782042248807907 / 100000)
      (156409083962071 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821961472 33 20 (2278019 / 100000)
        (1139011 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821961472 7821994240 88441 _ _ (2278019 / 100000) (1781329 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821961472 7821994240 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7821994240 :
    ThetaLowerSegment 7821994240 7822027008 (156409083962071 / 20000)
      (782048695601677 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7821994240 33 20 (2278019 / 100000)
        (1139011 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7821994240 7822027008 88442 _ _ (2278019 / 100000) (1781329 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7821994240 7822027008 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822027008 :
    ThetaLowerSegment 7822027008 7822059776 (782048695601677 / 100000)
      (156410386988939 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822027008 33 20 (2278019 / 100000)
        (1139011 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822027008 7822059776 88442 _ _ (2278019 / 100000) (1781329 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822027008 7822059776 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822059776 :
    ThetaLowerSegment 7822059776 7822092544 (156410386988939 / 20000) (31282208976223 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822059776 33 20 (113901 / 5000)
        (2278023 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822059776 7822092544 88442 _ _ (113901 / 5000) (1781331 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822059776 7822092544 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822092544 :
    ThetaLowerSegment 7822092544 7822125312 (31282208976223 / 4000) (156411702773291 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822092544 33 20 (113901 / 5000)
        (2278023 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822092544 7822125312 88442 _ _ (113901 / 5000) (1781331 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822092544 7822125312 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822125312 :
    ThetaLowerSegment 7822125312 7822158080 (156411702773291 / 20000)
      (391030895969337 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822125312 33 20 (2278021 / 100000)
        (284753 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822125312 7822158080 88442 _ _ (2278021 / 100000) (1781333 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822125312 7822158080 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822158080 :
    ThetaLowerSegment 7822158080 7822190848 (391030895969337 / 50000) (3128260434949 / 400) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822158080 33 20 (2278021 / 100000)
        (284753 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822158080 7822190848 88442 _ _ (2278021 / 100000) (1781333 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822158080 7822190848 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822190848 :
    ThetaLowerSegment 7822190848 7822223616 (3128260434949 / 400) (78206836630871 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822190848 33 20 (1139011 / 50000)
        (91121 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822190848 7822223616 88443 _ _ (1139011 / 50000) (890667 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822190848 7822223616 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822223616 :
    ThetaLowerSegment 7822223616 7822256384 (78206836630871 / 10000) (391035830164261 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822223616 33 20 (1139011 / 50000)
        (91121 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822223616 7822256384 88443 _ _ (1139011 / 50000) (890667 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822223616 7822256384 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822256384 :
    ThetaLowerSegment 7822256384 7822289152 (391035830164261 / 50000) (48879686212911 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822256384 33 20 (1139011 / 50000)
        (91121 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822256384 7822289152 88443 _ _ (1139011 / 50000) (890667 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822256384 7822289152 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822289152 :
    ThetaLowerSegment 7822289152 7822321920 (48879686212911 / 6250) (391039141269963 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822289152 33 20 (2278023 / 100000)
        (1139013 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822289152 7822321920 88443 _ _ (2278023 / 100000) (222667 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822289152 7822321920 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822321920 :
    ThetaLowerSegment 7822321920 7822354688 (391039141269963 / 50000)
      (391040849787213 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822321920 33 20 (2278023 / 100000)
        (1139013 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822321920 7822354688 88443 _ _ (2278023 / 100000) (222667 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822321920 7822354688 12 1500 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822354688 :
    ThetaLowerSegment 7822354688 7822387456 (391040849787213 / 50000)
      (391042493381529 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822354688 33 20 (284753 / 12500)
        (2278027 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822354688 7822387456 88444 _ _ (284753 / 12500) (890669 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822354688 7822387456 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822387456 :
    ThetaLowerSegment 7822387456 7822420224 (391042493381529 / 50000)
      (391044143809917 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822387456 33 20 (284753 / 12500)
        (2278027 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822387456 7822420224 88444 _ _ (284753 / 12500) (890669 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822387456 7822420224 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822420224 :
    ThetaLowerSegment 7822420224 7822452992 (391044143809917 / 50000)
      (391045863718037 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822420224 33 20 (284753 / 12500)
        (2278027 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822420224 7822452992 88444 _ _ (284753 / 12500) (890669 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822420224 7822452992 12 1510 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822452992 :
    ThetaLowerSegment 7822452992 7822485760 (391045863718037 / 50000)
      (782095000957999 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822452992 33 20 (91121 / 4000) (569507 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822452992 7822485760 88444 _ _ (91121 / 4000) (1781339 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822452992 7822485760 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822485760 :
    ThetaLowerSegment 7822485760 7822518528 (782095000957999 / 100000)
      (782098304094249 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822485760 33 20 (91121 / 4000) (569507 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822485760 7822518528 88444 _ _ (91121 / 4000) (1781339 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822485760 7822518528 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822518528 :
    ThetaLowerSegment 7822518528 7822551296 (782098304094249 / 100000)
      (782101591285767 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822518528 33 20 (1139013 / 50000)
        (2278029 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822518528 7822551296 88445 _ _ (1139013 / 50000) (1781341 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822518528 7822551296 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822551296 :
    ThetaLowerSegment 7822551296 7822584064 (782101591285767 / 100000)
      (782104746351777 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822551296 33 20 (1139013 / 50000)
        (2278029 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822551296 7822584064 88445 _ _ (1139013 / 50000) (1781341 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822551296 7822584064 12 1385 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822584064 :
    ThetaLowerSegment 7822584064 7822616832 (782104746351777 / 100000)
      (391053984879991 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822584064 33 20 (2278027 / 100000)
        (227803 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822584064 7822616832 88445 _ _ (2278027 / 100000) (1781343 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822584064 7822616832 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822616832 :
    ThetaLowerSegment 7822616832 7822649600 (391053984879991 / 50000)
      (782111329849807 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822616832 33 20 (2278027 / 100000)
        (227803 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822616832 7822649600 88445 _ _ (2278027 / 100000) (1781343 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822616832 7822649600 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822649600 :
    ThetaLowerSegment 7822649600 7822682368 (782111329849807 / 100000)
      (391057310799411 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822649600 33 20 (2278027 / 100000)
        (227803 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822649600 7822682368 88445 _ _ (2278027 / 100000) (1781343 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822649600 7822682368 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822682368 :
    ThetaLowerSegment 7822682368 7822715136 (391057310799411 / 50000) (78211780172591 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822682368 33 20 (569507 / 25000)
        (2278031 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822682368 7822715136 88445 _ _ (569507 / 25000) (55667 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822682368 7822715136 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822715136 :
    ThetaLowerSegment 7822715136 7822747904 (78211780172591 / 10000) (391060582047619 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822715136 33 20 (569507 / 25000)
        (2278031 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822715136 7822747904 88446 _ _ (569507 / 25000) (55667 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822715136 7822747904 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822747904 :
    ThetaLowerSegment 7822747904 7822780672 (391060582047619 / 50000)
      (782124515075897 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822747904 33 20 (2278029 / 100000)
        (142377 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822747904 7822780672 88446 _ _ (2278029 / 100000) (890673 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822747904 7822780672 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822780672 :
    ThetaLowerSegment 7822780672 7822813440 (782124515075897 / 100000)
      (782127827330063 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822780672 33 20 (2278029 / 100000)
        (142377 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822780672 7822813440 88446 _ _ (2278029 / 100000) (890673 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822780672 7822813440 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822813440 :
    ThetaLowerSegment 7822813440 7822846208 (782127827330063 / 100000)
      (782131071244783 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822813440 33 20 (227803 / 10000)
        (2278033 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822813440 7822846208 88446 _ _ (227803 / 10000) (1781347 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822813440 7822846208 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822846208 :
    ThetaLowerSegment 7822846208 7822878976 (782131071244783 / 100000)
      (782134422226913 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822846208 33 20 (227803 / 10000)
        (2278033 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822846208 7822878976 88446 _ _ (227803 / 10000) (1781347 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822846208 7822878976 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822878976 :
    ThetaLowerSegment 7822878976 7822911744 (782134422226913 / 100000)
      (782137695756023 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822878976 33 20 (227803 / 10000)
        (2278033 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822878976 7822911744 88447 _ _ (227803 / 10000) (1781347 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822878976 7822911744 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822911744 :
    ThetaLowerSegment 7822911744 7822944512 (782137695756023 / 100000) (48883814282211 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822911744 33 20 (2278031 / 100000)
        (1139017 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822911744 7822944512 88447 _ _ (2278031 / 100000) (1781349 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822911744 7822944512 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822944512 :
    ThetaLowerSegment 7822944512 7822977280 (48883814282211 / 6250) (391072179498349 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822944512 33 20 (2278031 / 100000)
        (1139017 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822944512 7822977280 88447 _ _ (2278031 / 100000) (1781349 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822944512 7822977280 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7822977280 :
    ThetaLowerSegment 7822977280 7823010048 (391072179498349 / 50000) (78214752773921 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7822977280 33 20 (142377 / 6250)
        (455607 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7822977280 7823010048 88447 _ _ (142377 / 6250) (1781351 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7822977280 7823010048 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823010048 :
    ThetaLowerSegment 7823010048 7823042816 (78214752773921 / 10000) (391075419998869 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823010048 33 20 (142377 / 6250)
        (455607 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823010048 7823042816 88447 _ _ (142377 / 6250) (1781351 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823010048 7823042816 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823042816 :
    ThetaLowerSegment 7823042816 7823075584 (391075419998869 / 50000)
      (391077064737973 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823042816 33 20 (142377 / 6250)
        (455607 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823042816 7823075584 88447 _ _ (142377 / 6250) (1781351 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823042816 7823075584 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823075584 :
    ThetaLowerSegment 7823075584 7823108352 (391077064737973 / 50000)
      (195539344487751 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823075584 33 20 (2278033 / 100000)
        (569509 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823075584 7823108352 88448 _ _ (2278033 / 100000) (222669 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823075584 7823108352 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823108352 :
    ThetaLowerSegment 7823108352 7823141120 (195539344487751 / 25000)
      (782160706157217 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823108352 33 20 (2278033 / 100000)
        (569509 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823108352 7823141120 88448 _ _ (2278033 / 100000) (222669 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823108352 7823141120 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823141120 :
    ThetaLowerSegment 7823141120 7823173888 (782160706157217 / 100000)
      (782163890848749 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823141120 33 20 (1139017 / 50000)
        (2278037 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823141120 7823173888 88448 _ _ (1139017 / 50000) (890677 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823141120 7823173888 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823173888 :
    ThetaLowerSegment 7823173888 7823206656 (782163890848749 / 100000)
      (782167212222321 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823173888 33 20 (1139017 / 50000)
        (2278037 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823173888 7823206656 88448 _ _ (1139017 / 50000) (890677 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823173888 7823206656 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823206656 :
    ThetaLowerSegment 7823206656 7823239424 (782167212222321 / 100000) (48885656498931 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823206656 33 20 (455607 / 20000)
        (1139019 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823206656 7823239424 88448 _ _ (455607 / 20000) (445339 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823206656 7823239424 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823239424 :
    ThetaLowerSegment 7823239424 7823272192 (48885656498931 / 6250) (391086921791103 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823239424 33 20 (455607 / 20000)
        (1139019 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823239424 7823272192 88449 _ _ (455607 / 20000) (445339 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823239424 7823272192 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823272192 :
    ThetaLowerSegment 7823272192 7823304960 (391086921791103 / 50000)
      (391088580200583 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823272192 33 20 (455607 / 20000)
        (1139019 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823272192 7823304960 88449 _ _ (455607 / 20000) (445339 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823272192 7823304960 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823304960 :
    ThetaLowerSegment 7823304960 7823337728 (391088580200583 / 50000)
      (391090227220611 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823304960 33 20 (569509 / 25000)
        (2278039 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823304960 7823337728 88449 _ _ (569509 / 25000) (1781357 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823304960 7823337728 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823337728 :
    ThetaLowerSegment 7823337728 7823370496 (391090227220611 / 50000)
      (391091867406531 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823337728 33 20 (569509 / 25000)
        (2278039 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823337728 7823370496 88449 _ _ (569509 / 25000) (1781357 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823337728 7823370496 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823370496 :
    ThetaLowerSegment 7823370496 7823403264 (391091867406531 / 50000) (4888668189979 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823370496 33 20 (2278037 / 100000)
        (56951 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823370496 7823403264 88449 _ _ (2278037 / 100000) (1781359 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823370496 7823403264 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823403264 :
    ThetaLowerSegment 7823403264 7823436032 (4888668189979 / 625) (156438040432021 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823403264 33 20 (2278037 / 100000)
        (56951 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823403264 7823436032 88450 _ _ (2278037 / 100000) (1781359 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823403264 7823436032 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823436032 :
    ThetaLowerSegment 7823436032 7823468800 (156438040432021 / 20000) (97774190727011 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823436032 33 20 (2278037 / 100000)
        (56951 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823436032 7823468800 88450 _ _ (2278037 / 100000) (1781359 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823436032 7823468800 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823468800 :
    ThetaLowerSegment 7823468800 7823501568 (97774190727011 / 12500) (391098427014803 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823468800 33 20 (1139019 / 50000)
        (2278041 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823468800 7823501568 88450 _ _ (1139019 / 50000) (1781361 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823468800 7823501568 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823501568 :
    ThetaLowerSegment 7823501568 7823534336 (391098427014803 / 50000)
      (391100037587669 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823501568 33 20 (1139019 / 50000)
        (2278041 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823501568 7823534336 88450 _ _ (1139019 / 50000) (1781361 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823501568 7823534336 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823534336 :
    ThetaLowerSegment 7823534336 7823567104 (391100037587669 / 50000)
      (156440681589279 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823534336 33 20 (2278039 / 100000)
        (1139021 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823534336 7823567104 88450 _ _ (2278039 / 100000) (890681 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823534336 7823567104 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823567104 :
    ThetaLowerSegment 7823567104 7823599872 (156440681589279 / 20000)
      (782206770331959 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823567104 33 20 (2278039 / 100000)
        (1139021 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823567104 7823599872 88450 _ _ (2278039 / 100000) (890681 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823567104 7823599872 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823599872 :
    ThetaLowerSegment 7823599872 7823632640 (782206770331959 / 100000)
      (782210130440959 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823599872 33 20 (56951 / 2500)
        (2278043 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823599872 7823632640 88451 _ _ (56951 / 2500) (445341 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823599872 7823632640 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823632640 :
    ThetaLowerSegment 7823632640 7823665408 (782210130440959 / 100000)
      (782213444989159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823632640 33 20 (56951 / 2500)
        (2278043 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823632640 7823665408 88451 _ _ (56951 / 2500) (445341 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823632640 7823665408 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823665408 :
    ThetaLowerSegment 7823665408 7823698176 (782213444989159 / 100000)
      (782216764093439 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823665408 33 20 (56951 / 2500)
        (2278043 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823665408 7823698176 88451 _ _ (56951 / 2500) (445341 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823665408 7823698176 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823698176 :
    ThetaLowerSegment 7823698176 7823730944 (782216764093439 / 100000)
      (782220090033299 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823698176 33 20 (2278041 / 100000)
        (569511 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823698176 7823730944 88451 _ _ (2278041 / 100000) (890683 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823698176 7823730944 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823730944 :
    ThetaLowerSegment 7823730944 7823763712 (782220090033299 / 100000)
      (782223365856257 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823730944 33 20 (2278041 / 100000)
        (569511 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823730944 7823763712 88451 _ _ (2278041 / 100000) (890683 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823730944 7823763712 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823763712 :
    ThetaLowerSegment 7823763712 7823796480 (782223365856257 / 100000)
      (782226728246249 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823763712 33 20 (1139021 / 50000)
        (455609 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823763712 7823796480 88452 _ _ (1139021 / 50000) (1781367 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823763712 7823796480 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823796480 :
    ThetaLowerSegment 7823796480 7823829248 (782226728246249 / 100000)
      (782230088358199 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823796480 33 20 (1139021 / 50000)
        (455609 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823796480 7823829248 88452 _ _ (1139021 / 50000) (1781367 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823796480 7823829248 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823829248 :
    ThetaLowerSegment 7823829248 7823862016 (782230088358199 / 100000)
      (782233434801897 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823829248 33 20 (1139021 / 50000)
        (455609 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823829248 7823862016 88452 _ _ (1139021 / 50000) (1781367 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823829248 7823862016 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823862016 :
    ThetaLowerSegment 7823862016 7823894784 (782233434801897 / 100000)
      (391118397457661 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823862016 33 20 (2278043 / 100000)
        (1139023 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823862016 7823894784 88452 _ _ (2278043 / 100000) (1781369 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823862016 7823894784 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823894784 :
    ThetaLowerSegment 7823894784 7823927552 (391118397457661 / 50000)
      (391120019424277 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823894784 33 20 (2278043 / 100000)
        (1139023 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823894784 7823927552 88452 _ _ (2278043 / 100000) (1781369 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823894784 7823927552 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823927552 :
    ThetaLowerSegment 7823927552 7823960320 (391120019424277 / 50000)
      (391121620889209 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823927552 33 20 (569511 / 25000)
        (2278047 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823927552 7823960320 88452 _ _ (569511 / 25000) (1781371 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823927552 7823960320 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823960320 :
    ThetaLowerSegment 7823960320 7823993088 (391121620889209 / 50000)
      (391123242856537 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823960320 33 20 (569511 / 25000)
        (2278047 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823960320 7823993088 88453 _ _ (569511 / 25000) (1781371 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823960320 7823993088 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7823993088 :
    ThetaLowerSegment 7823993088 7824025856 (391123242856537 / 50000)
      (391124860268487 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7823993088 33 20 (455609 / 20000) (71189 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7823993088 7824025856 88453 _ _ (455609 / 20000) (445343 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7823993088 7824025856 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824025856 :
    ThetaLowerSegment 7824025856 7824058624 (391124860268487 / 50000)
      (782252825512309 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824025856 33 20 (455609 / 20000) (71189 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824025856 7824058624 88453 _ _ (455609 / 20000) (445343 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824025856 7824058624 12 1363 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824058624 :
    ThetaLowerSegment 7824058624 7824091392 (782252825512309 / 100000)
      (782256014775309 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824058624 33 20 (455609 / 20000) (71189 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824058624 7824091392 88453 _ _ (455609 / 20000) (445343 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824058624 7824091392 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824091392 :
    ThetaLowerSegment 7824091392 7824124160 (782256014775309 / 100000)
      (782259288327411 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824091392 33 20 (1139023 / 50000)
        (2278049 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824091392 7824124160 88453 _ _ (1139023 / 50000) (890687 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824091392 7824124160 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824124160 :
    ThetaLowerSegment 7824124160 7824156928 (782259288327411 / 100000)
      (782262630220893 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824124160 33 20 (1139023 / 50000)
        (2278049 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824124160 7824156928 88454 _ _ (1139023 / 50000) (890687 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824124160 7824156928 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824156928 :
    ThetaLowerSegment 7824156928 7824189696 (782262630220893 / 100000)
      (195566482777749 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824156928 33 20 (2278047 / 100000)
        (45561 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824156928 7824189696 88454 _ _ (2278047 / 100000) (55668 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824156928 7824189696 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824189696 :
    ThetaLowerSegment 7824189696 7824222464 (195566482777749 / 25000)
      (195567270982011 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824189696 33 20 (2278047 / 100000)
        (45561 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824189696 7824222464 88454 _ _ (2278047 / 100000) (55668 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824189696 7824222464 12 1384 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824222464 :
    ThetaLowerSegment 7824222464 7824255232 (195567270982011 / 25000)
      (195568082536611 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824222464 33 20 (71189 / 3125)
        (2278051 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824222464 7824255232 88454 _ _ (71189 / 3125) (1781377 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824222464 7824255232 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824255232 :
    ThetaLowerSegment 7824255232 7824288000 (195568082536611 / 25000) (39113779615559 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824255232 33 20 (71189 / 3125)
        (2278051 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824255232 7824288000 88454 _ _ (71189 / 3125) (1781377 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824255232 7824288000 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824288000 :
    ThetaLowerSegment 7824288000 7824320768 (39113779615559 / 5000) (195569714758003 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824288000 33 20 (71189 / 3125)
        (2278051 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824288000 7824320768 88455 _ _ (71189 / 3125) (1781377 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824288000 7824320768 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824320768 :
    ThetaLowerSegment 7824320768 7824353536 (195569714758003 / 25000)
      (156456417405489 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824320768 33 20 (2278049 / 100000)
        (569513 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824320768 7824353536 88455 _ _ (2278049 / 100000) (1781379 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824320768 7824353536 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824353536 :
    ThetaLowerSegment 7824353536 7824386304 (156456417405489 / 20000)
      (195571341284989 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824353536 33 20 (2278049 / 100000)
        (569513 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824353536 7824386304 88455 _ _ (2278049 / 100000) (1781379 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824353536 7824386304 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824386304 :
    ThetaLowerSegment 7824386304 7824419072 (195571341284989 / 25000)
      (195572156826889 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824386304 33 20 (45561 / 2000)
        (2278053 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824386304 7824419072 88455 _ _ (45561 / 2000) (89069 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824386304 7824419072 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824419072 :
    ThetaLowerSegment 7824419072 7824451840 (195572156826889 / 25000)
      (391145939042453 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824419072 33 20 (45561 / 2000)
        (2278053 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824419072 7824451840 88455 _ _ (45561 / 2000) (89069 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824419072 7824451840 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824451840 :
    ThetaLowerSegment 7824451840 7824484608 (391145939042453 / 50000)
      (195573785632639 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824451840 33 20 (45561 / 2000)
        (2278053 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824451840 7824484608 88455 _ _ (45561 / 2000) (89069 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824451840 7824484608 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824484608 :
    ThetaLowerSegment 7824484608 7824517376 (195573785632639 / 25000)
      (391149222852253 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824484608 33 20 (2278051 / 100000)
        (1139027 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824484608 7824517376 88456 _ _ (2278051 / 100000) (890691 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824484608 7824517376 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824517376 :
    ThetaLowerSegment 7824517376 7824550144 (391149222852253 / 50000)
      (195575444053767 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824517376 33 20 (2278051 / 100000)
        (1139027 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824517376 7824550144 88456 _ _ (2278051 / 100000) (890691 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824517376 7824550144 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824550144 :
    ThetaLowerSegment 7824550144 7824582912 (195575444053767 / 25000)
      (195576272125669 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824550144 33 20 (569513 / 25000)
        (455611 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824550144 7824582912 88456 _ _ (569513 / 25000) (222673 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824550144 7824582912 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824582912 :
    ThetaLowerSegment 7824582912 7824615680 (195576272125669 / 25000) (97788535006691 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824582912 33 20 (569513 / 25000)
        (455611 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824582912 7824615680 88456 _ _ (569513 / 25000) (222673 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824582912 7824615680 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824615680 :
    ThetaLowerSegment 7824615680 7824648448 (97788535006691 / 12500) (48894471389089 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824615680 33 20 (2278053 / 100000)
        (284757 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824615680 7824648448 88456 _ _ (2278053 / 100000) (356277 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824615680 7824648448 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824648448 :
    ThetaLowerSegment 7824648448 7824681216 (48894471389089 / 6250) (782314916021917 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824648448 33 20 (2278053 / 100000)
        (284757 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824648448 7824681216 88457 _ _ (2278053 / 100000) (356277 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824648448 7824681216 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824681216 :
    ThetaLowerSegment 7824681216 7824713984 (782314916021917 / 100000)
      (782318219198767 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824681216 33 20 (2278053 / 100000)
        (284757 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824681216 7824713984 88457 _ _ (2278053 / 100000) (356277 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824681216 7824713984 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824713984 :
    ThetaLowerSegment 7824713984 7824746752 (782318219198767 / 100000)
      (782321442645177 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824713984 33 20 (1139027 / 50000)
        (2278057 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824713984 7824746752 88457 _ _ (1139027 / 50000) (1781387 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824713984 7824746752 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824746752 :
    ThetaLowerSegment 7824746752 7824779520 (782321442645177 / 100000)
      (782324675203803 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824746752 33 20 (1139027 / 50000)
        (2278057 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824746752 7824779520 88457 _ _ (1139027 / 50000) (1781387 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824746752 7824779520 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824779520 :
    ThetaLowerSegment 7824779520 7824812288 (782324675203803 / 100000)
      (782327919154123 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824779520 33 20 (455611 / 20000)
        (1139029 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824779520 7824812288 88457 _ _ (455611 / 20000) (1781389 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824779520 7824812288 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824812288 :
    ThetaLowerSegment 7824812288 7824845056 (782327919154123 / 100000)
      (782331181328883 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824812288 33 20 (455611 / 20000)
        (1139029 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824812288 7824845056 88457 _ _ (455611 / 20000) (1781389 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824812288 7824845056 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824845056 :
    ThetaLowerSegment 7824845056 7824877824 (782331181328883 / 100000)
      (195583619418617 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824845056 33 20 (455611 / 20000)
        (1139029 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824845056 7824877824 88458 _ _ (455611 / 20000) (1781389 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824845056 7824877824 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824877824 :
    ThetaLowerSegment 7824877824 7824910592 (195583619418617 / 25000)
      (195584438379749 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824877824 33 20 (284757 / 12500)
        (2278059 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824877824 7824910592 88458 _ _ (284757 / 12500) (178139 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824877824 7824910592 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824910592 :
    ThetaLowerSegment 7824910592 7824943360 (195584438379749 / 25000)
      (195585264744563 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824910592 33 20 (284757 / 12500)
        (2278059 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824910592 7824943360 88458 _ _ (284757 / 12500) (178139 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824910592 7824943360 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824943360 :
    ThetaLowerSegment 7824943360 7824976128 (195585264744563 / 25000) (78234432571199 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824943360 33 20 (2278057 / 100000)
        (113903 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824943360 7824976128 88458 _ _ (2278057 / 100000) (111337 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824943360 7824976128 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7824976128 :
    ThetaLowerSegment 7824976128 7825008896 (78234432571199 / 10000) (391173793944807 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7824976128 33 20 (2278057 / 100000)
        (113903 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7824976128 7825008896 88458 _ _ (2278057 / 100000) (111337 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7824976128 7825008896 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825008896 :
    ThetaLowerSegment 7825008896 7825041664 (391173793944807 / 50000)
      (391175406809871 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825008896 33 20 (1139029 / 50000)
        (2278061 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825008896 7825041664 88459 _ _ (1139029 / 50000) (890697 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825008896 7825041664 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825041664 :
    ThetaLowerSegment 7825041664 7825074432 (391175406809871 / 50000) (48897138422521 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825041664 33 20 (1139029 / 50000)
        (2278061 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825041664 7825074432 88459 _ _ (1139029 / 50000) (890697 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825041664 7825074432 12 1493 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825074432 :
    ThetaLowerSegment 7825074432 7825107200 (48897138422521 / 6250) (391178723662319 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825074432 33 20 (1139029 / 50000)
        (2278061 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825074432 7825107200 88459 _ _ (1139029 / 50000) (890697 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825074432 7825107200 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825107200 :
    ThetaLowerSegment 7825107200 7825139968 (391178723662319 / 50000)
      (782360661665887 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825107200 33 20 (2278059 / 100000)
        (1139031 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825107200 7825139968 88459 _ _ (2278059 / 100000) (356279 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825107200 7825139968 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825139968 :
    ThetaLowerSegment 7825139968 7825172736 (782360661665887 / 100000)
      (391182022291751 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825139968 33 20 (2278059 / 100000)
        (1139031 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825139968 7825172736 88459 _ _ (2278059 / 100000) (356279 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825139968 7825172736 12 1485 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825172736 :
    ThetaLowerSegment 7825172736 7825205504 (391182022291751 / 50000)
      (391183656799801 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825172736 33 20 (113903 / 5000)
        (2278063 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825172736 7825205504 88460 _ _ (113903 / 5000) (1781397 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825172736 7825205504 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825205504 :
    ThetaLowerSegment 7825205504 7825238272 (391183656799801 / 50000)
      (391185379013161 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825205504 33 20 (113903 / 5000)
        (2278063 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825205504 7825238272 88460 _ _ (113903 / 5000) (1781397 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825205504 7825238272 12 1512 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825238272 :
    ThetaLowerSegment 7825238272 7825271040 (391185379013161 / 50000)
      (156474809053669 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825238272 33 20 (2278061 / 100000)
        (142379 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825238272 7825271040 88460 _ _ (2278061 / 100000) (1781399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825238272 7825271040 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825271040 :
    ThetaLowerSegment 7825271040 7825303808 (156474809053669 / 20000)
      (391188627528147 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825271040 33 20 (2278061 / 100000)
        (142379 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825271040 7825303808 88460 _ _ (2278061 / 100000) (1781399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825271040 7825303808 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825303808 :
    ThetaLowerSegment 7825303808 7825336576 (391188627528147 / 50000)
      (391190295068799 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825303808 33 20 (2278061 / 100000)
        (142379 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825303808 7825336576 88460 _ _ (2278061 / 100000) (1781399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825303808 7825336576 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825336576 :
    ThetaLowerSegment 7825336576 7825369344 (391190295068799 / 50000) (78238379309277 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825336576 33 20 (1139031 / 50000)
        (455613 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825336576 7825369344 88460 _ _ (1139031 / 50000) (8907 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825336576 7825369344 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825369344 :
    ThetaLowerSegment 7825369344 7825402112 (78238379309277 / 10000) (195596779196307 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825369344 33 20 (1139031 / 50000)
        (455613 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825369344 7825402112 88461 _ _ (1139031 / 50000) (8907 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825369344 7825402112 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825402112 :
    ThetaLowerSegment 7825402112 7825434880 (195596779196307 / 25000) (9779878939821 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825402112 33 20 (2278063 / 100000)
        (1139033 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825402112 7825434880 88461 _ _ (2278063 / 100000) (890701 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825402112 7825434880 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825434880 :
    ThetaLowerSegment 7825434880 7825467648 (9779878939821 / 1250) (391196813744641 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825434880 33 20 (2278063 / 100000)
        (1139033 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825434880 7825467648 88461 _ _ (2278063 / 100000) (890701 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825434880 7825467648 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825467648 :
    ThetaLowerSegment 7825467648 7825500416 (391196813744641 / 50000)
      (782396896509687 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825467648 33 20 (2278063 / 100000)
        (1139033 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825467648 7825500416 88461 _ _ (2278063 / 100000) (890701 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825467648 7825500416 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825500416 :
    ThetaLowerSegment 7825500416 7825533184 (782396896509687 / 100000)
      (782400163253463 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825500416 33 20 (142379 / 6250)
        (2278067 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825500416 7825533184 88461 _ _ (142379 / 6250) (445351 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825500416 7825533184 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825533184 :
    ThetaLowerSegment 7825533184 7825565952 (782400163253463 / 100000)
      (782403475558519 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825533184 33 20 (142379 / 6250)
        (2278067 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825533184 7825565952 88462 _ _ (142379 / 6250) (445351 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825533184 7825565952 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825565952 :
    ThetaLowerSegment 7825565952 7825598720 (782403475558519 / 100000)
      (782406755972119 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825565952 33 20 (455613 / 20000)
        (569517 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825565952 7825598720 88462 _ _ (455613 / 20000) (356281 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825565952 7825598720 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825598720 :
    ThetaLowerSegment 7825598720 7825631488 (782406755972119 / 100000)
      (195602516500141 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825598720 33 20 (455613 / 20000)
        (569517 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825598720 7825631488 88462 _ _ (455613 / 20000) (356281 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825598720 7825631488 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825631488 :
    ThetaLowerSegment 7825631488 7825664256 (195602516500141 / 25000) (48900842978481 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825631488 33 20 (1139033 / 50000)
        (2278069 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825631488 7825664256 88462 _ _ (1139033 / 50000) (1781407 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825631488 7825664256 12 1502 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825664256 :
    ThetaLowerSegment 7825664256 7825697024 (48900842978481 / 6250) (48901050282487 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825664256 33 20 (1139033 / 50000)
        (2278069 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825664256 7825697024 88462 _ _ (1139033 / 50000) (1781407 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825664256 7825697024 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825697024 :
    ThetaLowerSegment 7825697024 7825729792 (48901050282487 / 6250) (39121001740869 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825697024 33 20 (1139033 / 50000)
        (2278069 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825697024 7825729792 88462 _ _ (1139033 / 50000) (1781407 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825697024 7825729792 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825729792 :
    ThetaLowerSegment 7825729792 7825762560 (39121001740869 / 5000) (782423358517133 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825729792 33 20 (2278067 / 100000)
        (227807 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825729792 7825762560 88463 _ _ (2278067 / 100000) (1781409 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825729792 7825762560 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825762560 :
    ThetaLowerSegment 7825762560 7825795328 (782423358517133 / 100000)
      (78242661843101 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825762560 33 20 (2278067 / 100000)
        (227807 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825762560 7825795328 88463 _ _ (2278067 / 100000) (1781409 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825762560 7825795328 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825795328 :
    ThetaLowerSegment 7825795328 7825828096 (78242661843101 / 10000) (391214944868329 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825795328 33 20 (569517 / 25000)
        (2278071 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825795328 7825828096 88463 _ _ (569517 / 25000) (178141 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825795328 7825828096 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825828096 :
    ThetaLowerSegment 7825828096 7825860864 (391214944868329 / 50000) (78243313370549 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825828096 33 20 (569517 / 25000)
        (2278071 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825828096 7825860864 88463 _ _ (569517 / 25000) (178141 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825828096 7825860864 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825860864 :
    ThetaLowerSegment 7825860864 7825893632 (78243313370549 / 10000) (391218210478807 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825860864 33 20 (569517 / 25000)
        (2278071 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825860864 7825893632 88463 _ _ (569517 / 25000) (178141 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825860864 7825893632 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825893632 :
    ThetaLowerSegment 7825893632 7825926400 (391218210478807 / 50000) (48902475925647 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825893632 33 20 (2278069 / 100000)
        (284759 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825893632 7825926400 88464 _ _ (2278069 / 100000) (445353 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825893632 7825926400 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825926400 :
    ThetaLowerSegment 7825926400 7825959168 (48902475925647 / 6250) (195610703304807 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825926400 33 20 (2278069 / 100000)
        (284759 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825926400 7825959168 88464 _ _ (2278069 / 100000) (445353 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825926400 7825959168 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825959168 :
    ThetaLowerSegment 7825959168 7825991936 (195610703304807 / 25000)
      (391223073017819 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825959168 33 20 (227807 / 10000)
        (2278073 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825959168 7825991936 88464 _ _ (227807 / 10000) (1781413 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825959168 7825991936 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7825991936 :
    ThetaLowerSegment 7825991936 7826024704 (391223073017819 / 50000)
      (391224724618569 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7825991936 33 20 (227807 / 10000)
        (2278073 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7825991936 7826024704 88464 _ _ (227807 / 10000) (1781413 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7825991936 7826024704 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826024704 :
    ThetaLowerSegment 7826024704 7826057472 (391224724618569 / 50000)
      (195613204056519 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826024704 33 20 (2278071 / 100000)
        (1139037 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826024704 7826057472 88464 _ _ (2278071 / 100000) (356283 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826024704 7826057472 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826057472 :
    ThetaLowerSegment 7826057472 7826090240 (195613204056519 / 25000)
      (391228096163649 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826057472 33 20 (2278071 / 100000)
        (1139037 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826057472 7826090240 88465 _ _ (2278071 / 100000) (356283 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826057472 7826090240 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826090240 :
    ThetaLowerSegment 7826090240 7826123008 (391228096163649 / 50000) (78245945452497 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826090240 33 20 (2278071 / 100000)
        (1139037 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826090240 7826123008 88465 _ _ (2278071 / 100000) (356283 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826090240 7826123008 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826123008 :
    ThetaLowerSegment 7826123008 7826155776 (78245945452497 / 10000) (391231340137461 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826123008 33 20 (284759 / 12500) (91123 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826123008 7826155776 88465 _ _ (284759 / 12500) (1781417 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826123008 7826155776 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826155776 :
    ThetaLowerSegment 7826155776 7826188544 (391231340137461 / 50000)
      (391233012242309 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826155776 33 20 (284759 / 12500) (91123 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826155776 7826188544 88465 _ _ (284759 / 12500) (1781417 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826155776 7826188544 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826188544 :
    ThetaLowerSegment 7826188544 7826221312 (391233012242309 / 50000)
      (782469216064891 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826188544 33 20 (2278073 / 100000)
        (569519 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826188544 7826221312 88465 _ _ (2278073 / 100000) (890709 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826188544 7826221312 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826221312 :
    ThetaLowerSegment 7826221312 7826254080 (782469216064891 / 100000)
      (782472569388347 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826221312 33 20 (2278073 / 100000)
        (569519 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826221312 7826254080 88465 _ _ (2278073 / 100000) (890709 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826221312 7826254080 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826254080 :
    ThetaLowerSegment 7826254080 7826286848 (782472569388347 / 100000)
      (156495177252527 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826254080 33 20 (2278073 / 100000)
        (569519 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826254080 7826286848 88466 _ _ (2278073 / 100000) (890709 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826254080 7826286848 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826286848 :
    ThetaLowerSegment 7826286848 7826319616 (156495177252527 / 20000)
      (782479082400457 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826286848 33 20 (1139037 / 50000)
        (2278077 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826286848 7826319616 88466 _ _ (1139037 / 50000) (89071 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826286848 7826319616 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826319616 :
    ThetaLowerSegment 7826319616 7826352384 (782479082400457 / 100000)
      (156496462086263 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826319616 33 20 (1139037 / 50000)
        (2278077 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826319616 7826352384 88466 _ _ (1139037 / 50000) (89071 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826319616 7826352384 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826352384 :
    ThetaLowerSegment 7826352384 7826385152 (156496462086263 / 20000)
      (156497096302343 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826352384 33 20 (91123 / 4000)
        (1139039 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826352384 7826385152 88466 _ _ (91123 / 4000) (890711 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826352384 7826385152 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826385152 :
    ThetaLowerSegment 7826385152 7826417920 (156497096302343 / 20000) (78248873688089 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826385152 33 20 (91123 / 4000)
        (1139039 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826385152 7826417920 88466 _ _ (91123 / 4000) (890711 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826385152 7826417920 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826417920 :
    ThetaLowerSegment 7826417920 7826450688 (78248873688089 / 10000) (78249196035843 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826417920 33 20 (569519 / 25000)
        (2278079 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826417920 7826450688 88467 _ _ (569519 / 25000) (1781423 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826417920 7826450688 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826450688 :
    ThetaLowerSegment 7826450688 7826483456 (78249196035843 / 10000) (391247679623911 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826450688 33 20 (569519 / 25000)
        (2278079 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826450688 7826483456 88467 _ _ (569519 / 25000) (1781423 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826450688 7826483456 12 1492 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826483456 :
    ThetaLowerSegment 7826483456 7826516224 (391247679623911 / 50000)
      (391249291362681 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826483456 33 20 (569519 / 25000)
        (2278079 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826483456 7826516224 88467 _ _ (569519 / 25000) (1781423 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826483456 7826516224 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826516224 :
    ThetaLowerSegment 7826516224 7826548992 (391249291362681 / 50000) (97812745993473 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826516224 33 20 (2278077 / 100000)
        (14238 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826516224 7826548992 88467 _ _ (2278077 / 100000) (71257 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826516224 7826548992 12 1486 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826548992 :
    ThetaLowerSegment 7826548992 7826581760 (97812745993473 / 12500) (78250524382251 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826548992 33 20 (2278077 / 100000)
        (14238 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826548992 7826581760 88467 _ _ (2278077 / 100000) (71257 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826548992 7826581760 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826581760 :
    ThetaLowerSegment 7826581760 7826614528 (78250524382251 / 10000) (78250843313171 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826581760 33 20 (1139039 / 50000)
        (2278081 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826581760 7826614528 88467 _ _ (1139039 / 50000) (1781427 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826581760 7826614528 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826614528 :
    ThetaLowerSegment 7826614528 7826647296 (78250843313171 / 10000) (391255818054689 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826614528 33 20 (1139039 / 50000)
        (2278081 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826614528 7826647296 88468 _ _ (1139039 / 50000) (1781427 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826614528 7826647296 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826647296 :
    ThetaLowerSegment 7826647296 7826680064 (391255818054689 / 50000)
      (195628723440587 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826647296 33 20 (2278079 / 100000)
        (1139041 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826647296 7826680064 88468 _ _ (2278079 / 100000) (445357 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826647296 7826680064 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826680064 :
    ThetaLowerSegment 7826680064 7826712832 (195628723440587 / 25000)
      (156503640762227 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826680064 33 20 (2278079 / 100000)
        (1139041 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826680064 7826712832 88468 _ _ (2278079 / 100000) (445357 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826680064 7826712832 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826712832 :
    ThetaLowerSegment 7826712832 7826745600 (156503640762227 / 20000)
      (391260797935383 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826712832 33 20 (2278079 / 100000)
        (1139041 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826712832 7826745600 88468 _ _ (2278079 / 100000) (445357 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826712832 7826745600 12 1489 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826745600 :
    ThetaLowerSegment 7826745600 7826778368 (391260797935383 / 50000)
      (391262425623543 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826745600 33 20 (14238 / 625)
        (2278083 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826745600 7826778368 88468 _ _ (14238 / 625) (178143 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826745600 7826778368 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826778368 :
    ThetaLowerSegment 7826778368 7826811136 (391262425623543 / 50000)
      (391264018001463 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826778368 33 20 (14238 / 625)
        (2278083 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826778368 7826811136 88469 _ _ (14238 / 625) (178143 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826778368 7826811136 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826811136 :
    ThetaLowerSegment 7826811136 7826843904 (391264018001463 / 50000)
      (782531295936837 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826811136 33 20 (2278081 / 100000)
        (569521 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826811136 7826843904 88469 _ _ (2278081 / 100000) (222679 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826811136 7826843904 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826843904 :
    ThetaLowerSegment 7826843904 7826876672 (782531295936837 / 100000)
      (156506928031949 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826843904 33 20 (2278081 / 100000)
        (569521 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826843904 7826876672 88469 _ _ (2278081 / 100000) (222679 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826843904 7826876672 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826876672 :
    ThetaLowerSegment 7826876672 7826909440 (156506928031949 / 20000)
      (391268934100261 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826876672 33 20 (2278081 / 100000)
        (569521 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826876672 7826909440 88469 _ _ (2278081 / 100000) (222679 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826876672 7826909440 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826909440 :
    ThetaLowerSegment 7826909440 7826942208 (391268934100261 / 50000)
      (391270628993269 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826909440 33 20 (1139041 / 50000)
        (455617 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826909440 7826942208 88469 _ _ (1139041 / 50000) (1781433 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826909440 7826942208 12 1488 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826942208 :
    ThetaLowerSegment 7826942208 7826974976 (391270628993269 / 50000)
      (391272255543817 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826942208 33 20 (1139041 / 50000)
        (455617 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826942208 7826974976 88470 _ _ (1139041 / 50000) (1781433 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826942208 7826974976 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7826974976 :
    ThetaLowerSegment 7826974976 7827007744 (391272255543817 / 50000)
      (195636978635909 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7826974976 33 20 (2278083 / 100000)
        (1139043 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7826974976 7827007744 88470 _ _ (2278083 / 100000) (356287 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7826974976 7827007744 12 1494 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827007744 :
    ThetaLowerSegment 7827007744 7827040512 (195636978635909 / 25000) (24454722849901 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827007744 33 20 (2278083 / 100000)
        (1139043 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827007744 7827040512 88470 _ _ (2278083 / 100000) (356287 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827007744 7827040512 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827040512 :
    ThetaLowerSegment 7827040512 7827073280 (24454722849901 / 3125) (195638617147473 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827040512 33 20 (569521 / 25000)
        (2278087 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827040512 7827073280 88470 _ _ (569521 / 25000) (1781437 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827040512 7827073280 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827073280 :
    ThetaLowerSegment 7827073280 7827106048 (195638617147473 / 25000)
      (195639431562503 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827073280 33 20 (569521 / 25000)
        (2278087 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827073280 7827106048 88470 _ _ (569521 / 25000) (1781437 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827073280 7827106048 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827106048 :
    ThetaLowerSegment 7827106048 7827138816 (195639431562503 / 25000)
      (195640233448071 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827106048 33 20 (569521 / 25000)
        (2278087 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827106048 7827138816 88470 _ _ (569521 / 25000) (1781437 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827106048 7827138816 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827138816 :
    ThetaLowerSegment 7827138816 7827171584 (195640233448071 / 25000)
      (782564198288089 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827138816 33 20 (455617 / 20000)
        (284761 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827138816 7827171584 88471 _ _ (455617 / 20000) (890719 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827138816 7827171584 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827171584 :
    ThetaLowerSegment 7827171584 7827204352 (782564198288089 / 100000)
      (782567455949639 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827171584 33 20 (455617 / 20000)
        (284761 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827171584 7827204352 88471 _ _ (455617 / 20000) (890719 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827171584 7827204352 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827204352 :
    ThetaLowerSegment 7827204352 7827237120 (782567455949639 / 100000)
      (782570722724963 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827204352 33 20 (1139043 / 50000)
        (2278089 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827204352 7827237120 88471 _ _ (1139043 / 50000) (11134 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827204352 7827237120 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827237120 :
    ThetaLowerSegment 7827237120 7827269888 (782570722724963 / 100000)
      (782574060120953 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827237120 33 20 (1139043 / 50000)
        (2278089 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827237120 7827269888 88471 _ _ (1139043 / 50000) (11134 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827237120 7827269888 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827269888 :
    ThetaLowerSegment 7827269888 7827302656 (782574060120953 / 100000)
      (782577397516943 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827269888 33 20 (1139043 / 50000)
        (2278089 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827269888 7827302656 88471 _ _ (1139043 / 50000) (11134 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827269888 7827302656 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827302656 :
    ThetaLowerSegment 7827302656 7827335424 (782577397516943 / 100000)
      (782580591394917 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827302656 33 20 (2278087 / 100000)
        (227809 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827302656 7827335424 88472 _ _ (2278087 / 100000) (890721 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827302656 7827335424 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827335424 :
    ThetaLowerSegment 7827335424 7827368192 (782580591394917 / 100000)
      (782583794385239 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827335424 33 20 (2278087 / 100000)
        (227809 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827335424 7827368192 88472 _ _ (2278087 / 100000) (890721 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827335424 7827368192 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827368192 :
    ThetaLowerSegment 7827368192 7827400960 (782583794385239 / 100000)
      (782587038382551 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827368192 33 20 (284761 / 12500)
        (2278091 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827368192 7827400960 88472 _ _ (284761 / 12500) (1781443 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827368192 7827400960 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827400960 :
    ThetaLowerSegment 7827400960 7827433728 (782587038382551 / 100000)
      (782590432733671 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827400960 33 20 (284761 / 12500)
        (2278091 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827400960 7827433728 88472 _ _ (284761 / 12500) (1781443 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827400960 7827433728 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827433728 :
    ThetaLowerSegment 7827433728 7827466496 (782590432733671 / 100000)
      (391296809890091 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827433728 33 20 (2278089 / 100000)
        (569523 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827433728 7827466496 88472 _ _ (2278089 / 100000) (356289 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827433728 7827466496 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827466496 :
    ThetaLowerSegment 7827466496 7827499264 (391296809890091 / 50000)
      (391298477451239 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827466496 33 20 (2278089 / 100000)
        (569523 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827466496 7827499264 88472 _ _ (2278089 / 100000) (356289 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827466496 7827499264 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827499264 :
    ThetaLowerSegment 7827499264 7827532032 (391298477451239 / 50000)
      (782600255853439 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827499264 33 20 (2278089 / 100000)
        (569523 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827499264 7827532032 88473 _ _ (2278089 / 100000) (356289 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827499264 7827532032 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827532032 :
    ThetaLowerSegment 7827532032 7827564800 (782600255853439 / 100000)
      (782603611480009 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827532032 33 20 (227809 / 10000)
        (2278093 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827532032 7827564800 88473 _ _ (227809 / 10000) (1781447 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827532032 7827564800 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827564800 :
    ThetaLowerSegment 7827564800 7827597568 (782603611480009 / 100000)
      (782606839533539 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827564800 33 20 (227809 / 10000)
        (2278093 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827564800 7827597568 88473 _ _ (227809 / 10000) (1781447 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827564800 7827597568 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827597568 :
    ThetaLowerSegment 7827597568 7827630336 (782606839533539 / 100000)
      (782610119984579 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827597568 33 20 (2278091 / 100000)
        (1139047 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827597568 7827630336 88473 _ _ (2278091 / 100000) (222681 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827597568 7827630336 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827630336 :
    ThetaLowerSegment 7827630336 7827663104 (782610119984579 / 100000)
      (391306646682671 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827630336 33 20 (2278091 / 100000)
        (1139047 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827630336 7827663104 88473 _ _ (2278091 / 100000) (222681 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827630336 7827663104 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827663104 :
    ThetaLowerSegment 7827663104 7827695872 (391306646682671 / 50000)
      (391308245902553 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827663104 33 20 (2278091 / 100000)
        (1139047 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827663104 7827695872 88474 _ _ (2278091 / 100000) (222681 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827663104 7827695872 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827695872 :
    ThetaLowerSegment 7827695872 7827728640 (391308245902553 / 50000) (78261977681377 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827695872 33 20 (569523 / 25000)
        (455619 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827695872 7827728640 88474 _ _ (569523 / 25000) (35629 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827695872 7827728640 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827728640 :
    ThetaLowerSegment 7827728640 7827761408 (78261977681377 / 10000) (391311510408389 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827728640 33 20 (569523 / 25000)
        (455619 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827728640 7827761408 88474 _ _ (569523 / 25000) (35629 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827728640 7827761408 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827761408 :
    ThetaLowerSegment 7827761408 7827794176 (391311510408389 / 50000)
      (195656544563419 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827761408 33 20 (2278093 / 100000)
        (142381 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827761408 7827794176 88474 _ _ (2278093 / 100000) (1781451 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827761408 7827794176 12 1386 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827794176 :
    ThetaLowerSegment 7827794176 7827826944 (195656544563419 / 25000) (39131473846617 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827794176 33 20 (2278093 / 100000)
        (142381 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827794176 7827826944 88474 _ _ (2278093 / 100000) (1781451 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827794176 7827826944 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827826944 :
    ThetaLowerSegment 7827826944 7827859712 (39131473846617 / 5000) (39131640147479 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827826944 33 20 (1139047 / 50000)
        (2278097 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827826944 7827859712 88475 _ _ (1139047 / 50000) (1781453 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827826944 7827859712 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827859712 :
    ThetaLowerSegment 7827859712 7827892480 (39131640147479 / 5000) (97829506438953 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827859712 33 20 (1139047 / 50000)
        (2278097 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827859712 7827892480 88475 _ _ (1139047 / 50000) (1781453 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827859712 7827892480 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827892480 :
    ThetaLowerSegment 7827892480 7827925248 (97829506438953 / 12500) (195659836408887 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827892480 33 20 (1139047 / 50000)
        (2278097 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827892480 7827925248 88475 _ _ (1139047 / 50000) (1781453 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827892480 7827925248 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827925248 :
    ThetaLowerSegment 7827925248 7827958016 (195659836408887 / 25000)
      (782642664819963 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827925248 33 20 (455619 / 20000)
        (1139049 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827925248 7827958016 88475 _ _ (455619 / 20000) (356291 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827925248 7827958016 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827958016 :
    ThetaLowerSegment 7827958016 7827990784 (782642664819963 / 100000)
      (195661494862047 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827958016 33 20 (455619 / 20000)
        (1139049 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827958016 7827990784 88475 _ _ (455619 / 20000) (356291 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827958016 7827990784 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7827990784 :
    ThetaLowerSegment 7827990784 7828023552 (195661494862047 / 25000) (39132465501227 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7827990784 33 20 (142381 / 6250)
        (2278099 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7827990784 7828023552 88475 _ _ (142381 / 6250) (111341 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7827990784 7828023552 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828023552 :
    ThetaLowerSegment 7828023552 7828056320 (39132465501227 / 5000) (195663132243547 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828023552 33 20 (142381 / 6250)
        (2278099 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828023552 7828056320 88476 _ _ (142381 / 6250) (111341 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828023552 7828056320 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828056320 :
    ThetaLowerSegment 7828056320 7828089088 (195663132243547 / 25000)
      (782655820824353 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828056320 33 20 (2278097 / 100000)
        (22781 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828056320 7828089088 88476 _ _ (2278097 / 100000) (890729 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828056320 7828089088 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828089088 :
    ThetaLowerSegment 7828089088 7828121856 (782655820824353 / 100000)
      (391329560893453 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828089088 33 20 (2278097 / 100000)
        (22781 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828089088 7828121856 88476 _ _ (2278097 / 100000) (890729 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828089088 7828121856 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828121856 :
    ThetaLowerSegment 7828121856 7828154624 (391329560893453 / 50000)
      (195665615369277 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828121856 33 20 (2278097 / 100000)
        (22781 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828121856 7828154624 88476 _ _ (2278097 / 100000) (890729 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828121856 7828154624 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828154624 :
    ThetaLowerSegment 7828154624 7828187392 (195665615369277 / 25000) (78266578522209 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828154624 33 20 (1139049 / 50000)
        (2278101 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828154624 7828187392 88476 _ _ (1139049 / 50000) (89073 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828154624 7828187392 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828187392 :
    ThetaLowerSegment 7828187392 7828220160 (78266578522209 / 10000) (97833644316129 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828187392 33 20 (1139049 / 50000)
        (2278101 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828187392 7828220160 88477 _ _ (1139049 / 50000) (89073 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828187392 7828220160 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828220160 :
    ThetaLowerSegment 7828220160 7828252928 (97833644316129 / 12500)
      (782672414488701 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828220160 33 20 (2278099 / 100000)
        (1139051 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828220160 7828252928 88477 _ _ (2278099 / 100000) (1781461 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828220160 7828252928 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828252928 :
    ThetaLowerSegment 7828252928 7828285696 (782672414488701 / 100000)
      (156535141723971 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828252928 33 20 (2278099 / 100000)
        (1139051 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828252928 7828285696 88477 _ _ (2278099 / 100000) (1781461 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828252928 7828285696 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828285696 :
    ThetaLowerSegment 7828285696 7828318464 (156535141723971 / 20000) (97834865377193 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828285696 33 20 (2278099 / 100000)
        (1139051 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828285696 7828318464 88477 _ _ (2278099 / 100000) (1781461 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828285696 7828318464 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828318464 :
    ThetaLowerSegment 7828318464 7828351232 (97834865377193 / 12500) (97835275435193 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828318464 33 20 (22781 / 1000)
        (2278103 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828318464 7828351232 88477 _ _ (22781 / 1000) (1781463 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828318464 7828351232 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828351232 :
    ThetaLowerSegment 7828351232 7828384000 (97835275435193 / 12500) (97835700300843 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828351232 33 20 (22781 / 1000)
        (2278103 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828351232 7828384000 88477 _ _ (22781 / 1000) (1781463 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828351232 7828384000 12 1492 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828384000 :
    ThetaLowerSegment 7828384000 7828416768 (97835700300843 / 12500) (391344416376981 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828384000 33 20 (2278101 / 100000)
        (284763 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828384000 7828416768 88478 _ _ (2278101 / 100000) (356293 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828384000 7828416768 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828416768 :
    ThetaLowerSegment 7828416768 7828449536 (391344416376981 / 50000)
      (391346024716287 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828416768 33 20 (2278101 / 100000)
        (284763 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828416768 7828449536 88478 _ _ (2278101 / 100000) (356293 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828416768 7828449536 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828449536 :
    ThetaLowerSegment 7828449536 7828482304 (391346024716287 / 50000)
      (195673835322491 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828449536 33 20 (1139051 / 50000)
        (455621 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828449536 7828482304 88478 _ _ (1139051 / 50000) (890733 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828449536 7828482304 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828482304 :
    ThetaLowerSegment 7828482304 7828515072 (195673835322491 / 25000) (24459330648469 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828482304 33 20 (1139051 / 50000)
        (455621 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828482304 7828515072 88478 _ _ (1139051 / 50000) (890733 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828482304 7828515072 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828515072 :
    ThetaLowerSegment 7828515072 7828547840 (24459330648469 / 3125) (195675436828197 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828515072 33 20 (1139051 / 50000)
        (455621 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828515072 7828547840 88478 _ _ (1139051 / 50000) (890733 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828515072 7828547840 12 1390 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828547840 :
    ThetaLowerSegment 7828547840 7828580608 (195675436828197 / 25000) (78270510523661 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828547840 33 20 (2278103 / 100000)
        (1139053 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828547840 7828580608 88479 _ _ (2278103 / 100000) (445367 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828547840 7828580608 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828580608 :
    ThetaLowerSegment 7828580608 7828613376 (78270510523661 / 10000)
      (782708424432681 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828580608 33 20 (2278103 / 100000)
        (1139053 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828580608 7828613376 88479 _ _ (2278103 / 100000) (445367 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828580608 7828613376 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828613376 :
    ThetaLowerSegment 7828613376 7828646144 (782708424432681 / 100000)
      (782711643393633 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828613376 33 20 (284763 / 12500)
        (2278107 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828613376 7828646144 88479 _ _ (284763 / 12500) (178147 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828613376 7828646144 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828646144 :
    ThetaLowerSegment 7828646144 7828678912 (782711643393633 / 100000)
      (782714962591161 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828646144 33 20 (284763 / 12500)
        (2278107 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828646144 7828678912 88479 _ _ (284763 / 12500) (178147 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828646144 7828678912 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828678912 :
    ThetaLowerSegment 7828678912 7828711680 (782714962591161 / 100000)
      (782718190664529 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828678912 33 20 (284763 / 12500)
        (2278107 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828678912 7828711680 88479 _ _ (284763 / 12500) (178147 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828678912 7828711680 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828711680 :
    ThetaLowerSegment 7828711680 7828744448 (782718190664529 / 100000)
      (391360750375547 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828711680 33 20 (455621 / 20000)
        (569527 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828711680 7828744448 88480 _ _ (455621 / 20000) (1781471 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828711680 7828744448 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828744448 :
    ThetaLowerSegment 7828744448 7828777216 (391360750375547 / 50000)
      (195681203278941 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828744448 33 20 (455621 / 20000)
        (569527 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828744448 7828777216 88480 _ _ (455621 / 20000) (1781471 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828744448 7828777216 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828777216 :
    ThetaLowerSegment 7828777216 7828809984 (195681203278941 / 25000)
      (195682025675207 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828777216 33 20 (1139053 / 50000)
        (2278109 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828777216 7828809984 88480 _ _ (1139053 / 50000) (1781473 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828777216 7828809984 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828809984 :
    ThetaLowerSegment 7828809984 7828842752 (195682025675207 / 25000)
      (391365672222833 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828809984 33 20 (1139053 / 50000)
        (2278109 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828809984 7828842752 88480 _ _ (1139053 / 50000) (1781473 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828809984 7828842752 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828842752 :
    ThetaLowerSegment 7828842752 7828875520 (391365672222833 / 50000) (48920915481301 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828842752 33 20 (2278107 / 100000)
        (227811 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828842752 7828875520 88480 _ _ (2278107 / 100000) (71259 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828842752 7828875520 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828875520 :
    ThetaLowerSegment 7828875520 7828908288 (48920915481301 / 6250) (195684507102901 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828875520 33 20 (2278107 / 100000)
        (227811 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828875520 7828908288 88480 _ _ (2278107 / 100000) (71259 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828875520 7828908288 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828908288 :
    ThetaLowerSegment 7828908288 7828941056 (195684507102901 / 25000)
      (782741320276219 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828908288 33 20 (2278107 / 100000)
        (227811 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828908288 7828941056 88481 _ _ (2278107 / 100000) (71259 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828908288 7828941056 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828941056 :
    ThetaLowerSegment 7828941056 7828973824 (782741320276219 / 100000)
      (156548902836727 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828941056 33 20 (569527 / 25000)
        (2278111 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828941056 7828973824 88481 _ _ (569527 / 25000) (445369 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828941056 7828973824 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7828973824 :
    ThetaLowerSegment 7828973824 7829006592 (156548902836727 / 20000)
      (782747767321859 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7828973824 33 20 (569527 / 25000)
        (2278111 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7828973824 7829006592 88481 _ _ (569527 / 25000) (445369 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7828973824 7829006592 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829006592 :
    ThetaLowerSegment 7829006592 7829039360 (782747767321859 / 100000)
      (391375550097663 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829006592 33 20 (2278109 / 100000)
        (71191 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829006592 7829039360 88481 _ _ (2278109 / 100000) (890739 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829006592 7829039360 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829039360 :
    ThetaLowerSegment 7829039360 7829072128 (391375550097663 / 50000)
      (195688594029017 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829039360 33 20 (2278109 / 100000)
        (71191 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829039360 7829072128 88481 _ _ (2278109 / 100000) (890739 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829039360 7829072128 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829072128 :
    ThetaLowerSegment 7829072128 7829104896 (195688594029017 / 25000)
      (782757576859213 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829072128 33 20 (2278109 / 100000)
        (71191 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829072128 7829104896 88482 _ _ (2278109 / 100000) (890739 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829072128 7829104896 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829104896 :
    ThetaLowerSegment 7829104896 7829137664 (782757576859213 / 100000)
      (782760930237133 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829104896 33 20 (227811 / 10000)
        (2278113 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829104896 7829137664 88482 _ _ (227811 / 10000) (44537 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829104896 7829137664 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829137664 :
    ThetaLowerSegment 7829137664 7829170432 (782760930237133 / 100000)
      (782764153762783 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829137664 33 20 (227811 / 10000)
        (2278113 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829137664 7829170432 88482 _ _ (227811 / 10000) (44537 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829137664 7829170432 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829170432 :
    ThetaLowerSegment 7829170432 7829203200 (782764153762783 / 100000)
      (156553487759769 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829170432 33 20 (2278111 / 100000)
        (1139057 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829170432 7829203200 88482 _ _ (2278111 / 100000) (1781481 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829170432 7829203200 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829203200 :
    ThetaLowerSegment 7829203200 7829235968 (156553487759769 / 20000)
      (782770732947351 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829203200 33 20 (2278111 / 100000)
        (1139057 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829203200 7829235968 88482 _ _ (2278111 / 100000) (1781481 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829203200 7829235968 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829235968 :
    ThetaLowerSegment 7829235968 7829268736 (782770732947351 / 100000)
      (782773897244919 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829235968 33 20 (71191 / 3125) (455623 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829235968 7829268736 88482 _ _ (71191 / 3125) (1781483 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829235968 7829268736 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829268736 :
    ThetaLowerSegment 7829268736 7829301504 (782773897244919 / 100000)
      (782777159501303 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829268736 33 20 (71191 / 3125) (455623 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829268736 7829301504 88483 _ _ (71191 / 3125) (1781483 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829268736 7829301504 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829301504 :
    ThetaLowerSegment 7829301504 7829334272 (782777159501303 / 100000)
      (782780446816919 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829301504 33 20 (71191 / 3125) (455623 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829301504 7829334272 88483 _ _ (71191 / 3125) (1781483 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829301504 7829334272 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829334272 :
    ThetaLowerSegment 7829334272 7829367040 (782780446816919 / 100000)
      (782783695406057 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829334272 33 20 (2278113 / 100000)
        (569529 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829334272 7829367040 88483 _ _ (2278113 / 100000) (445371 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829334272 7829367040 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829367040 :
    ThetaLowerSegment 7829367040 7829399808 (782783695406057 / 100000) (15655740474583 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829367040 33 20 (2278113 / 100000)
        (569529 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829367040 7829399808 88483 _ _ (2278113 / 100000) (445371 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829367040 7829399808 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829399808 :
    ThetaLowerSegment 7829399808 7829432576 (15655740474583 / 2000) (195697564093229 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829399808 33 20 (1139057 / 50000)
        (2278117 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829399808 7829432576 88483 _ _ (1139057 / 50000) (890743 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829399808 7829432576 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829432576 :
    ThetaLowerSegment 7829432576 7829465344 (195697564093229 / 25000)
      (391396785514393 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829432576 33 20 (1139057 / 50000)
        (2278117 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829432576 7829465344 88484 _ _ (1139057 / 50000) (890743 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829432576 7829465344 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829465344 :
    ThetaLowerSegment 7829465344 7829498112 (391396785514393 / 50000)
      (782796872017421 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829465344 33 20 (455623 / 20000)
        (1139059 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829465344 7829498112 88484 _ _ (455623 / 20000) (111343 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829465344 7829498112 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829498112 :
    ThetaLowerSegment 7829498112 7829530880 (782796872017421 / 100000)
      (391400084224913 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829498112 33 20 (455623 / 20000)
        (1139059 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829498112 7829530880 88484 _ _ (455623 / 20000) (111343 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829498112 7829530880 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829530880 :
    ThetaLowerSegment 7829530880 7829563648 (391400084224913 / 50000)
      (782803446657311 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829530880 33 20 (455623 / 20000)
        (1139059 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829530880 7829563648 88484 _ _ (455623 / 20000) (111343 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829530880 7829563648 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829563648 :
    ThetaLowerSegment 7829563648 7829596416 (782803446657311 / 100000)
      (782806939009139 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829563648 33 20 (569529 / 25000)
        (2278119 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829563648 7829596416 88484 _ _ (569529 / 25000) (1781489 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829563648 7829596416 12 1533 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829596416 :
    ThetaLowerSegment 7829596416 7829629184 (782806939009139 / 100000)
      (782810274170963 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829596416 33 20 (569529 / 25000)
        (2278119 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829596416 7829629184 88485 _ _ (569529 / 25000) (1781489 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829596416 7829629184 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829629184 :
    ThetaLowerSegment 7829629184 7829661952 (782810274170963 / 100000)
      (156562718221863 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829629184 33 20 (2278117 / 100000)
        (56953 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829629184 7829661952 88485 _ _ (2278117 / 100000) (1781491 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829629184 7829661952 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829661952 :
    ThetaLowerSegment 7829661952 7829694720 (156562718221863 / 20000)
      (391408457441009 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829661952 33 20 (2278117 / 100000)
        (56953 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829661952 7829694720 88485 _ _ (2278117 / 100000) (1781491 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829661952 7829694720 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829694720 :
    ThetaLowerSegment 7829694720 7829727488 (391408457441009 / 50000)
      (782820238654721 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829694720 33 20 (2278117 / 100000)
        (56953 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829694720 7829727488 88485 _ _ (2278117 / 100000) (1781491 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829694720 7829727488 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829727488 :
    ThetaLowerSegment 7829727488 7829760256 (782820238654721 / 100000)
      (782823541925821 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829727488 33 20 (1139059 / 50000)
        (2278121 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829727488 7829760256 88485 _ _ (1139059 / 50000) (1781493 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829727488 7829760256 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829760256 :
    ThetaLowerSegment 7829760256 7829793024 (782823541925821 / 100000)
      (782826785965853 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829760256 33 20 (1139059 / 50000)
        (2278121 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829760256 7829793024 88485 _ _ (1139059 / 50000) (1781493 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829760256 7829793024 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829793024 :
    ThetaLowerSegment 7829793024 7829825792 (782826785965853 / 100000)
      (78283007329157 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829793024 33 20 (2278119 / 100000)
        (1139061 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829793024 7829825792 88486 _ _ (2278119 / 100000) (890747 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829793024 7829825792 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829825792 :
    ThetaLowerSegment 7829825792 7829858560 (78283007329157 / 10000) (156566663922229 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829825792 33 20 (2278119 / 100000)
        (1139061 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829825792 7829858560 88486 _ _ (2278119 / 100000) (890747 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829825792 7829858560 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829858560 :
    ThetaLowerSegment 7829858560 7829891328 (156566663922229 / 20000)
      (156567338245749 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829858560 33 20 (56953 / 2500)
        (2278123 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829858560 7829891328 88486 _ _ (56953 / 2500) (222687 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829858560 7829891328 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829891328 :
    ThetaLowerSegment 7829891328 7829924096 (156567338245749 / 20000)
      (156567995711181 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829891328 33 20 (56953 / 2500)
        (2278123 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829891328 7829924096 88486 _ _ (56953 / 2500) (222687 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829891328 7829924096 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829924096 :
    ThetaLowerSegment 7829924096 7829956864 (156567995711181 / 20000)
      (156568634951653 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829924096 33 20 (56953 / 2500)
        (2278123 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829924096 7829956864 88486 _ _ (56953 / 2500) (222687 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829924096 7829956864 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829956864 :
    ThetaLowerSegment 7829956864 7829989632 (156568634951653 / 20000)
      (391423196871619 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829956864 33 20 (2278121 / 100000)
        (569531 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829956864 7829989632 88487 _ _ (2278121 / 100000) (890749 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829956864 7829989632 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7829989632 :
    ThetaLowerSegment 7829989632 7830022400 (391423196871619 / 50000)
      (782849731190503 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7829989632 33 20 (2278121 / 100000)
        (569531 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7829989632 7830022400 88487 _ _ (2278121 / 100000) (890749 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7829989632 7830022400 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830022400 :
    ThetaLowerSegment 7830022400 7830055168 (782849731190503 / 100000)
      (782853009408061 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830022400 33 20 (1139061 / 50000) (729 / 32) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830022400 7830055168 88487 _ _ (1139061 / 50000) (1781499 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830022400 7830055168 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830055168 :
    ThetaLowerSegment 7830055168 7830087936 (782853009408061 / 100000)
      (782856232950691 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830055168 33 20 (1139061 / 50000) (729 / 32) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830055168 7830087936 88487 _ _ (1139061 / 50000) (1781499 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830055168 7830087936 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830087936 :
    ThetaLowerSegment 7830087936 7830120704 (782856232950691 / 100000)
      (782859604571251 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830087936 33 20 (1139061 / 50000) (729 / 32) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830087936 7830120704 88487 _ _ (1139061 / 50000) (1781499 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830087936 7830120704 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830120704 :
    ThetaLowerSegment 7830120704 7830153472 (782859604571251 / 100000) (39143144595137 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830120704 33 20 (2278123 / 100000)
        (1139063 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830120704 7830153472 88487 _ _ (2278123 / 100000) (1781501 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830120704 7830153472 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830153472 :
    ThetaLowerSegment 7830153472 7830186240 (39143144595137 / 5000) (782866156452999 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830153472 33 20 (2278123 / 100000)
        (1139063 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830153472 7830186240 88488 _ _ (2278123 / 100000) (1781501 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830153472 7830186240 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830186240 :
    ThetaLowerSegment 7830186240 7830219008 (782866156452999 / 100000)
      (782869443785931 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830186240 33 20 (569531 / 25000)
        (2278127 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830186240 7830219008 88488 _ _ (569531 / 25000) (1781503 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830186240 7830219008 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830219008 :
    ThetaLowerSegment 7830219008 7830251776 (782869443785931 / 100000)
      (782872799462583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830219008 33 20 (569531 / 25000)
        (2278127 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830219008 7830251776 88488 _ _ (569531 / 25000) (1781503 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830219008 7830251776 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830251776 :
    ThetaLowerSegment 7830251776 7830284544 (782872799462583 / 100000)
      (391438020617229 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830251776 33 20 (729 / 32) (142383 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830251776 7830284544 88488 _ _ (729 / 32) (55672 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830251776 7830284544 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830284544 :
    ThetaLowerSegment 7830284544 7830317312 (391438020617229 / 50000)
      (782879260225083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830284544 33 20 (729 / 32) (142383 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830284544 7830317312 88488 _ _ (729 / 32) (55672 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830284544 7830317312 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830317312 :
    ThetaLowerSegment 7830317312 7830350080 (782879260225083 / 100000)
      (391441287448479 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830317312 33 20 (729 / 32) (142383 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830317312 7830350080 88489 _ _ (729 / 32) (55672 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830317312 7830350080 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830350080 :
    ThetaLowerSegment 7830350080 7830382848 (391441287448479 / 50000) (15657717199093 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830350080 33 20 (1139063 / 50000)
        (2278129 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830350080 7830382848 88489 _ _ (1139063 / 50000) (890753 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830350080 7830382848 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830382848 :
    ThetaLowerSegment 7830382848 7830415616 (15657717199093 / 2000) (195722279988239 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830382848 33 20 (1139063 / 50000)
        (2278129 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830382848 7830415616 88489 _ _ (1139063 / 50000) (890753 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830382848 7830415616 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830415616 :
    ThetaLowerSegment 7830415616 7830448384 (195722279988239 / 25000)
      (391446197949791 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830415616 33 20 (2278127 / 100000)
        (227813 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830415616 7830448384 88489 _ _ (2278127 / 100000) (445377 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830415616 7830448384 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830448384 :
    ThetaLowerSegment 7830448384 7830481152 (391446197949791 / 50000)
      (782895665011827 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830448384 33 20 (2278127 / 100000)
        (227813 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830448384 7830481152 88489 _ _ (2278127 / 100000) (445377 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830448384 7830481152 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830481152 :
    ThetaLowerSegment 7830481152 7830513920 (782895665011827 / 100000)
      (782898918177183 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830481152 33 20 (2278127 / 100000)
        (227813 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830481152 7830513920 88490 _ _ (2278127 / 100000) (445377 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830481152 7830513920 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830513920 :
    ThetaLowerSegment 7830513920 7830546688 (782898918177183 / 100000)
      (782902180456479 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830513920 33 20 (142383 / 6250)
        (2278131 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830513920 7830546688 88490 _ _ (142383 / 6250) (1781509 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830513920 7830546688 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830546688 :
    ThetaLowerSegment 7830546688 7830579456 (782902180456479 / 100000)
      (782905458682671 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830546688 33 20 (142383 / 6250)
        (2278131 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830546688 7830579456 88490 _ _ (142383 / 6250) (1781509 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830546688 7830579456 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830579456 :
    ThetaLowerSegment 7830579456 7830612224 (782905458682671 / 100000) (48931803176047 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830579456 33 20 (2278129 / 100000)
        (569533 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830579456 7830612224 88490 _ _ (2278129 / 100000) (1781511 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830579456 7830612224 12 1489 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830612224 :
    ThetaLowerSegment 7830612224 7830644992 (48931803176047 / 6250) (97864032362217 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830612224 33 20 (2278129 / 100000)
        (569533 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830612224 7830644992 88490 _ _ (2278129 / 100000) (1781511 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830612224 7830644992 12 1496 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830644992 :
    ThetaLowerSegment 7830644992 7830677760 (97864032362217 / 12500) (391457800457223 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830644992 33 20 (227813 / 10000)
        (2278133 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830644992 7830677760 88490 _ _ (227813 / 10000) (1781513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830644992 7830677760 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830677760 :
    ThetaLowerSegment 7830677760 7830710528 (391457800457223 / 50000)
      (195729722064009 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830677760 33 20 (227813 / 10000)
        (2278133 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830677760 7830710528 88491 _ _ (227813 / 10000) (1781513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830677760 7830710528 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830710528 :
    ThetaLowerSegment 7830710528 7830743296 (195729722064009 / 25000)
      (195730530800159 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830710528 33 20 (227813 / 10000)
        (2278133 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830710528 7830743296 88491 _ _ (227813 / 10000) (1781513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830710528 7830743296 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830743296 :
    ThetaLowerSegment 7830743296 7830776064 (195730530800159 / 25000)
      (391462754251651 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830743296 33 20 (2278131 / 100000)
        (1139067 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830743296 7830776064 88491 _ _ (2278131 / 100000) (890757 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830743296 7830776064 12 1486 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830776064 :
    ThetaLowerSegment 7830776064 7830808832 (391462754251651 / 50000)
      (782928759396239 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830776064 33 20 (2278131 / 100000)
        (1139067 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830776064 7830808832 88491 _ _ (2278131 / 100000) (890757 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830776064 7830808832 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830808832 :
    ThetaLowerSegment 7830808832 7830841600 (782928759396239 / 100000)
      (156586391123087 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830808832 33 20 (569533 / 25000)
        (455627 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830808832 7830841600 88491 _ _ (569533 / 25000) (445379 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830808832 7830841600 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830841600 :
    ThetaLowerSegment 7830841600 7830874368 (156586391123087 / 20000)
      (782935274853759 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830841600 33 20 (569533 / 25000)
        (455627 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830841600 7830874368 88492 _ _ (569533 / 25000) (445379 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830841600 7830874368 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830874368 :
    ThetaLowerSegment 7830874368 7830907136 (782935274853759 / 100000)
      (391469326662499 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830874368 33 20 (2278133 / 100000)
        (284767 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830874368 7830907136 88492 _ _ (2278133 / 100000) (1781517 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830874368 7830907136 12 1483 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830907136 :
    ThetaLowerSegment 7830907136 7830939904 (391469326662499 / 50000)
      (782941995346109 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830907136 33 20 (2278133 / 100000)
        (284767 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830907136 7830939904 88492 _ _ (2278133 / 100000) (1781517 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830907136 7830939904 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830939904 :
    ThetaLowerSegment 7830939904 7830972672 (782941995346109 / 100000)
      (195736302447943 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830939904 33 20 (2278133 / 100000)
        (284767 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830939904 7830972672 88492 _ _ (2278133 / 100000) (1781517 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830939904 7830972672 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7830972672 :
    ThetaLowerSegment 7830972672 7831005440 (195736302447943 / 25000)
      (391474271350907 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7830972672 33 20 (1139067 / 50000)
        (2278137 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7830972672 7831005440 88492 _ _ (1139067 / 50000) (1781519 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7830972672 7831005440 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831005440 :
    ThetaLowerSegment 7831005440 7831038208 (391474271350907 / 50000) (97868965087343 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831005440 33 20 (1139067 / 50000)
        (2278137 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831005440 7831038208 88492 _ _ (1139067 / 50000) (1781519 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831005440 7831038208 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831038208 :
    ThetaLowerSegment 7831038208 7831070976 (97868965087343 / 12500)
      (782955062722789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831038208 33 20 (455627 / 20000)
        (1139069 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831038208 7831070976 88493 _ _ (455627 / 20000) (1781521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831038208 7831070976 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831070976 :
    ThetaLowerSegment 7831070976 7831103744 (782955062722789 / 100000) (24467448012587 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831070976 33 20 (455627 / 20000)
        (1139069 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831070976 7831103744 88493 _ _ (455627 / 20000) (1781521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831070976 7831103744 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831103744 :
    ThetaLowerSegment 7831103744 7831136512 (24467448012587 / 3125) (782961710320719 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831103744 33 20 (455627 / 20000)
        (1139069 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831103744 7831136512 88493 _ _ (455627 / 20000) (1781521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831103744 7831136512 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831136512 :
    ThetaLowerSegment 7831136512 7831169280 (782961710320719 / 100000) (6263720036043 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831136512 33 20 (284767 / 12500)
        (2278139 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831136512 7831169280 88493 _ _ (284767 / 12500) (890761 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831136512 7831169280 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831169280 :
    ThetaLowerSegment 7831169280 7831202048 (6263720036043 / 800) (782968287299351 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831169280 33 20 (284767 / 12500)
        (2278139 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831169280 7831202048 88493 _ _ (284767 / 12500) (890761 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831169280 7831202048 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831202048 :
    ThetaLowerSegment 7831202048 7831234816 (782968287299351 / 100000)
      (782971586041727 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831202048 33 20 (2278137 / 100000)
        (113907 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831202048 7831234816 88494 _ _ (2278137 / 100000) (445381 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831202048 7831234816 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831234816 :
    ThetaLowerSegment 7831234816 7831267584 (782971586041727 / 100000)
      (195743701262327 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831234816 33 20 (2278137 / 100000)
        (113907 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831234816 7831267584 88494 _ _ (2278137 / 100000) (445381 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831234816 7831267584 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831267584 :
    ThetaLowerSegment 7831267584 7831300352 (195743701262327 / 25000) (97872251013917 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831267584 33 20 (1139069 / 50000)
        (2278141 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831267584 7831300352 88494 _ _ (1139069 / 50000) (890763 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831267584 7831300352 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831300352 :
    ThetaLowerSegment 7831300352 7831333120 (97872251013917 / 12500) (391490604447613 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831300352 33 20 (1139069 / 50000)
        (2278141 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831300352 7831333120 88494 _ _ (1139069 / 50000) (890763 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831300352 7831333120 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831333120 :
    ThetaLowerSegment 7831333120 7831365888 (391490604447613 / 50000)
      (391492251541387 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831333120 33 20 (1139069 / 50000)
        (2278141 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831333120 7831365888 88494 _ _ (1139069 / 50000) (890763 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831333120 7831365888 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831365888 :
    ThetaLowerSegment 7831365888 7831398656 (391492251541387 / 50000) (97873474658971 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831365888 33 20 (2278139 / 100000)
        (1139071 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831365888 7831398656 88495 _ _ (2278139 / 100000) (1781527 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831365888 7831398656 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831398656 :
    ThetaLowerSegment 7831398656 7831431424 (97873474658971 / 12500) (9787388700213 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831398656 33 20 (2278139 / 100000)
        (1139071 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831398656 7831431424 88495 _ _ (2278139 / 100000) (1781527 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831398656 7831431424 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831431424 :
    ThetaLowerSegment 7831431424 7831464192 (9787388700213 / 1250) (19574858843931 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831431424 33 20 (113907 / 5000)
        (2278143 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831431424 7831464192 88495 _ _ (113907 / 5000) (1781529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831431424 7831464192 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831464192 :
    ThetaLowerSegment 7831464192 7831496960 (19574858843931 / 2500) (39149885245059 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831464192 33 20 (113907 / 5000)
        (2278143 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831464192 7831496960 88495 _ _ (113907 / 5000) (1781529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831464192 7831496960 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831496960 :
    ThetaLowerSegment 7831496960 7831529728 (39149885245059 / 5000) (9787512631029 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831496960 33 20 (113907 / 5000)
        (2278143 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831496960 7831529728 88495 _ _ (113907 / 5000) (1781529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831496960 7831529728 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831529728 :
    ThetaLowerSegment 7831529728 7831562496 (9787512631029 / 1250) (783004238608117 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831529728 33 20 (2278141 / 100000)
        (71192 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831529728 7831562496 88495 _ _ (2278141 / 100000) (1781531 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831529728 7831562496 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831562496 :
    ThetaLowerSegment 7831562496 7831595264 (783004238608117 / 100000)
      (391503710585547 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831562496 33 20 (2278141 / 100000)
        (71192 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831562496 7831595264 88496 _ _ (2278141 / 100000) (1781531 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831562496 7831595264 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831595264 :
    ThetaLowerSegment 7831595264 7831628032 (391503710585547 / 50000)
      (391505339457077 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831595264 33 20 (1139071 / 50000)
        (455629 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831595264 7831628032 88496 _ _ (1139071 / 50000) (445383 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831595264 7831628032 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831628032 :
    ThetaLowerSegment 7831628032 7831660800 (391505339457077 / 50000)
      (391507016169589 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831628032 33 20 (1139071 / 50000)
        (455629 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831628032 7831660800 88496 _ _ (1139071 / 50000) (445383 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831628032 7831660800 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831660800 :
    ThetaLowerSegment 7831660800 7831693568 (391507016169589 / 50000)
      (391508688326551 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831660800 33 20 (2278143 / 100000)
        (1139073 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831660800 7831693568 88496 _ _ (2278143 / 100000) (890767 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831660800 7831693568 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831693568 :
    ThetaLowerSegment 7831693568 7831726336 (391508688326551 / 50000)
      (783020582000303 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831693568 33 20 (2278143 / 100000)
        (1139073 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831693568 7831726336 88496 _ _ (2278143 / 100000) (890767 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831693568 7831726336 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831726336 :
    ThetaLowerSegment 7831726336 7831759104 (783020582000303 / 100000)
      (783023816963363 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831726336 33 20 (2278143 / 100000)
        (1139073 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831726336 7831759104 88497 _ _ (2278143 / 100000) (890767 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831726336 7831759104 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831759104 :
    ThetaLowerSegment 7831759104 7831791872 (783023816963363 / 100000)
      (783027108881443 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831759104 33 20 (71192 / 3125)
        (2278147 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831759104 7831791872 88497 _ _ (71192 / 3125) (55673 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831759104 7831791872 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831791872 :
    ThetaLowerSegment 7831791872 7831824640 (783027108881443 / 100000)
      (783030332455203 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831791872 33 20 (71192 / 3125)
        (2278147 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831791872 7831824640 88497 _ _ (71192 / 3125) (55673 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831791872 7831824640 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831824640 :
    ThetaLowerSegment 7831824640 7831857408 (783030332455203 / 100000)
      (97879198490551 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831824640 33 20 (455629 / 20000)
        (569537 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831824640 7831857408 88497 _ _ (455629 / 20000) (1781537 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831824640 7831857408 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831857408 :
    ThetaLowerSegment 7831857408 7831890176 (97879198490551 / 12500)
      (783036825168453 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831857408 33 20 (455629 / 20000)
        (569537 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831857408 7831890176 88497 _ _ (455629 / 20000) (1781537 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831857408 7831890176 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831890176 :
    ThetaLowerSegment 7831890176 7831922944 (783036825168453 / 100000)
      (195760012185907 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831890176 33 20 (455629 / 20000)
        (569537 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831890176 7831922944 88497 _ _ (455629 / 20000) (1781537 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831890176 7831922944 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831922944 :
    ThetaLowerSegment 7831922944 7831955712 (195760012185907 / 25000)
      (391521658941569 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831922944 33 20 (1139073 / 50000)
        (2278149 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831922944 7831955712 88498 _ _ (1139073 / 50000) (1781539 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831922944 7831955712 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831955712 :
    ThetaLowerSegment 7831955712 7831988480 (391521658941569 / 50000)
      (391523285537813 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831955712 33 20 (1139073 / 50000)
        (2278149 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831955712 7831988480 88498 _ _ (1139073 / 50000) (1781539 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831955712 7831988480 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7831988480 :
    ThetaLowerSegment 7831988480 7832021248 (391523285537813 / 50000)
      (783049881223217 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7831988480 33 20 (2278147 / 100000)
        (45563 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7831988480 7832021248 88498 _ _ (2278147 / 100000) (1781541 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7831988480 7832021248 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832021248 :
    ThetaLowerSegment 7832021248 7832054016 (783049881223217 / 100000)
      (391526529619141 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832021248 33 20 (2278147 / 100000)
        (45563 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832021248 7832054016 88498 _ _ (2278147 / 100000) (1781541 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832021248 7832054016 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832054016 :
    ThetaLowerSegment 7832054016 7832086784 (391526529619141 / 50000)
      (391528180137367 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832054016 33 20 (569537 / 25000)
        (2278151 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832054016 7832086784 88498 _ _ (569537 / 25000) (890771 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832054016 7832086784 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832086784 :
    ThetaLowerSegment 7832086784 7832119552 (391528180137367 / 50000)
      (391529894443737 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832086784 33 20 (569537 / 25000)
        (2278151 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832086784 7832119552 88499 _ _ (569537 / 25000) (890771 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832086784 7832119552 12 1505 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832119552 :
    ThetaLowerSegment 7832119552 7832152320 (391529894443737 / 50000)
      (391531511928817 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832119552 33 20 (569537 / 25000)
        (2278151 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832119552 7832152320 88499 _ _ (569537 / 25000) (890771 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832119552 7832152320 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832152320 :
    ThetaLowerSegment 7832152320 7832185088 (391531511928817 / 50000) (7830662907233 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832152320 33 20 (2278149 / 100000)
        (284769 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832152320 7832185088 88499 _ _ (2278149 / 100000) (222693 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832152320 7832185088 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832185088 :
    ThetaLowerSegment 7832185088 7832217856 (7830662907233 / 1000) (391534801575973 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832185088 33 20 (2278149 / 100000)
        (284769 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832185088 7832217856 88499 _ _ (2278149 / 100000) (222693 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832185088 7832217856 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832217856 :
    ThetaLowerSegment 7832217856 7832250624 (391534801575973 / 50000)
      (391536457791023 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832217856 33 20 (45563 / 2000)
        (2278153 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832217856 7832250624 88499 _ _ (45563 / 2000) (890773 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832217856 7832250624 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832250624 :
    ThetaLowerSegment 7832250624 7832283392 (391536457791023 / 50000)
      (391538093502723 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832250624 33 20 (45563 / 2000)
        (2278153 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832250624 7832283392 88500 _ _ (45563 / 2000) (890773 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832250624 7832283392 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832283392 :
    ThetaLowerSegment 7832283392 7832316160 (391538093502723 / 50000)
      (391539740605173 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832283392 33 20 (45563 / 2000)
        (2278153 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832283392 7832316160 88500 _ _ (45563 / 2000) (890773 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832283392 7832316160 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832316160 :
    ThetaLowerSegment 7832316160 7832348928 (391539740605173 / 50000)
      (783082745800729 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832316160 33 20 (2278151 / 100000)
        (1139077 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832316160 7832348928 88500 _ _ (2278151 / 100000) (1781547 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832316160 7832348928 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832348928 :
    ThetaLowerSegment 7832348928 7832381696 (783082745800729 / 100000)
      (78308605139783 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832348928 33 20 (2278151 / 100000)
        (1139077 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832348928 7832381696 88500 _ _ (2278151 / 100000) (1781547 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832348928 7832381696 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832381696 :
    ThetaLowerSegment 7832381696 7832414464 (78308605139783 / 10000) (391544679637267 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832381696 33 20 (284769 / 12500)
        (455631 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832381696 7832414464 88500 _ _ (284769 / 12500) (1781549 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832381696 7832414464 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832414464 :
    ThetaLowerSegment 7832414464 7832447232 (391544679637267 / 50000) (78309260108483 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832414464 33 20 (284769 / 12500)
        (455631 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832414464 7832447232 88500 _ _ (284769 / 12500) (1781549 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832414464 7832447232 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832447232 :
    ThetaLowerSegment 7832447232 7832480000 (78309260108483 / 10000) (97886978938223 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832447232 33 20 (2278153 / 100000)
        (569539 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832447232 7832480000 88501 _ _ (2278153 / 100000) (35631 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832447232 7832480000 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832480000 :
    ThetaLowerSegment 7832480000 7832512768 (97886978938223 / 12500) (156619834711247 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832480000 33 20 (2278153 / 100000)
        (569539 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832480000 7832512768 88501 _ _ (2278153 / 100000) (35631 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832480000 7832512768 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832512768 :
    ThetaLowerSegment 7832512768 7832545536 (156619834711247 / 20000)
      (783102490547003 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832512768 33 20 (2278153 / 100000)
        (569539 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832512768 7832545536 88501 _ _ (2278153 / 100000) (35631 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832512768 7832545536 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832545536 :
    ThetaLowerSegment 7832545536 7832578304 (783102490547003 / 100000)
      (783105759697993 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832545536 33 20 (1139077 / 50000)
        (2278157 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832545536 7832578304 88501 _ _ (1139077 / 50000) (111347 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832545536 7832578304 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832578304 :
    ThetaLowerSegment 7832578304 7832611072 (783105759697993 / 100000)
      (783109074412063 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832578304 33 20 (1139077 / 50000)
        (2278157 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832578304 7832611072 88501 _ _ (1139077 / 50000) (111347 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832578304 7832611072 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832611072 :
    ThetaLowerSegment 7832611072 7832643840 (783109074412063 / 100000)
      (783112327617403 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832611072 33 20 (455631 / 20000)
        (1139079 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832611072 7832643840 88502 _ _ (455631 / 20000) (890777 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832611072 7832643840 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832643840 :
    ThetaLowerSegment 7832643840 7832676608 (783112327617403 / 100000)
      (783115580822743 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832643840 33 20 (455631 / 20000)
        (1139079 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832643840 7832676608 88502 _ _ (455631 / 20000) (890777 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832643840 7832676608 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832676608 :
    ThetaLowerSegment 7832676608 7832709376 (783115580822743 / 100000)
      (783118886427099 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832676608 33 20 (569539 / 25000)
        (2278159 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832676608 7832709376 88502 _ _ (569539 / 25000) (356311 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832676608 7832709376 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832709376 :
    ThetaLowerSegment 7832709376 7832742144 (783118886427099 / 100000)
      (783122262654291 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832709376 33 20 (569539 / 25000)
        (2278159 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832709376 7832742144 88502 _ _ (569539 / 25000) (356311 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832709376 7832742144 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832742144 :
    ThetaLowerSegment 7832742144 7832774912 (783122262654291 / 100000)
      (783125568258647 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832742144 33 20 (569539 / 25000)
        (2278159 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832742144 7832774912 88502 _ _ (569539 / 25000) (356311 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832742144 7832774912 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832774912 :
    ThetaLowerSegment 7832774912 7832807680 (783125568258647 / 100000)
      (783128908036809 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832774912 33 20 (2278157 / 100000)
        (28477 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832774912 7832807680 88502 _ _ (2278157 / 100000) (1781557 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832774912 7832807680 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832807680 :
    ThetaLowerSegment 7832807680 7832840448 (783128908036809 / 100000)
      (783132193139203 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832807680 33 20 (2278157 / 100000)
        (28477 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832807680 7832840448 88503 _ _ (2278157 / 100000) (1781557 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832807680 7832840448 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832840448 :
    ThetaLowerSegment 7832840448 7832873216 (783132193139203 / 100000)
      (783135507859093 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832840448 33 20 (1139079 / 50000)
        (2278161 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832840448 7832873216 88503 _ _ (1139079 / 50000) (1781559 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832840448 7832873216 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832873216 :
    ThetaLowerSegment 7832873216 7832905984 (783135507859093 / 100000)
      (783138720061873 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832873216 33 20 (1139079 / 50000)
        (2278161 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832873216 7832905984 88503 _ _ (1139079 / 50000) (1781559 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832873216 7832905984 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832905984 :
    ThetaLowerSegment 7832905984 7832938752 (783138720061873 / 100000)
      (783142048450711 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832905984 33 20 (1139079 / 50000)
        (2278161 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832905984 7832938752 88503 _ _ (1139079 / 50000) (1781559 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832905984 7832938752 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832938752 :
    ThetaLowerSegment 7832938752 7832971520 (783142048450711 / 100000) (39157263146653 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832938752 33 20 (2278159 / 100000)
        (1139081 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832938752 7832971520 88503 _ _ (2278159 / 100000) (44539 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832938752 7832971520 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7832971520 :
    ThetaLowerSegment 7832971520 7833004288 (39157263146653 / 5000) (391574292244441 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7832971520 33 20 (2278159 / 100000)
        (1139081 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7832971520 7833004288 88504 _ _ (2278159 / 100000) (44539 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7832971520 7833004288 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833004288 :
    ThetaLowerSegment 7833004288 7833037056 (391574292244441 / 50000)
      (391575922267921 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833004288 33 20 (28477 / 1250)
        (2278163 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833004288 7833037056 88504 _ _ (28477 / 1250) (890781 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833004288 7833037056 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833037056 :
    ThetaLowerSegment 7833037056 7833069824 (391575922267921 / 50000)
      (391577588741961 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833037056 33 20 (28477 / 1250)
        (2278163 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833037056 7833069824 88504 _ _ (28477 / 1250) (890781 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833037056 7833069824 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833069824 :
    ThetaLowerSegment 7833069824 7833102592 (391577588741961 / 50000)
      (195789615648021 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833069824 33 20 (2278161 / 100000)
        (569541 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833069824 7833102592 88504 _ _ (2278161 / 100000) (445391 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833069824 7833102592 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833102592 :
    ThetaLowerSegment 7833102592 7833135360 (195789615648021 / 25000) (78316171124967 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833102592 33 20 (2278161 / 100000)
        (569541 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833102592 7833135360 88504 _ _ (2278161 / 100000) (445391 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833102592 7833135360 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833135360 :
    ThetaLowerSegment 7833135360 7833168128 (78316171124967 / 10000) (391582486788111 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833135360 33 20 (2278161 / 100000)
        (569541 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833135360 7833168128 88505 _ _ (2278161 / 100000) (445391 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833135360 7833168128 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833168128 :
    ThetaLowerSegment 7833168128 7833200896 (391582486788111 / 50000) (78316821767891 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833168128 33 20 (1139081 / 50000)
        (455633 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833168128 7833200896 88505 _ _ (1139081 / 50000) (356313 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833168128 7833200896 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833200896 :
    ThetaLowerSegment 7833200896 7833233664 (78316821767891 / 10000) (15663429053379 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833200896 33 20 (1139081 / 50000)
        (455633 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833200896 7833233664 88505 _ _ (1139081 / 50000) (356313 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833200896 7833233664 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833233664 :
    ThetaLowerSegment 7833233664 7833266432 (15663429053379 / 2000) (783174712720203 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833233664 33 20 (2278163 / 100000)
        (1139083 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833233664 7833266432 88505 _ _ (2278163 / 100000) (1781567 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833233664 7833266432 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833266432 :
    ThetaLowerSegment 7833266432 7833299200 (783174712720203 / 100000)
      (783177943155337 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833266432 33 20 (2278163 / 100000)
        (1139083 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833266432 7833299200 88505 _ _ (2278163 / 100000) (1781567 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833266432 7833299200 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833299200 :
    ThetaLowerSegment 7833299200 7833331968 (783177943155337 / 100000)
      (783181246491687 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833299200 33 20 (2278163 / 100000)
        (1139083 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833299200 7833331968 88505 _ _ (2278163 / 100000) (1781567 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833299200 7833331968 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833331968 :
    ThetaLowerSegment 7833331968 7833364736 (783181246491687 / 100000)
      (783184472371911 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833331968 33 20 (569541 / 25000)
        (2278167 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833331968 7833364736 88506 _ _ (569541 / 25000) (1781569 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833331968 7833364736 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833364736 :
    ThetaLowerSegment 7833364736 7833397504 (783184472371911 / 100000)
      (783187702808463 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833364736 33 20 (569541 / 25000)
        (2278167 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833364736 7833397504 88506 _ _ (569541 / 25000) (1781569 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833364736 7833397504 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833397504 :
    ThetaLowerSegment 7833397504 7833430272 (783187702808463 / 100000)
      (783190956028083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833397504 33 20 (455633 / 20000)
        (284771 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833397504 7833430272 88506 _ _ (455633 / 20000) (178157 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833397504 7833430272 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833430272 :
    ThetaLowerSegment 7833430272 7833463040 (783190956028083 / 100000)
      (783194277592653 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833430272 33 20 (455633 / 20000)
        (284771 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833430272 7833463040 88506 _ _ (455633 / 20000) (178157 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833430272 7833463040 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833463040 :
    ThetaLowerSegment 7833463040 7833495808 (783194277592653 / 100000)
      (156639503428941 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833463040 33 20 (1139083 / 50000)
        (2278169 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833463040 7833495808 88506 _ _ (1139083 / 50000) (445393 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833463040 7833495808 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833495808 :
    ThetaLowerSegment 7833495808 7833528576 (156639503428941 / 20000)
      (783200799981911 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833495808 33 20 (1139083 / 50000)
        (2278169 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833495808 7833528576 88507 _ _ (1139083 / 50000) (445393 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833495808 7833528576 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833528576 :
    ThetaLowerSegment 7833528576 7833561344 (783200799981911 / 100000)
      (783204121547939 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833528576 33 20 (1139083 / 50000)
        (2278169 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833528576 7833561344 88507 _ _ (1139083 / 50000) (445393 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833528576 7833561344 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833561344 :
    ThetaLowerSegment 7833561344 7833594112 (783204121547939 / 100000) (19580185223573 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833561344 33 20 (2278167 / 100000)
        (227817 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833561344 7833594112 88507 _ _ (2278167 / 100000) (890787 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833561344 7833594112 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833594112 :
    ThetaLowerSegment 7833594112 7833626880 (19580185223573 / 2500) (783210778351913 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833594112 33 20 (2278167 / 100000)
        (227817 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833594112 7833626880 88507 _ _ (2278167 / 100000) (890787 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833594112 7833626880 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833626880 :
    ThetaLowerSegment 7833626880 7833659648 (783210778351913 / 100000)
      (783214063470169 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833626880 33 20 (284771 / 12500)
        (2278171 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833626880 7833659648 88507 _ _ (284771 / 12500) (71263 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833626880 7833659648 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833659648 :
    ThetaLowerSegment 7833659648 7833692416 (783214063470169 / 100000)
      (783217353144761 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833659648 33 20 (284771 / 12500)
        (2278171 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833659648 7833692416 88507 _ _ (284771 / 12500) (71263 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833659648 7833692416 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833692416 :
    ThetaLowerSegment 7833692416 7833725184 (783217353144761 / 100000)
      (783220645097521 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833692416 33 20 (284771 / 12500)
        (2278171 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833692416 7833725184 88508 _ _ (284771 / 12500) (71263 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833692416 7833725184 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833725184 :
    ThetaLowerSegment 7833725184 7833757952 (783220645097521 / 100000)
      (391611922962483 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833725184 33 20 (2278169 / 100000)
        (569543 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833725184 7833757952 88508 _ _ (2278169 / 100000) (1781577 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833725184 7833757952 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833757952 :
    ThetaLowerSegment 7833757952 7833790720 (391611922962483 / 50000)
      (783226982963679 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833757952 33 20 (2278169 / 100000)
        (569543 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833757952 7833790720 88508 _ _ (2278169 / 100000) (1781577 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833757952 7833790720 12 1377 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833790720 :
    ThetaLowerSegment 7833790720 7833823488 (783226982963679 / 100000)
      (783230258972139 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833790720 33 20 (227817 / 10000)
        (2278173 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833790720 7833823488 88508 _ _ (227817 / 10000) (1781579 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833790720 7833823488 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833823488 :
    ThetaLowerSegment 7833823488 7833856256 (783230258972139 / 100000)
      (783233598769359 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833823488 33 20 (227817 / 10000)
        (2278173 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833823488 7833856256 88508 _ _ (227817 / 10000) (1781579 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833823488 7833856256 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833856256 :
    ThetaLowerSegment 7833856256 7833889024 (783233598769359 / 100000)
      (783236934011703 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833856256 33 20 (2278171 / 100000)
        (1139087 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833856256 7833889024 88509 _ _ (2278171 / 100000) (89079 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833856256 7833889024 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833889024 :
    ThetaLowerSegment 7833889024 7833921792 (783236934011703 / 100000)
      (195810043962259 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833889024 33 20 (2278171 / 100000)
        (1139087 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833889024 7833921792 88509 _ _ (2278171 / 100000) (89079 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833889024 7833921792 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833921792 :
    ThetaLowerSegment 7833921792 7833954560 (195810043962259 / 25000)
      (783243417686369 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833921792 33 20 (2278171 / 100000)
        (1139087 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833921792 7833954560 88509 _ _ (2278171 / 100000) (89079 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833921792 7833954560 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833954560 :
    ThetaLowerSegment 7833954560 7833987328 (783243417686369 / 100000)
      (783246677750501 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833954560 33 20 (569543 / 25000) (91127 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833954560 7833987328 88509 _ _ (569543 / 25000) (890791 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833954560 7833987328 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7833987328 :
    ThetaLowerSegment 7833987328 7834020096 (783246677750501 / 100000) (31329998514981 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7833987328 33 20 (569543 / 25000) (91127 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7833987328 7834020096 88509 _ _ (569543 / 25000) (890791 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7833987328 7834020096 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834020096 :
    ThetaLowerSegment 7834020096 7834052864 (31329998514981 / 4000) (783253079415189 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834020096 33 20 (2278173 / 100000)
        (71193 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834020096 7834052864 88509 _ _ (2278173 / 100000) (111349 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834020096 7834052864 12 1368 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834052864 :
    ThetaLowerSegment 7834052864 7834085632 (783253079415189 / 100000)
      (78325635314979 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834052864 33 20 (2278173 / 100000)
        (71193 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834052864 7834085632 88510 _ _ (2278173 / 100000) (111349 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834052864 7834085632 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834085632 :
    ThetaLowerSegment 7834085632 7834118400 (78325635314979 / 10000) (78325967928383 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834085632 33 20 (1139087 / 50000)
        (2278177 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834085632 7834118400 88510 _ _ (1139087 / 50000) (356317 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834085632 7834118400 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834118400 :
    ThetaLowerSegment 7834118400 7834151168 (78325967928383 / 10000) (195815717751401 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834118400 33 20 (1139087 / 50000)
        (2278177 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834118400 7834151168 88510 _ _ (1139087 / 50000) (356317 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834118400 7834151168 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834151168 :
    ThetaLowerSegment 7834151168 7834183936 (195815717751401 / 25000) (48954138175543 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834151168 33 20 (1139087 / 50000)
        (2278177 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834151168 7834183936 88510 _ _ (1139087 / 50000) (356317 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834151168 7834183936 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834183936 :
    ThetaLowerSegment 7834183936 7834216704 (48954138175543 / 6250) (195817379679697 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834183936 33 20 (91127 / 4000)
        (1139089 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834183936 7834216704 88510 _ _ (91127 / 4000) (1781587 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834183936 7834216704 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834216704 :
    ThetaLowerSegment 7834216704 7834249472 (195817379679697 / 25000)
      (783272801568963 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834216704 33 20 (91127 / 4000)
        (1139089 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834216704 7834249472 88511 _ _ (91127 / 4000) (1781587 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834216704 7834249472 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834249472 :
    ThetaLowerSegment 7834249472 7834282240 (783272801568963 / 100000)
      (783275970511779 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834249472 33 20 (71193 / 3125)
        (2278179 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834249472 7834282240 88511 _ _ (71193 / 3125) (445397 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834249472 7834282240 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834282240 :
    ThetaLowerSegment 7834282240 7834315008 (783275970511779 / 100000)
      (156655855229031 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834282240 33 20 (71193 / 3125)
        (2278179 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834282240 7834315008 88511 _ _ (71193 / 3125) (445397 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834282240 7834315008 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834315008 :
    ThetaLowerSegment 7834315008 7834347776 (156655855229031 / 20000)
      (783282588613059 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834315008 33 20 (71193 / 3125)
        (2278179 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834315008 7834347776 88511 _ _ (71193 / 3125) (445397 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834315008 7834347776 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834347776 :
    ThetaLowerSegment 7834347776 7834380544 (783282588613059 / 100000)
      (391642947123943 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834347776 33 20 (2278177 / 100000)
        (113909 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834347776 7834380544 88511 _ _ (2278177 / 100000) (178159 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834347776 7834380544 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834380544 :
    ThetaLowerSegment 7834380544 7834413312 (391642947123943 / 50000)
      (783289163431881 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834380544 33 20 (2278177 / 100000)
        (113909 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834380544 7834413312 88512 _ _ (2278177 / 100000) (178159 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834380544 7834413312 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834413312 :
    ThetaLowerSegment 7834413312 7834446080 (783289163431881 / 100000)
      (156658467386767 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834413312 33 20 (1139089 / 50000)
        (2278181 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834413312 7834446080 88512 _ _ (1139089 / 50000) (222699 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834413312 7834446080 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834446080 :
    ThetaLowerSegment 7834446080 7834478848 (156658467386767 / 20000)
      (783295585615663 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834446080 33 20 (1139089 / 50000)
        (2278181 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834446080 7834478848 88512 _ _ (1139089 / 50000) (222699 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834446080 7834478848 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834478848 :
    ThetaLowerSegment 7834478848 7834511616 (783295585615663 / 100000)
      (391649498024813 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834478848 33 20 (2278179 / 100000)
        (1139091 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834478848 7834511616 88512 _ _ (2278179 / 100000) (1781593 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834478848 7834511616 12 1497 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834511616 :
    ThetaLowerSegment 7834511616 7834544384 (391649498024813 / 50000) (97912778313431 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834511616 33 20 (2278179 / 100000)
        (1139091 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834511616 7834544384 88512 _ _ (2278179 / 100000) (1781593 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834511616 7834544384 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834544384 :
    ThetaLowerSegment 7834544384 7834577152 (97912778313431 / 12500) (97913197498367 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834544384 33 20 (2278179 / 100000)
        (1139091 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834544384 7834577152 88512 _ _ (2278179 / 100000) (1781593 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834544384 7834577152 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834577152 :
    ThetaLowerSegment 7834577152 7834609920 (97913197498367 / 12500) (195827204320179 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834577152 33 20 (113909 / 5000)
        (2278183 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834577152 7834609920 88513 _ _ (113909 / 5000) (356319 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834577152 7834609920 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834609920 :
    ThetaLowerSegment 7834609920 7834642688 (195827204320179 / 25000)
      (195828013074079 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834609920 33 20 (113909 / 5000)
        (2278183 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834609920 7834642688 88513 _ _ (113909 / 5000) (356319 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834609920 7834642688 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834642688 :
    ThetaLowerSegment 7834642688 7834675456 (195828013074079 / 25000)
      (391657677829383 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834642688 33 20 (2278181 / 100000)
        (284773 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834642688 7834675456 88513 _ _ (2278181 / 100000) (1781597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834642688 7834675456 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834675456 :
    ThetaLowerSegment 7834675456 7834708224 (391657677829383 / 50000)
      (391659354570599 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834675456 33 20 (2278181 / 100000)
        (284773 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834675456 7834708224 88513 _ _ (2278181 / 100000) (1781597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834675456 7834708224 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834708224 :
    ThetaLowerSegment 7834708224 7834740992 (391659354570599 / 50000) (15666437607383 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834708224 33 20 (2278181 / 100000)
        (284773 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834708224 7834740992 88513 _ _ (2278181 / 100000) (1781597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834708224 7834740992 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834740992 :
    ThetaLowerSegment 7834740992 7834773760 (15666437607383 / 2000) (24478913201942 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834740992 33 20 (1139091 / 50000)
        (455637 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834740992 7834773760 88514 _ _ (1139091 / 50000) (890799 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834740992 7834773760 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834773760 :
    ThetaLowerSegment 7834773760 7834806528 (24478913201942 / 3125) (391664248104839 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834773760 33 20 (1139091 / 50000)
        (455637 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834773760 7834806528 88514 _ _ (1139091 / 50000) (890799 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834773760 7834806528 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834806528 :
    ThetaLowerSegment 7834806528 7834839296 (391664248104839 / 50000)
      (195832936224659 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834806528 33 20 (2278183 / 100000)
        (1139093 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834806528 7834839296 88514 _ _ (2278183 / 100000) (2227 / 125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834806528 7834839296 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834839296 :
    ThetaLowerSegment 7834839296 7834872064 (195832936224659 / 25000)
      (391667496793797 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834839296 33 20 (2278183 / 100000)
        (1139093 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834839296 7834872064 88514 _ _ (2278183 / 100000) (2227 / 125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834839296 7834872064 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834872064 :
    ThetaLowerSegment 7834872064 7834904832 (391667496793797 / 50000) (78333830606713 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834872064 33 20 (284773 / 12500)
        (2278187 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834872064 7834904832 88514 _ _ (284773 / 12500) (890801 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834872064 7834904832 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834904832 :
    ThetaLowerSegment 7834904832 7834937600 (78333830606713 / 10000) (391670760292377 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834904832 33 20 (284773 / 12500)
        (2278187 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834904832 7834937600 88514 _ _ (284773 / 12500) (890801 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834904832 7834937600 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834937600 :
    ThetaLowerSegment 7834937600 7834970368 (391670760292377 / 50000)
      (391672451843997 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834937600 33 20 (284773 / 12500)
        (2278187 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834937600 7834970368 88515 _ _ (284773 / 12500) (890801 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834937600 7834970368 12 1485 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7834970368 :
    ThetaLowerSegment 7834970368 7835003136 (391672451843997 / 50000)
      (783348209334429 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7834970368 33 20 (455637 / 20000)
        (569547 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7834970368 7835003136 88515 _ _ (455637 / 20000) (1781603 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7834970368 7835003136 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835003136 :
    ThetaLowerSegment 7835003136 7835035904 (783348209334429 / 100000)
      (391675746099507 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835003136 33 20 (455637 / 20000)
        (569547 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835003136 7835035904 88515 _ _ (455637 / 20000) (1781603 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835003136 7835035904 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835035904 :
    ThetaLowerSegment 7835035904 7835068672 (391675746099507 / 50000)
      (391677352220637 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835035904 33 20 (1139093 / 50000)
        (2278189 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835035904 7835068672 88515 _ _ (1139093 / 50000) (356321 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835035904 7835068672 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835068672 :
    ThetaLowerSegment 7835068672 7835101440 (391677352220637 / 50000) (19583950252229 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835068672 33 20 (1139093 / 50000)
        (2278189 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835068672 7835101440 88515 _ _ (1139093 / 50000) (356321 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835068672 7835101440 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835101440 :
    ThetaLowerSegment 7835101440 7835134208 (19583950252229 / 2500) (48960076680487 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835101440 33 20 (1139093 / 50000)
        (2278189 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835101440 7835134208 88516 _ _ (1139093 / 50000) (356321 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835101440 7835134208 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835134208 :
    ThetaLowerSegment 7835134208 7835166976 (48960076680487 / 6250) (783364445966023 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835134208 33 20 (2278187 / 100000)
        (227819 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835134208 7835166976 88516 _ _ (2278187 / 100000) (1781607 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835134208 7835166976 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835166976 :
    ThetaLowerSegment 7835166976 7835199744 (783364445966023 / 100000)
      (783367804013661 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835166976 33 20 (2278187 / 100000)
        (227819 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835166976 7835199744 88516 _ _ (2278187 / 100000) (1781607 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835166976 7835199744 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835199744 :
    ThetaLowerSegment 7835199744 7835232512 (783367804013661 / 100000)
      (783371059544313 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835199744 33 20 (569547 / 25000)
        (2278191 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835199744 7835232512 88516 _ _ (569547 / 25000) (222701 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835199744 7835232512 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835232512 :
    ThetaLowerSegment 7835232512 7835265280 (783371059544313 / 100000)
      (783374483660877 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835232512 33 20 (569547 / 25000)
        (2278191 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835232512 7835265280 88516 _ _ (569547 / 25000) (222701 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835232512 7835265280 12 1503 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835265280 :
    ThetaLowerSegment 7835265280 7835298048 (783374483660877 / 100000)
      (783377864493353 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835265280 33 20 (2278189 / 100000)
        (142387 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835265280 7835298048 88517 _ _ (2278189 / 100000) (178161 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835265280 7835298048 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835298048 :
    ThetaLowerSegment 7835298048 7835330816 (783377864493353 / 100000)
      (391690578238229 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835298048 33 20 (2278189 / 100000)
        (142387 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835298048 7835330816 88517 _ _ (2278189 / 100000) (178161 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835298048 7835330816 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835330816 :
    ThetaLowerSegment 7835330816 7835363584 (391690578238229 / 50000) (1253414964441 / 160) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835330816 33 20 (2278189 / 100000)
        (142387 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835330816 7835363584 88517 _ _ (2278189 / 100000) (178161 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835330816 7835363584 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835363584 :
    ThetaLowerSegment 7835363584 7835396352 (1253414964441 / 160) (6267101249209 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835363584 33 20 (227819 / 10000)
        (2278193 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835363584 7835396352 88517 _ _ (227819 / 10000) (445403 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835363584 7835396352 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835396352 :
    ThetaLowerSegment 7835396352 7835429120 (6267101249209 / 800) (156678177780547 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835396352 33 20 (227819 / 10000)
        (2278193 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835396352 7835429120 88517 _ _ (227819 / 10000) (445403 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835396352 7835429120 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835429120 :
    ThetaLowerSegment 7835429120 7835461888 (156678177780547 / 20000) (24481067725612 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835429120 33 20 (2278191 / 100000)
        (1139097 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835429120 7835461888 88517 _ _ (2278191 / 100000) (1781613 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835429120 7835461888 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835461888 :
    ThetaLowerSegment 7835461888 7835494656 (24481067725612 / 3125) (783397509325781 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835461888 33 20 (2278191 / 100000)
        (1139097 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835461888 7835494656 88518 _ _ (2278191 / 100000) (1781613 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835461888 7835494656 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835494656 :
    ThetaLowerSegment 7835494656 7835527424 (783397509325781 / 100000)
      (78340069651499 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835494656 33 20 (2278191 / 100000)
        (1139097 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835494656 7835527424 88518 _ _ (2278191 / 100000) (1781613 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835494656 7835527424 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835527424 :
    ThetaLowerSegment 7835527424 7835560192 (78340069651499 / 10000) (391701997668503 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835527424 33 20 (142387 / 6250)
        (455639 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835527424 7835560192 88518 _ _ (142387 / 6250) (356323 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835527424 7835560192 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835560192 :
    ThetaLowerSegment 7835560192 7835592960 (391701997668503 / 50000)
      (391703639105839 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835560192 33 20 (142387 / 6250)
        (455639 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835560192 7835592960 88518 _ _ (142387 / 6250) (356323 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835560192 7835592960 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835592960 :
    ThetaLowerSegment 7835592960 7835625728 (391703639105839 / 50000) (78341052235851 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835592960 33 20 (2278193 / 100000)
        (569549 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835592960 7835625728 88518 _ _ (2278193 / 100000) (1781617 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835592960 7835625728 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835625728 :
    ThetaLowerSegment 7835625728 7835658496 (78341052235851 / 10000) (156682758313093 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835625728 33 20 (2278193 / 100000)
        (569549 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835625728 7835658496 88519 _ _ (2278193 / 100000) (1781617 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835625728 7835658496 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835658496 :
    ThetaLowerSegment 7835658496 7835691264 (156682758313093 / 20000)
      (783417165570779 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835658496 33 20 (1139097 / 50000)
        (2278197 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835658496 7835691264 88519 _ _ (1139097 / 50000) (890809 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835658496 7835691264 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835691264 :
    ThetaLowerSegment 7835691264 7835724032 (783417165570779 / 100000) (31336819578233 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835691264 33 20 (1139097 / 50000)
        (2278197 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835691264 7835724032 88519 _ _ (1139097 / 50000) (890809 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835691264 7835724032 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835724032 :
    ThetaLowerSegment 7835724032 7835756800 (31336819578233 / 4000) (783423751829633 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835724032 33 20 (1139097 / 50000)
        (2278197 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835724032 7835756800 88519 _ _ (1139097 / 50000) (890809 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835724032 7835756800 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835756800 :
    ThetaLowerSegment 7835756800 7835789568 (783423751829633 / 100000)
      (783427068881553 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835756800 33 20 (455639 / 20000)
        (1139099 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835756800 7835789568 88519 _ _ (455639 / 20000) (89081 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835756800 7835789568 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835789568 :
    ThetaLowerSegment 7835789568 7835822336 (783427068881553 / 100000)
      (195857574270967 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835789568 33 20 (455639 / 20000)
        (1139099 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835789568 7835822336 88519 _ _ (455639 / 20000) (89081 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835789568 7835822336 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835822336 :
    ThetaLowerSegment 7835822336 7835855104 (195857574270967 / 25000)
      (195858394421527 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835822336 33 20 (569549 / 25000)
        (2278199 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835822336 7835855104 88520 _ _ (569549 / 25000) (1781621 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835822336 7835855104 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835855104 :
    ThetaLowerSegment 7835855104 7835887872 (195858394421527 / 25000)
      (195859223684871 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835855104 33 20 (569549 / 25000)
        (2278199 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835855104 7835887872 88520 _ _ (569549 / 25000) (1781621 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835855104 7835887872 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835887872 :
    ThetaLowerSegment 7835887872 7835920640 (195859223684871 / 25000)
      (783440173064967 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835887872 33 20 (2278197 / 100000)
        (11391 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835887872 7835920640 88520 _ _ (2278197 / 100000) (1781623 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835887872 7835920640 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835920640 :
    ThetaLowerSegment 7835920640 7835953408 (783440173064967 / 100000)
      (783443481007011 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835920640 33 20 (2278197 / 100000)
        (11391 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835920640 7835953408 88520 _ _ (2278197 / 100000) (1781623 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835920640 7835953408 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835953408 :
    ThetaLowerSegment 7835953408 7835986176 (783443481007011 / 100000)
      (783446807174631 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835953408 33 20 (2278197 / 100000)
        (11391 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835953408 7835986176 88520 _ _ (2278197 / 100000) (1781623 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835953408 7835986176 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7835986176 :
    ThetaLowerSegment 7835986176 7836018944 (783446807174631 / 100000)
      (783449939696881 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7835986176 33 20 (1139099 / 50000)
        (2278201 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7835986176 7836018944 88521 _ _ (1139099 / 50000) (14253 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7835986176 7836018944 12 1375 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836018944 :
    ThetaLowerSegment 7836018944 7836051712 (783449939696881 / 100000)
      (783453186129031 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836018944 33 20 (1139099 / 50000)
        (2278201 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836018944 7836051712 88521 _ _ (1139099 / 50000) (14253 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836018944 7836051712 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836051712 :
    ThetaLowerSegment 7836051712 7836084480 (783453186129031 / 100000)
      (783456430284407 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836051712 33 20 (2278199 / 100000)
        (1139101 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836051712 7836084480 88521 _ _ (2278199 / 100000) (890813 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836051712 7836084480 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836084480 :
    ThetaLowerSegment 7836084480 7836117248 (783456430284407 / 100000)
      (783459619763007 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836084480 33 20 (2278199 / 100000)
        (1139101 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836084480 7836117248 88521 _ _ (2278199 / 100000) (890813 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836084480 7836117248 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836117248 :
    ThetaLowerSegment 7836117248 7836150016 (783459619763007 / 100000)
      (783462868474781 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836117248 33 20 (2278199 / 100000)
        (1139101 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836117248 7836150016 88521 _ _ (2278199 / 100000) (890813 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836117248 7836150016 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836150016 :
    ThetaLowerSegment 7836150016 7836182784 (783462868474781 / 100000)
      (783466219706981 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836150016 33 20 (11391 / 500)
        (2278203 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836150016 7836182784 88522 _ _ (11391 / 500) (445407 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836150016 7836182784 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836182784 :
    ThetaLowerSegment 7836182784 7836215552 (783466219706981 / 100000)
      (783469393239581 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836182784 33 20 (11391 / 500)
        (2278203 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836182784 7836215552 88522 _ _ (11391 / 500) (445407 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836182784 7836215552 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836215552 :
    ThetaLowerSegment 7836215552 7836248320 (783469393239581 / 100000)
      (391736342620013 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836215552 33 20 (2278201 / 100000)
        (569551 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836215552 7836248320 88522 _ _ (2278201 / 100000) (178163 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836215552 7836248320 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836248320 :
    ThetaLowerSegment 7836248320 7836281088 (391736342620013 / 50000)
      (783475945345657 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836248320 33 20 (2278201 / 100000)
        (569551 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836248320 7836281088 88522 _ _ (2278201 / 100000) (178163 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836248320 7836281088 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836281088 :
    ThetaLowerSegment 7836281088 7836313856 (783475945345657 / 100000)
      (783479171279689 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836281088 33 20 (1139101 / 50000)
        (455641 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836281088 7836313856 88522 _ _ (1139101 / 50000) (1781631 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836281088 7836313856 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836313856 :
    ThetaLowerSegment 7836313856 7836346624 (783479171279689 / 100000)
      (783482449612367 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836313856 33 20 (1139101 / 50000)
        (455641 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836313856 7836346624 88522 _ _ (1139101 / 50000) (1781631 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836313856 7836346624 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836346624 :
    ThetaLowerSegment 7836346624 7836379392 (783482449612367 / 100000)
      (156697166092827 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836346624 33 20 (1139101 / 50000)
        (455641 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836346624 7836379392 88523 _ _ (1139101 / 50000) (1781631 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836346624 7836379392 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836379392 :
    ThetaLowerSegment 7836379392 7836412160 (156697166092827 / 20000) (78348907690341 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836379392 33 20 (2278203 / 100000)
        (1139103 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836379392 7836412160 88523 _ _ (2278203 / 100000) (1781633 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836379392 7836412160 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836412160 :
    ThetaLowerSegment 7836412160 7836444928 (78348907690341 / 10000)
      (783492373463151 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836412160 33 20 (2278203 / 100000)
        (1139103 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836412160 7836444928 88523 _ _ (2278203 / 100000) (1781633 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836412160 7836444928 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836444928 :
    ThetaLowerSegment 7836444928 7836477696 (783492373463151 / 100000)
      (783495745205071 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836444928 33 20 (569551 / 25000)
        (2278207 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836444928 7836477696 88523 _ _ (569551 / 25000) (356327 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836444928 7836477696 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836477696 :
    ThetaLowerSegment 7836477696 7836510464 (783495745205071 / 100000)
      (783499000758587 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836477696 33 20 (569551 / 25000)
        (2278207 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836477696 7836510464 88523 _ _ (569551 / 25000) (356327 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836477696 7836510464 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836510464 :
    ThetaLowerSegment 7836510464 7836543232 (783499000758587 / 100000)
      (783502374778711 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836510464 33 20 (569551 / 25000)
        (2278207 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836510464 7836543232 88524 _ _ (569551 / 25000) (356327 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836510464 7836543232 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836543232 :
    ThetaLowerSegment 7836543232 7836576000 (783502374778711 / 100000)
      (391752863009133 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836543232 33 20 (455641 / 20000) (71194 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836543232 7836576000 88524 _ _ (455641 / 20000) (445409 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836543232 7836576000 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836576000 :
    ThetaLowerSegment 7836576000 7836608768 (391752863009133 / 50000)
      (783509027137311 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836576000 33 20 (455641 / 20000) (71194 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836576000 7836608768 88524 _ _ (455641 / 20000) (445409 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836576000 7836608768 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836608768 :
    ThetaLowerSegment 7836608768 7836641536 (783509027137311 / 100000)
      (783512269024449 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836608768 33 20 (1139103 / 50000)
        (2278209 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836608768 7836641536 88524 _ _ (1139103 / 50000) (890819 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836608768 7836641536 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836641536 :
    ThetaLowerSegment 7836641536 7836674304 (783512269024449 / 100000)
      (783515668107801 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836641536 33 20 (1139103 / 50000)
        (2278209 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836641536 7836674304 88524 _ _ (1139103 / 50000) (890819 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836641536 7836674304 12 1492 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836674304 :
    ThetaLowerSegment 7836674304 7836707072 (783515668107801 / 100000)
      (195879749142057 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836674304 33 20 (2278207 / 100000)
        (227821 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836674304 7836707072 88524 _ _ (2278207 / 100000) (44541 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836674304 7836707072 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836707072 :
    ThetaLowerSegment 7836707072 7836739840 (195879749142057 / 25000)
      (783522320472241 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836707072 33 20 (2278207 / 100000)
        (227821 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836707072 7836739840 88525 _ _ (2278207 / 100000) (44541 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836707072 7836739840 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836739840 :
    ThetaLowerSegment 7836739840 7836772608 (783522320472241 / 100000)
      (391762790293229 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836739840 33 20 (2278207 / 100000)
        (227821 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836739840 7836772608 88525 _ _ (2278207 / 100000) (44541 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836739840 7836772608 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836772608 :
    ThetaLowerSegment 7836772608 7836805376 (391762790293229 / 50000)
      (391764416933741 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836772608 33 20 (71194 / 3125)
        (2278211 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836772608 7836805376 88525 _ _ (71194 / 3125) (1781641 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836772608 7836805376 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836805376 :
    ThetaLowerSegment 7836805376 7836838144 (391764416933741 / 50000)
      (391766026487693 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836805376 33 20 (71194 / 3125)
        (2278211 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836805376 7836838144 88525 _ _ (71194 / 3125) (1781641 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836805376 7836838144 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836838144 :
    ThetaLowerSegment 7836838144 7836870912 (391766026487693 / 50000)
      (783535276641121 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836838144 33 20 (2278209 / 100000)
        (569553 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836838144 7836870912 88525 _ _ (2278209 / 100000) (1781643 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836838144 7836870912 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836870912 :
    ThetaLowerSegment 7836870912 7836903680 (783535276641121 / 100000)
      (78353860510447 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836870912 33 20 (2278209 / 100000)
        (569553 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836870912 7836903680 88526 _ _ (2278209 / 100000) (1781643 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836870912 7836903680 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836903680 :
    ThetaLowerSegment 7836903680 7836936448 (78353860510447 / 10000) (78354193128961 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836903680 33 20 (2278209 / 100000)
        (569553 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836903680 7836936448 88526 _ _ (2278209 / 100000) (1781643 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836903680 7836936448 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836936448 :
    ThetaLowerSegment 7836936448 7836969216 (78354193128961 / 10000) (39177264810289 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836936448 33 20 (227821 / 10000)
        (2278213 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836936448 7836969216 88526 _ _ (227821 / 10000) (356329 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836936448 7836969216 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7836969216 :
    ThetaLowerSegment 7836969216 7837001984 (39177264810289 / 5000) (78354848797799 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7836969216 33 20 (227821 / 10000)
        (2278213 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7836969216 7837001984 88526 _ _ (227821 / 10000) (356329 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7836969216 7837001984 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837001984 :
    ThetaLowerSegment 7837001984 7837034752 (78354848797799 / 10000)
      (783551798218573 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837001984 33 20 (2278211 / 100000)
        (1139107 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837001984 7837034752 88526 _ _ (2278211 / 100000) (890823 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837001984 7837034752 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837034752 :
    ThetaLowerSegment 7837034752 7837067520 (783551798218573 / 100000)
      (156711025792611 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837034752 33 20 (2278211 / 100000)
        (1139107 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837034752 7837067520 88527 _ _ (2278211 / 100000) (890823 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837034752 7837067520 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837067520 :
    ThetaLowerSegment 7837067520 7837100288 (156711025792611 / 20000) (31342338206103 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837067520 33 20 (569553 / 25000)
        (455643 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837067520 7837100288 88527 _ _ (569553 / 25000) (111353 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837067520 7837100288 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837100288 :
    ThetaLowerSegment 7837100288 7837133056 (31342338206103 / 4000) (156712353990207 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837100288 33 20 (569553 / 25000)
        (455643 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837100288 7837133056 88527 _ _ (569553 / 25000) (111353 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837100288 7837133056 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837133056 :
    ThetaLowerSegment 7837133056 7837165824 (156712353990207 / 20000)
      (783565077914859 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837133056 33 20 (569553 / 25000)
        (455643 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837133056 7837165824 88527 _ _ (569553 / 25000) (111353 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837133056 7837165824 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837165824 :
    ThetaLowerSegment 7837165824 7837198592 (783565077914859 / 100000)
      (195892069701031 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837165824 33 20 (2278213 / 100000)
        (284777 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837165824 7837198592 88527 _ _ (2278213 / 100000) (35633 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837165824 7837198592 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837198592 :
    ThetaLowerSegment 7837198592 7837231360 (195892069701031 / 25000)
      (783571639168299 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837198592 33 20 (2278213 / 100000)
        (284777 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837198592 7837231360 88527 _ _ (2278213 / 100000) (35633 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837198592 7837231360 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837231360 :
    ThetaLowerSegment 7837231360 7837264128 (783571639168299 / 100000)
      (783574878788607 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837231360 33 20 (1139107 / 50000)
        (2278217 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837231360 7837264128 88528 _ _ (1139107 / 50000) (1781651 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837231360 7837264128 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837264128 :
    ThetaLowerSegment 7837264128 7837296896 (783574878788607 / 100000)
      (783578211815689 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837264128 33 20 (1139107 / 50000)
        (2278217 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837264128 7837296896 88528 _ _ (1139107 / 50000) (1781651 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837264128 7837296896 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837296896 :
    ThetaLowerSegment 7837296896 7837329664 (783578211815689 / 100000) (250746102369 / 32) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837296896 33 20 (1139107 / 50000)
        (2278217 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837296896 7837329664 88528 _ _ (1139107 / 50000) (1781651 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837296896 7837329664 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837329664 :
    ThetaLowerSegment 7837329664 7837362432 (250746102369 / 32) (39179238995403 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837329664 33 20 (455643 / 20000)
        (1139109 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837329664 7837362432 88528 _ _ (455643 / 20000) (1781653 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837329664 7837362432 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837362432 :
    ThetaLowerSegment 7837362432 7837395200 (39179238995403 / 5000) (979485064281 / 125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837362432 33 20 (455643 / 20000)
        (1139109 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837362432 7837395200 88528 _ _ (455643 / 20000) (1781653 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837362432 7837395200 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837395200 :
    ThetaLowerSegment 7837395200 7837427968 (979485064281 / 125) (24487231404961 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837395200 33 20 (284777 / 12500)
        (2278219 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837395200 7837427968 88529 _ _ (284777 / 12500) (890827 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837395200 7837427968 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837427968 :
    ThetaLowerSegment 7837427968 7837460736 (24487231404961 / 3125) (4897466044516 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837427968 33 20 (284777 / 12500)
        (2278219 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837427968 7837460736 88529 _ _ (284777 / 12500) (890827 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837427968 7837460736 12 1388 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837460736 :
    ThetaLowerSegment 7837460736 7837493504 (4897466044516 / 625) (783597872815427 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837460736 33 20 (2278217 / 100000)
        (113911 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837460736 7837493504 88529 _ _ (2278217 / 100000) (222707 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837460736 7837493504 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837493504 :
    ThetaLowerSegment 7837493504 7837526272 (783597872815427 / 100000)
      (783601158004341 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837493504 33 20 (2278217 / 100000)
        (113911 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837493504 7837526272 88529 _ _ (2278217 / 100000) (222707 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837493504 7837526272 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837526272 :
    ThetaLowerSegment 7837526272 7837559040 (783601158004341 / 100000)
      (97950557962151 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837526272 33 20 (2278217 / 100000)
        (113911 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837526272 7837559040 88529 _ _ (2278217 / 100000) (222707 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837526272 7837559040 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837559040 :
    ThetaLowerSegment 7837559040 7837591808 (97950557962151 / 12500) (39180384254873 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837559040 33 20 (1139109 / 50000)
        (2278221 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837559040 7837591808 88529 _ _ (1139109 / 50000) (890829 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837559040 7837591808 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837591808 :
    ThetaLowerSegment 7837591808 7837624576 (39180384254873 / 5000) (97951378120631 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837591808 33 20 (1139109 / 50000)
        (2278221 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837591808 7837624576 88530 _ _ (1139109 / 50000) (890829 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837591808 7837624576 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837624576 :
    ThetaLowerSegment 7837624576 7837657344 (97951378120631 / 12500)
      (783614207636991 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837624576 33 20 (2278219 / 100000)
        (1139111 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837624576 7837657344 88530 _ _ (2278219 / 100000) (1781659 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837624576 7837657344 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837657344 :
    ThetaLowerSegment 7837657344 7837690112 (783614207636991 / 100000)
      (391808717936657 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837657344 33 20 (2278219 / 100000)
        (1139111 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837657344 7837690112 88530 _ _ (2278219 / 100000) (1781659 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837657344 7837690112 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837690112 :
    ThetaLowerSegment 7837690112 7837722880 (391808717936657 / 50000)
      (391810371923651 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837690112 33 20 (2278219 / 100000)
        (1139111 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837690112 7837722880 88530 _ _ (2278219 / 100000) (1781659 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837690112 7837722880 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837722880 :
    ThetaLowerSegment 7837722880 7837755648 (391810371923651 / 50000)
      (391812069197551 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837722880 33 20 (113911 / 5000)
        (2278223 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837722880 7837755648 88530 _ _ (113911 / 5000) (1781661 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837722880 7837755648 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837755648 :
    ThetaLowerSegment 7837755648 7837788416 (391812069197551 / 50000)
      (391813694707521 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837755648 33 20 (113911 / 5000)
        (2278223 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837755648 7837788416 88531 _ _ (113911 / 5000) (1781661 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837755648 7837788416 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837788416 :
    ThetaLowerSegment 7837788416 7837821184 (391813694707521 / 50000)
      (391815289462221 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837788416 33 20 (2278221 / 100000)
        (142389 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837788416 7837821184 88531 _ _ (2278221 / 100000) (1781663 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837788416 7837821184 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837821184 :
    ThetaLowerSegment 7837821184 7837853952 (391815289462221 / 50000)
      (783633925631091 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837821184 33 20 (2278221 / 100000)
        (142389 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837821184 7837853952 88531 _ _ (2278221 / 100000) (1781663 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837821184 7837853952 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837853952 :
    ThetaLowerSegment 7837853952 7837886720 (783633925631091 / 100000)
      (783637156149887 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837853952 33 20 (1139111 / 50000)
        (91129 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837853952 7837886720 88531 _ _ (1139111 / 50000) (55677 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837853952 7837886720 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837886720 :
    ThetaLowerSegment 7837886720 7837919488 (783637156149887 / 100000)
      (783640370721129 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837886720 33 20 (1139111 / 50000)
        (91129 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837886720 7837919488 88531 _ _ (1139111 / 50000) (55677 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837886720 7837919488 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837919488 :
    ThetaLowerSegment 7837919488 7837952256 (783640370721129 / 100000)
      (156728752143093 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837919488 33 20 (1139111 / 50000)
        (91129 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837919488 7837952256 88532 _ _ (1139111 / 50000) (55677 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837919488 7837952256 12 1488 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837952256 :
    ThetaLowerSegment 7837952256 7837985024 (156728752143093 / 20000) (6269175966337 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837952256 33 20 (2278223 / 100000)
        (1139113 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837952256 7837985024 88532 _ _ (2278223 / 100000) (890833 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837952256 7837985024 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7837985024 :
    ThetaLowerSegment 7837985024 7838017792 (6269175966337 / 800) (391825118851727 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7837985024 33 20 (2278223 / 100000)
        (1139113 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7837985024 7838017792 88532 _ _ (2278223 / 100000) (890833 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7837985024 7838017792 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838017792 :
    ThetaLowerSegment 7838017792 7838050560 (391825118851727 / 50000)
      (391826787650807 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838017792 33 20 (142389 / 6250)
        (2278227 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838017792 7838050560 88532 _ _ (142389 / 6250) (445417 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838017792 7838050560 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838050560 :
    ThetaLowerSegment 7838050560 7838083328 (391826787650807 / 50000) (15673137073319 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838050560 33 20 (142389 / 6250)
        (2278227 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838050560 7838083328 88532 _ _ (142389 / 6250) (445417 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838050560 7838083328 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838083328 :
    ThetaLowerSegment 7838083328 7838116096 (15673137073319 / 2000) (15673201957167 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838083328 33 20 (91129 / 4000) (569557 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838083328 7838116096 88532 _ _ (91129 / 4000) (1781669 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838083328 7838116096 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838116096 :
    ThetaLowerSegment 7838116096 7838148864 (15673201957167 / 2000) (7836633921717 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838116096 33 20 (91129 / 4000) (569557 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838116096 7838148864 88533 _ _ (91129 / 4000) (1781669 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838116096 7838148864 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838148864 :
    ThetaLowerSegment 7838148864 7838181632 (7836633921717 / 1000) (15673332271637 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838148864 33 20 (91129 / 4000) (569557 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838148864 7838181632 88533 _ _ (91129 / 4000) (1781669 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838148864 7838181632 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838181632 :
    ThetaLowerSegment 7838181632 7838214400 (15673332271637 / 2000) (39183490724469 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838181632 33 20 (1139113 / 50000)
        (2278229 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838181632 7838214400 88533 _ _ (1139113 / 50000) (1781671 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838181632 7838214400 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838214400 :
    ThetaLowerSegment 7838214400 7838247168 (39183490724469 / 5000) (391836489472647 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838214400 33 20 (1139113 / 50000)
        (2278229 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838214400 7838247168 88533 _ _ (1139113 / 50000) (1781671 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838214400 7838247168 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838247168 :
    ThetaLowerSegment 7838247168 7838279936 (391836489472647 / 50000)
      (783676330217211 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838247168 33 20 (2278227 / 100000)
        (227823 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838247168 7838279936 88533 _ _ (2278227 / 100000) (1781673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838247168 7838279936 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838279936 :
    ThetaLowerSegment 7838279936 7838312704 (783676330217211 / 100000)
      (783679574412459 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838279936 33 20 (2278227 / 100000)
        (227823 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838279936 7838312704 88534 _ _ (2278227 / 100000) (1781673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838279936 7838312704 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838312704 :
    ThetaLowerSegment 7838312704 7838345472 (783679574412459 / 100000)
      (783682768486713 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838312704 33 20 (2278227 / 100000)
        (227823 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838312704 7838345472 88534 _ _ (2278227 / 100000) (1781673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838312704 7838345472 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838345472 :
    ThetaLowerSegment 7838345472 7838378240 (783682768486713 / 100000)
      (783685946614773 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838345472 33 20 (569557 / 25000)
        (2278231 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838345472 7838378240 88534 _ _ (569557 / 25000) (890837 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838345472 7838378240 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838378240 :
    ThetaLowerSegment 7838378240 7838411008 (783685946614773 / 100000)
      (783689277384109 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838378240 33 20 (569557 / 25000)
        (2278231 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838378240 7838411008 88534 _ _ (569557 / 25000) (890837 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838378240 7838411008 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838411008 :
    ThetaLowerSegment 7838411008 7838443776 (783689277384109 / 100000)
      (97961564912997 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838411008 33 20 (2278229 / 100000)
        (284779 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838411008 7838443776 88534 _ _ (2278229 / 100000) (445419 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838411008 7838443776 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838443776 :
    ThetaLowerSegment 7838443776 7838476544 (97961564912997 / 12500)
      (783695793119049 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838443776 33 20 (2278229 / 100000)
        (284779 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838443776 7838476544 88534 _ _ (2278229 / 100000) (445419 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838443776 7838476544 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838476544 :
    ThetaLowerSegment 7838476544 7838509312 (783695793119049 / 100000)
      (783698966693439 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838476544 33 20 (227823 / 10000)
        (2278233 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838476544 7838509312 88535 _ _ (227823 / 10000) (890839 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838476544 7838509312 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838509312 :
    ThetaLowerSegment 7838509312 7838542080 (783698966693439 / 100000)
      (783702258735789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838509312 33 20 (227823 / 10000)
        (2278233 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838509312 7838542080 88535 _ _ (227823 / 10000) (890839 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838509312 7838542080 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838542080 :
    ThetaLowerSegment 7838542080 7838574848 (783702258735789 / 100000)
      (783705639629109 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838542080 33 20 (227823 / 10000)
        (2278233 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838542080 7838574848 88535 _ _ (227823 / 10000) (890839 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838542080 7838574848 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838574848 :
    ThetaLowerSegment 7838574848 7838607616 (783705639629109 / 100000)
      (97963616459113 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838574848 33 20 (2278231 / 100000)
        (1139117 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838574848 7838607616 88535 _ _ (2278231 / 100000) (1781679 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838574848 7838607616 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838607616 :
    ThetaLowerSegment 7838607616 7838640384 (97963616459113 / 12500) (391856071989307 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838607616 33 20 (2278231 / 100000)
        (1139117 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838607616 7838640384 88535 _ _ (2278231 / 100000) (1781679 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838607616 7838640384 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838640384 :
    ThetaLowerSegment 7838640384 7838673152 (391856071989307 / 50000)
      (391857689534027 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838640384 33 20 (284779 / 12500)
        (455647 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838640384 7838673152 88536 _ _ (284779 / 12500) (1781681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838640384 7838673152 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838673152 :
    ThetaLowerSegment 7838673152 7838705920 (391857689534027 / 50000) (78371872351263 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838673152 33 20 (284779 / 12500)
        (455647 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838673152 7838705920 88536 _ _ (284779 / 12500) (1781681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838673152 7838705920 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838705920 :
    ThetaLowerSegment 7838705920 7838738688 (78371872351263 / 10000) (391860974744571 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838705920 33 20 (284779 / 12500)
        (455647 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838705920 7838738688 88536 _ _ (284779 / 12500) (1781681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838705920 7838738688 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838738688 :
    ThetaLowerSegment 7838738688 7838771456 (391860974744571 / 50000)
      (391862619628797 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838738688 33 20 (2278233 / 100000)
        (569559 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838738688 7838771456 88536 _ _ (2278233 / 100000) (1781683 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838738688 7838771456 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838771456 :
    ThetaLowerSegment 7838771456 7838804224 (391862619628797 / 50000) (19593216529089 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838771456 33 20 (2278233 / 100000)
        (569559 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838771456 7838804224 88536 _ _ (2278233 / 100000) (1781683 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838771456 7838804224 12 1502 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838804224 :
    ThetaLowerSegment 7838804224 7838836992 (19593216529089 / 2500) (391865951545271 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838804224 33 20 (1139117 / 50000)
        (2278237 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838804224 7838836992 88537 _ _ (1139117 / 50000) (445421 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838804224 7838836992 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838836992 :
    ThetaLowerSegment 7838836992 7838869760 (391865951545271 / 50000)
      (195933783976147 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838836992 33 20 (1139117 / 50000)
        (2278237 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838836992 7838869760 88537 _ _ (1139117 / 50000) (445421 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838836992 7838869760 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838869760 :
    ThetaLowerSegment 7838869760 7838902528 (195933783976147 / 25000)
      (783738423397693 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838869760 33 20 (455647 / 20000)
        (1139119 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838869760 7838902528 88537 _ _ (455647 / 20000) (890843 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838869760 7838902528 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838902528 :
    ThetaLowerSegment 7838902528 7838935296 (783738423397693 / 100000)
      (195935437974757 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838902528 33 20 (455647 / 20000)
        (1139119 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838902528 7838935296 88537 _ _ (455647 / 20000) (890843 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838902528 7838935296 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838935296 :
    ThetaLowerSegment 7838935296 7838968064 (195935437974757 / 25000)
      (195936258139357 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838935296 33 20 (455647 / 20000)
        (1139119 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838935296 7838968064 88537 _ _ (455647 / 20000) (890843 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838935296 7838968064 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7838968064 :
    ThetaLowerSegment 7838968064 7839000832 (195936258139357 / 25000)
      (195937057800193 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7838968064 33 20 (569559 / 25000)
        (2278239 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7838968064 7839000832 88537 _ _ (569559 / 25000) (222711 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7838968064 7839000832 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839000832 :
    ThetaLowerSegment 7839000832 7839033600 (195937057800193 / 25000)
      (195937875686917 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839000832 33 20 (569559 / 25000)
        (2278239 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839000832 7839033600 88538 _ _ (569559 / 25000) (222711 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839000832 7839033600 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839033600 :
    ThetaLowerSegment 7839033600 7839066368 (195937875686917 / 25000)
      (783754735565971 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839033600 33 20 (2278237 / 100000)
        (14239 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839033600 7839066368 88538 _ _ (2278237 / 100000) (1781689 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839033600 7839066368 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839066368 :
    ThetaLowerSegment 7839066368 7839099136 (783754735565971 / 100000)
      (391878988748611 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839066368 33 20 (2278237 / 100000)
        (14239 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839066368 7839099136 88538 _ _ (2278237 / 100000) (1781689 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839066368 7839099136 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839099136 :
    ThetaLowerSegment 7839099136 7839131904 (391878988748611 / 50000)
      (391880624522777 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839099136 33 20 (2278237 / 100000)
        (14239 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839099136 7839131904 88538 _ _ (2278237 / 100000) (1781689 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839099136 7839131904 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839131904 :
    ThetaLowerSegment 7839131904 7839164672 (391880624522777 / 50000)
      (391882253462947 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839131904 33 20 (1139119 / 50000)
        (2278241 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839131904 7839164672 88538 _ _ (1139119 / 50000) (1781691 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839131904 7839164672 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839164672 :
    ThetaLowerSegment 7839164672 7839197440 (391882253462947 / 50000) (97970979998511 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839164672 33 20 (1139119 / 50000)
        (2278241 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839164672 7839197440 88539 _ _ (1139119 / 50000) (1781691 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839164672 7839197440 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839197440 :
    ThetaLowerSegment 7839197440 7839230208 (97970979998511 / 12500) (156754211827959 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839197440 33 20 (2278239 / 100000)
        (1139121 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839197440 7839230208 88539 _ _ (2278239 / 100000) (445423 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839197440 7839230208 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839230208 :
    ThetaLowerSegment 7839230208 7839262976 (156754211827959 / 20000)
      (195943575268473 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839230208 33 20 (2278239 / 100000)
        (1139121 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839230208 7839262976 88539 _ _ (2278239 / 100000) (445423 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839230208 7839262976 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839262976 :
    ThetaLowerSegment 7839262976 7839295744 (195943575268473 / 25000)
      (195944398852233 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839262976 33 20 (14239 / 625)
        (2278243 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839262976 7839295744 88539 _ _ (14239 / 625) (890847 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839262976 7839295744 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839295744 :
    ThetaLowerSegment 7839295744 7839328512 (195944398852233 / 25000)
      (195945181997233 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839295744 33 20 (14239 / 625)
        (2278243 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839295744 7839328512 88539 _ _ (14239 / 625) (890847 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839295744 7839328512 12 1375 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839328512 :
    ThetaLowerSegment 7839328512 7839361280 (195945181997233 / 25000)
      (195945977102993 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839328512 33 20 (14239 / 625)
        (2278243 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839328512 7839361280 88539 _ _ (14239 / 625) (890847 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839328512 7839361280 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839361280 :
    ThetaLowerSegment 7839361280 7839394048 (195945977102993 / 25000)
      (391893605930711 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839361280 33 20 (2278241 / 100000)
        (569561 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839361280 7839394048 88540 _ _ (2278241 / 100000) (55678 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839361280 7839394048 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839394048 :
    ThetaLowerSegment 7839394048 7839426816 (391893605930711 / 50000)
      (195947608323549 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839394048 33 20 (2278241 / 100000)
        (569561 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839394048 7839426816 88540 _ _ (2278241 / 100000) (55678 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839394048 7839426816 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839426816 :
    ThetaLowerSegment 7839426816 7839459584 (195947608323549 / 25000) (97974230762589 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839426816 33 20 (1139121 / 50000)
        (455649 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839426816 7839459584 88540 _ _ (1139121 / 50000) (1781697 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839426816 7839459584 12 1498 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839459584 :
    ThetaLowerSegment 7839459584 7839492352 (97974230762589 / 12500) (391898571358443 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839459584 33 20 (1139121 / 50000)
        (455649 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839459584 7839492352 88540 _ _ (1139121 / 50000) (1781697 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839459584 7839492352 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839492352 :
    ThetaLowerSegment 7839492352 7839525120 (391898571358443 / 50000) (97975050929709 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839492352 33 20 (1139121 / 50000)
        (455649 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839492352 7839525120 88540 _ _ (1139121 / 50000) (1781697 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839492352 7839525120 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839525120 :
    ThetaLowerSegment 7839525120 7839557888 (97975050929709 / 12500) (97975470126421 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839525120 33 20 (2278243 / 100000)
        (1139123 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839525120 7839557888 88541 _ _ (2278243 / 100000) (1781699 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839525120 7839557888 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839557888 :
    ThetaLowerSegment 7839557888 7839590656 (97975470126421 / 12500) (391903509449429 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839557888 33 20 (2278243 / 100000)
        (1139123 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839557888 7839590656 88541 _ _ (2278243 / 100000) (1781699 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839557888 7839590656 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839590656 :
    ThetaLowerSegment 7839590656 7839623424 (391903509449429 / 50000)
      (391905145228621 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839590656 33 20 (569561 / 25000)
        (2278247 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839590656 7839623424 88541 _ _ (569561 / 25000) (1781701 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839590656 7839623424 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839623424 :
    ThetaLowerSegment 7839623424 7839656192 (391905145228621 / 50000)
      (391906814042351 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839623424 33 20 (569561 / 25000)
        (2278247 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839623424 7839656192 88541 _ _ (569561 / 25000) (1781701 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839623424 7839656192 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839656192 :
    ThetaLowerSegment 7839656192 7839688960 (391906814042351 / 50000)
      (195954212380783 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839656192 33 20 (455649 / 20000)
        (284781 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839656192 7839688960 88541 _ _ (455649 / 20000) (890851 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839656192 7839688960 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839688960 :
    ThetaLowerSegment 7839688960 7839721728 (195954212380783 / 25000)
      (783820100578747 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839688960 33 20 (455649 / 20000)
        (284781 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839688960 7839721728 88542 _ _ (455649 / 20000) (890851 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839688960 7839721728 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839721728 :
    ThetaLowerSegment 7839721728 7839754496 (783820100578747 / 100000)
      (783823340243137 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839721728 33 20 (455649 / 20000)
        (284781 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839721728 7839754496 88542 _ _ (455649 / 20000) (890851 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839721728 7839754496 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839754496 :
    ThetaLowerSegment 7839754496 7839787264 (783823340243137 / 100000) (31353061464891 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839754496 33 20 (1139123 / 50000)
        (2278249 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839754496 7839787264 88542 _ _ (1139123 / 50000) (222713 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839754496 7839787264 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839787264 :
    ThetaLowerSegment 7839787264 7839820032 (31353061464891 / 4000) (783829856026697 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839787264 33 20 (1139123 / 50000)
        (2278249 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839787264 7839820032 88542 _ _ (1139123 / 50000) (222713 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839787264 7839820032 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839820032 :
    ThetaLowerSegment 7839820032 7839852800 (783829856026697 / 100000)
      (391916603664017 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839820032 33 20 (2278247 / 100000) (9113 / 400) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839820032 7839852800 88542 _ _ (2278247 / 100000) (890853 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839820032 7839852800 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839852800 :
    ThetaLowerSegment 7839852800 7839885568 (391916603664017 / 50000)
      (783836431047539 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839852800 33 20 (2278247 / 100000) (9113 / 400) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839852800 7839885568 88542 _ _ (2278247 / 100000) (890853 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839852800 7839885568 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839885568 :
    ThetaLowerSegment 7839885568 7839918336 (783836431047539 / 100000)
      (783839768680859 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839885568 33 20 (284781 / 12500)
        (2278251 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839885568 7839918336 88543 _ _ (284781 / 12500) (1781707 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839885568 7839918336 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839918336 :
    ThetaLowerSegment 7839918336 7839951104 (783839768680859 / 100000)
      (783843142766147 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839918336 33 20 (284781 / 12500)
        (2278251 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839918336 7839951104 88543 _ _ (284781 / 12500) (1781707 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839918336 7839951104 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839951104 :
    ThetaLowerSegment 7839951104 7839983872 (783843142766147 / 100000)
      (156769287422551 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839951104 33 20 (284781 / 12500)
        (2278251 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839951104 7839983872 88543 _ _ (284781 / 12500) (1781707 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839951104 7839983872 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7839983872 :
    ThetaLowerSegment 7839983872 7840016640 (156769287422551 / 20000) (97981218426069 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7839983872 33 20 (2278249 / 100000)
        (569563 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7839983872 7840016640 88543 _ _ (2278249 / 100000) (1781709 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7839983872 7840016640 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840016640 :
    ThetaLowerSegment 7840016640 7840049408 (97981218426069 / 12500)
      (783852911896413 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840016640 33 20 (2278249 / 100000)
        (569563 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840016640 7840049408 88543 _ _ (2278249 / 100000) (1781709 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840016640 7840049408 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840049408 :
    ThetaLowerSegment 7840049408 7840082176 (783852911896413 / 100000)
      (783856244976163 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840049408 33 20 (9113 / 400) (2278253 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840049408 7840082176 88544 _ _ (9113 / 400) (1781711 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840049408 7840082176 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840082176 :
    ThetaLowerSegment 7840082176 7840114944 (783856244976163 / 100000)
      (783859527934413 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840082176 33 20 (9113 / 400) (2278253 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840082176 7840114944 88544 _ _ (9113 / 400) (1781711 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840082176 7840114944 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840114944 :
    ThetaLowerSegment 7840114944 7840147712 (783859527934413 / 100000)
      (783862881518413 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840114944 33 20 (9113 / 400) (2278253 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840114944 7840147712 88544 _ _ (9113 / 400) (1781711 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840114944 7840147712 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840147712 :
    ThetaLowerSegment 7840147712 7840180480 (783862881518413 / 100000)
      (783866171312857 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840147712 33 20 (2278251 / 100000)
        (1139127 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840147712 7840180480 88544 _ _ (2278251 / 100000) (111357 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840147712 7840180480 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840180480 :
    ThetaLowerSegment 7840180480 7840213248 (783866171312857 / 100000) (19596737040289 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840180480 33 20 (2278251 / 100000)
        (1139127 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840180480 7840213248 88544 _ _ (2278251 / 100000) (111357 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840180480 7840213248 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840213248 :
    ThetaLowerSegment 7840213248 7840246016 (19596737040289 / 2500) (97984090730301 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840213248 33 20 (569563 / 25000)
        (455651 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840213248 7840246016 88544 _ _ (569563 / 25000) (890857 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840213248 7840246016 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840246016 :
    ThetaLowerSegment 7840246016 7840278784 (97984090730301 / 12500) (195969017009523 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840246016 33 20 (569563 / 25000)
        (455651 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840246016 7840278784 88545 _ _ (569563 / 25000) (890857 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840246016 7840278784 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840278784 :
    ThetaLowerSegment 7840278784 7840311552 (195969017009523 / 25000)
      (783879337331147 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840278784 33 20 (2278253 / 100000)
        (142391 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840278784 7840311552 88545 _ _ (2278253 / 100000) (445429 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840278784 7840311552 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840311552 :
    ThetaLowerSegment 7840311552 7840344320 (783879337331147 / 100000)
      (783882531441853 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840311552 33 20 (2278253 / 100000)
        (142391 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840311552 7840344320 88545 _ _ (2278253 / 100000) (445429 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840311552 7840344320 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840344320 :
    ThetaLowerSegment 7840344320 7840377088 (783882531441853 / 100000) (39194292770649 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840344320 33 20 (2278253 / 100000)
        (142391 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840344320 7840377088 88545 _ _ (2278253 / 100000) (445429 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840344320 7840377088 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840377088 :
    ThetaLowerSegment 7840377088 7840409856 (39194292770649 / 5000) (39194456804937 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840377088 33 20 (1139127 / 50000)
        (2278257 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840377088 7840409856 88545 _ _ (1139127 / 50000) (1781717 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840377088 7840409856 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840409856 :
    ThetaLowerSegment 7840409856 7840442624 (39194456804937 / 5000) (391946211809631 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840409856 33 20 (1139127 / 50000)
        (2278257 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840409856 7840442624 88546 _ _ (1139127 / 50000) (1781717 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840409856 7840442624 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840442624 :
    ThetaLowerSegment 7840442624 7840475392 (391946211809631 / 50000)
      (783895706584717 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840442624 33 20 (455651 / 20000)
        (1139129 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840442624 7840475392 88546 _ _ (455651 / 20000) (1781719 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840442624 7840475392 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840475392 :
    ThetaLowerSegment 7840475392 7840508160 (783895706584717 / 100000)
      (783898918924267 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840475392 33 20 (455651 / 20000)
        (1139129 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840475392 7840508160 88546 _ _ (455651 / 20000) (1781719 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840475392 7840508160 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840508160 :
    ThetaLowerSegment 7840508160 7840540928 (783898918924267 / 100000)
      (783902172272407 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840508160 33 20 (455651 / 20000)
        (1139129 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840508160 7840540928 88546 _ _ (455651 / 20000) (1781719 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840508160 7840540928 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840540928 :
    ThetaLowerSegment 7840540928 7840573696 (783902172272407 / 100000)
      (783905400561159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840540928 33 20 (142391 / 6250)
        (2278259 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840540928 7840573696 88546 _ _ (142391 / 6250) (1781721 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840540928 7840573696 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840573696 :
    ThetaLowerSegment 7840573696 7840606464 (783905400561159 / 100000)
      (783908667580263 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840573696 33 20 (142391 / 6250)
        (2278259 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840573696 7840606464 88547 _ _ (142391 / 6250) (1781721 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840573696 7840606464 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840606464 :
    ThetaLowerSegment 7840606464 7840639232 (783908667580263 / 100000)
      (783911925487773 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840606464 33 20 (2278257 / 100000)
        (113913 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840606464 7840639232 88547 _ _ (2278257 / 100000) (890861 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840606464 7840639232 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840639232 :
    ThetaLowerSegment 7840639232 7840672000 (783911925487773 / 100000)
      (78391516289097 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840639232 33 20 (2278257 / 100000)
        (113913 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840639232 7840672000 88547 _ _ (2278257 / 100000) (890861 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840639232 7840672000 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840672000 :
    ThetaLowerSegment 7840672000 7840704768 (78391516289097 / 10000) (97989805163029 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840672000 33 20 (1139129 / 50000)
        (2278261 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840672000 7840704768 88547 _ _ (1139129 / 50000) (445431 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840672000 7840704768 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840704768 :
    ThetaLowerSegment 7840704768 7840737536 (97989805163029 / 12500) (391960837076167 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840704768 33 20 (1139129 / 50000)
        (2278261 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840704768 7840737536 88547 _ _ (1139129 / 50000) (445431 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840704768 7840737536 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840737536 :
    ThetaLowerSegment 7840737536 7840770304 (391960837076167 / 50000)
      (391962447804573 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840737536 33 20 (1139129 / 50000)
        (2278261 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840737536 7840770304 88547 _ _ (1139129 / 50000) (445431 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840737536 7840770304 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840770304 :
    ThetaLowerSegment 7840770304 7840803072 (391962447804573 / 50000)
      (156785649385627 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840770304 33 20 (2278259 / 100000)
        (1139131 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840770304 7840803072 88548 _ _ (2278259 / 100000) (71269 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840770304 7840803072 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840803072 :
    ThetaLowerSegment 7840803072 7840835840 (156785649385627 / 20000)
      (195982885892227 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840803072 33 20 (2278259 / 100000)
        (1139131 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840803072 7840835840 88548 _ _ (2278259 / 100000) (71269 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840803072 7840835840 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840835840 :
    ThetaLowerSegment 7840835840 7840868608 (195982885892227 / 25000) (48995926089283 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840835840 33 20 (113913 / 5000)
        (2278263 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840835840 7840868608 88548 _ _ (113913 / 5000) (1781727 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840835840 7840868608 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840868608 :
    ThetaLowerSegment 7840868608 7840901376 (48995926089283 / 6250) (195984528517687 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840868608 33 20 (113913 / 5000)
        (2278263 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840868608 7840901376 88548 _ _ (113913 / 5000) (1781727 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840868608 7840901376 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840901376 :
    ThetaLowerSegment 7840901376 7840934144 (195984528517687 / 25000)
      (195985338439117 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840901376 33 20 (113913 / 5000)
        (2278263 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840901376 7840934144 88548 _ _ (113913 / 5000) (1781727 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840901376 7840934144 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840934144 :
    ThetaLowerSegment 7840934144 7840966912 (195985338439117 / 25000)
      (195986163169599 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840934144 33 20 (2278261 / 100000)
        (284783 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840934144 7840966912 88549 _ _ (2278261 / 100000) (1781729 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840934144 7840966912 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840966912 :
    ThetaLowerSegment 7840966912 7840999680 (195986163169599 / 25000)
      (783947958435107 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840966912 33 20 (2278261 / 100000)
        (284783 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840966912 7840999680 88549 _ _ (2278261 / 100000) (1781729 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840966912 7840999680 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7840999680 :
    ThetaLowerSegment 7840999680 7841032448 (783947958435107 / 100000) (31358044917641 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7840999680 33 20 (1139131 / 50000)
        (455653 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7840999680 7841032448 88549 _ _ (1139131 / 50000) (178173 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7840999680 7841032448 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841032448 :
    ThetaLowerSegment 7841032448 7841065216 (31358044917641 / 4000) (783954442368759 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841032448 33 20 (1139131 / 50000)
        (455653 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841032448 7841065216 88549 _ _ (1139131 / 50000) (178173 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841032448 7841065216 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841065216 :
    ThetaLowerSegment 7841065216 7841097984 (783954442368759 / 100000)
      (783957759519687 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841065216 33 20 (2278263 / 100000)
        (1139133 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841065216 7841097984 88549 _ _ (2278263 / 100000) (445433 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841065216 7841097984 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841097984 :
    ThetaLowerSegment 7841097984 7841130752 (783957759519687 / 100000)
      (391980534917913 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841097984 33 20 (2278263 / 100000)
        (1139133 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841097984 7841130752 88549 _ _ (2278263 / 100000) (445433 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841097984 7841130752 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841130752 :
    ThetaLowerSegment 7841130752 7841163520 (391980534917913 / 50000)
      (783964361925861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841130752 33 20 (2278263 / 100000)
        (1139133 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841130752 7841163520 88550 _ _ (2278263 / 100000) (445433 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841130752 7841163520 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841163520 :
    ThetaLowerSegment 7841163520 7841196288 (783964361925861 / 100000)
      (783967592504213 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841163520 33 20 (284783 / 12500)
        (2278267 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841163520 7841196288 88550 _ _ (284783 / 12500) (890867 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841163520 7841196288 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841196288 :
    ThetaLowerSegment 7841196288 7841229056 (783967592504213 / 100000)
      (783970841308677 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841196288 33 20 (284783 / 12500)
        (2278267 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841196288 7841229056 88550 _ _ (284783 / 12500) (890867 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841196288 7841229056 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841229056 :
    ThetaLowerSegment 7841229056 7841261824 (783970841308677 / 100000)
      (391987030248561 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841229056 33 20 (455653 / 20000)
        (569567 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841229056 7841261824 88550 _ _ (455653 / 20000) (356347 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841229056 7841261824 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841261824 :
    ThetaLowerSegment 7841261824 7841294592 (391987030248561 / 50000)
      (195994327325753 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841261824 33 20 (455653 / 20000)
        (569567 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841261824 7841294592 88550 _ _ (455653 / 20000) (356347 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841261824 7841294592 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841294592 :
    ThetaLowerSegment 7841294592 7841327360 (195994327325753 / 25000) (24499393152861 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841294592 33 20 (455653 / 20000)
        (569567 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841294592 7841327360 88551 _ _ (455653 / 20000) (356347 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841294592 7841327360 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841327360 :
    ThetaLowerSegment 7841327360 7841360128 (24499393152861 / 3125) (24499495674831 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841327360 33 20 (1139133 / 50000)
        (2278269 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841327360 7841360128 88551 _ _ (1139133 / 50000) (1781737 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841327360 7841360128 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841360128 :
    ThetaLowerSegment 7841360128 7841392896 (24499495674831 / 3125) (391993556340087 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841360128 33 20 (1139133 / 50000)
        (2278269 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841360128 7841392896 88551 _ _ (1139133 / 50000) (1781737 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841360128 7841392896 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841392896 :
    ThetaLowerSegment 7841392896 7841425664 (391993556340087 / 50000)
      (195997581259161 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841392896 33 20 (2278267 / 100000)
        (227827 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841392896 7841425664 88551 _ _ (2278267 / 100000) (1781739 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841392896 7841425664 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841425664 :
    ThetaLowerSegment 7841425664 7841458432 (195997581259161 / 25000)
      (391996773253091 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841425664 33 20 (2278267 / 100000)
        (227827 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841425664 7841458432 88551 _ _ (2278267 / 100000) (1781739 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841425664 7841458432 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841458432 :
    ThetaLowerSegment 7841458432 7841491200 (391996773253091 / 50000)
      (391998451197473 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841458432 33 20 (569567 / 25000)
        (2278271 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841458432 7841491200 88552 _ _ (569567 / 25000) (89087 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841458432 7841491200 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841491200 :
    ThetaLowerSegment 7841491200 7841523968 (391998451197473 / 50000)
      (392000114333113 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841491200 33 20 (569567 / 25000)
        (2278271 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841491200 7841523968 88552 _ _ (569567 / 25000) (89087 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841491200 7841523968 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841523968 :
    ThetaLowerSegment 7841523968 7841556736 (392000114333113 / 50000)
      (392001733042527 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841523968 33 20 (569567 / 25000)
        (2278271 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841523968 7841556736 88552 _ _ (569567 / 25000) (89087 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841523968 7841556736 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841556736 :
    ThetaLowerSegment 7841556736 7841589504 (392001733042527 / 50000)
      (392003405291973 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841556736 33 20 (2278269 / 100000)
        (71196 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841556736 7841589504 88552 _ _ (2278269 / 100000) (890871 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841556736 7841589504 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841589504 :
    ThetaLowerSegment 7841589504 7841622272 (392003405291973 / 50000)
      (392005027419501 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841589504 33 20 (2278269 / 100000)
        (71196 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841589504 7841622272 88552 _ _ (2278269 / 100000) (890871 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841589504 7841622272 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841622272 :
    ThetaLowerSegment 7841622272 7841655040 (392005027419501 / 50000) (98001671784799 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841622272 33 20 (227827 / 10000)
        (2278273 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841622272 7841655040 88552 _ _ (227827 / 10000) (111359 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841622272 7841655040 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841655040 :
    ThetaLowerSegment 7841655040 7841687808 (98001671784799 / 12500) (196004167164203 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841655040 33 20 (227827 / 10000)
        (2278273 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841655040 7841687808 88553 _ _ (227827 / 10000) (111359 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841655040 7841687808 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841687808 :
    ThetaLowerSegment 7841687808 7841720576 (196004167164203 / 25000)
      (392009978100211 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841687808 33 20 (227827 / 10000)
        (2278273 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841687808 7841720576 88553 _ _ (227827 / 10000) (111359 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841687808 7841720576 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841720576 :
    ThetaLowerSegment 7841720576 7841753344 (392009978100211 / 50000) (78402325513683 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841720576 33 20 (2278271 / 100000)
        (1139137 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841720576 7841753344 88553 _ _ (2278271 / 100000) (356349 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841720576 7841753344 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841753344 :
    ThetaLowerSegment 7841753344 7841786112 (78402325513683 / 10000) (31361061889537 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841753344 33 20 (2278271 / 100000)
        (1139137 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841753344 7841786112 88553 _ _ (2278271 / 100000) (356349 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841753344 7841786112 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841786112 :
    ThetaLowerSegment 7841786112 7841818880 (31361061889537 / 4000) (784029875793817 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841786112 33 20 (71196 / 3125) (91131 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841786112 7841818880 88553 _ _ (71196 / 3125) (1781747 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841786112 7841818880 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841818880 :
    ThetaLowerSegment 7841818880 7841851648 (784029875793817 / 100000)
      (784033047148441 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841818880 33 20 (71196 / 3125) (91131 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841818880 7841851648 88554 _ _ (71196 / 3125) (1781747 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841818880 7841851648 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841851648 :
    ThetaLowerSegment 7841851648 7841884416 (784033047148441 / 100000)
      (784036336974653 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841851648 33 20 (2278273 / 100000)
        (569569 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841851648 7841884416 88554 _ _ (2278273 / 100000) (1781749 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841851648 7841884416 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841884416 :
    ThetaLowerSegment 7841884416 7841917184 (784036336974653 / 100000)
      (196009890182737 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841884416 33 20 (2278273 / 100000)
        (569569 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841884416 7841917184 88554 _ _ (2278273 / 100000) (1781749 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841884416 7841917184 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841917184 :
    ThetaLowerSegment 7841917184 7841949952 (196009890182737 / 25000) (19601071263929 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841917184 33 20 (2278273 / 100000)
        (569569 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841917184 7841949952 88554 _ _ (2278273 / 100000) (1781749 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841917184 7841949952 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841949952 :
    ThetaLowerSegment 7841949952 7841982720 (19601071263929 / 2500) (49002881495777 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841949952 33 20 (1139137 / 50000)
        (2278277 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841949952 7841982720 88554 _ _ (1139137 / 50000) (7127 / 400) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841949952 7841982720 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7841982720 :
    ThetaLowerSegment 7841982720 7842015488 (49002881495777 / 6250) (196012340466063 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7841982720 33 20 (1139137 / 50000)
        (2278277 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7841982720 7842015488 88554 _ _ (1139137 / 50000) (7127 / 400) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7841982720 7842015488 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842015488 :
    ThetaLowerSegment 7842015488 7842048256 (196012340466063 / 25000)
      (392026273446351 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842015488 33 20 (91131 / 4000)
        (1139139 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842015488 7842048256 88555 _ _ (91131 / 4000) (222719 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842015488 7842048256 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842048256 :
    ThetaLowerSegment 7842048256 7842081024 (392026273446351 / 50000)
      (784055866339377 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842048256 33 20 (91131 / 4000)
        (1139139 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842048256 7842081024 88555 _ _ (91131 / 4000) (222719 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842048256 7842081024 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842081024 :
    ThetaLowerSegment 7842081024 7842113792 (784055866339377 / 100000)
      (784059110604401 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842081024 33 20 (569569 / 25000)
        (2278279 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842081024 7842113792 88555 _ _ (569569 / 25000) (890877 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842081024 7842113792 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842113792 :
    ThetaLowerSegment 7842113792 7842146560 (784059110604401 / 100000)
      (784062402713221 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842113792 33 20 (569569 / 25000)
        (2278279 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842113792 7842146560 88555 _ _ (569569 / 25000) (890877 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842113792 7842146560 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842146560 :
    ThetaLowerSegment 7842146560 7842179328 (784062402713221 / 100000)
      (784065697100317 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842146560 33 20 (569569 / 25000)
        (2278279 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842146560 7842179328 88555 _ _ (569569 / 25000) (890877 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842146560 7842179328 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842179328 :
    ThetaLowerSegment 7842179328 7842212096 (784065697100317 / 100000) (49004309832169 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842179328 33 20 (2278277 / 100000)
        (56957 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842179328 7842212096 88556 _ _ (2278277 / 100000) (356351 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842179328 7842212096 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842212096 :
    ThetaLowerSegment 7842212096 7842244864 (49004309832169 / 6250) (196018084569443 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842212096 33 20 (2278277 / 100000)
        (56957 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842212096 7842244864 88556 _ _ (2278277 / 100000) (356351 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842212096 7842244864 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842244864 :
    ThetaLowerSegment 7842244864 7842277632 (196018084569443 / 25000)
      (392037781020571 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842244864 33 20 (1139139 / 50000)
        (2278281 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842244864 7842277632 88556 _ _ (1139139 / 50000) (1781757 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842244864 7842277632 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842277632 :
    ThetaLowerSegment 7842277632 7842310400 (392037781020571 / 50000)
      (392039423659009 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842277632 33 20 (1139139 / 50000)
        (2278281 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842277632 7842310400 88556 _ _ (1139139 / 50000) (1781757 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842277632 7842310400 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842310400 :
    ThetaLowerSegment 7842310400 7842343168 (392039423659009 / 50000)
      (392041050349501 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842310400 33 20 (1139139 / 50000)
        (2278281 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842310400 7842343168 88556 _ _ (1139139 / 50000) (1781757 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842310400 7842343168 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842343168 :
    ThetaLowerSegment 7842343168 7842375936 (392041050349501 / 50000) (39204267020587 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842343168 33 20 (2278279 / 100000)
        (1139141 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842343168 7842375936 88557 _ _ (2278279 / 100000) (890879 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842343168 7842375936 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842375936 :
    ThetaLowerSegment 7842375936 7842408704 (39204267020587 / 5000) (784088573289641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842375936 33 20 (2278279 / 100000)
        (1139141 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842375936 7842408704 88557 _ _ (2278279 / 100000) (890879 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842375936 7842408704 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842408704 :
    ThetaLowerSegment 7842408704 7842441472 (784088573289641 / 100000)
      (784091908691561 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842408704 33 20 (56957 / 2500)
        (2278283 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842408704 7842441472 88557 _ _ (56957 / 2500) (11136 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842408704 7842441472 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842441472 :
    ThetaLowerSegment 7842441472 7842474240 (784091908691561 / 100000)
      (784095207641001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842441472 33 20 (56957 / 2500)
        (2278283 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842441472 7842474240 88557 _ _ (56957 / 2500) (11136 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842441472 7842474240 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842474240 :
    ThetaLowerSegment 7842474240 7842507008 (784095207641001 / 100000)
      (784098461026269 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842474240 33 20 (2278281 / 100000)
        (569571 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842474240 7842507008 88557 _ _ (2278281 / 100000) (890881 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842474240 7842507008 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842507008 :
    ThetaLowerSegment 7842507008 7842539776 (784098461026269 / 100000)
      (784101764533719 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842507008 33 20 (2278281 / 100000)
        (569571 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842507008 7842539776 88557 _ _ (2278281 / 100000) (890881 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842507008 7842539776 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842539776 :
    ThetaLowerSegment 7842539776 7842572544 (784101764533719 / 100000)
      (784104935900871 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842539776 33 20 (2278281 / 100000)
        (569571 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842539776 7842572544 88558 _ _ (2278281 / 100000) (890881 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842539776 7842572544 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842572544 :
    ThetaLowerSegment 7842572544 7842605312 (784104935900871 / 100000)
      (784108125495671 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842572544 33 20 (1139141 / 50000)
        (455657 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842572544 7842605312 88558 _ _ (1139141 / 50000) (1781763 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842572544 7842605312 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842605312 :
    ThetaLowerSegment 7842605312 7842638080 (784108125495671 / 100000)
      (784111545196953 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842605312 33 20 (1139141 / 50000)
        (455657 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842605312 7842638080 88558 _ _ (1139141 / 50000) (1781763 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842605312 7842638080 12 1501 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842638080 :
    ThetaLowerSegment 7842638080 7842670848 (784111545196953 / 100000)
      (784114771245681 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842638080 33 20 (2278283 / 100000)
        (1139143 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842638080 7842670848 88558 _ _ (2278283 / 100000) (356353 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842638080 7842670848 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842670848 :
    ThetaLowerSegment 7842670848 7842703616 (784114771245681 / 100000)
      (196029527232569 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842670848 33 20 (2278283 / 100000)
        (1139143 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842670848 7842703616 88558 _ _ (2278283 / 100000) (356353 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842670848 7842703616 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842703616 :
    ThetaLowerSegment 7842703616 7842736384 (196029527232569 / 25000) (39206065837637 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842703616 33 20 (2278283 / 100000)
        (1139143 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842703616 7842736384 88559 _ _ (2278283 / 100000) (356353 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842703616 7842736384 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842736384 :
    ThetaLowerSegment 7842736384 7842769152 (39206065837637 / 5000) (196031161900987 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842736384 33 20 (569571 / 25000)
        (2278287 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842736384 7842769152 88559 _ _ (569571 / 25000) (1781767 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842736384 7842769152 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842769152 :
    ThetaLowerSegment 7842769152 7842801920 (196031161900987 / 25000)
      (196031971830949 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842769152 33 20 (569571 / 25000)
        (2278287 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842769152 7842801920 88559 _ _ (569571 / 25000) (1781767 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842769152 7842801920 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842801920 :
    ThetaLowerSegment 7842801920 7842834688 (196031971830949 / 25000)
      (784131161219341 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842801920 33 20 (455657 / 20000)
        (142393 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842801920 7842834688 88559 _ _ (455657 / 20000) (222721 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842801920 7842834688 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842834688 :
    ThetaLowerSegment 7842834688 7842867456 (784131161219341 / 100000)
      (784134482958871 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842834688 33 20 (455657 / 20000)
        (142393 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842834688 7842867456 88559 _ _ (455657 / 20000) (222721 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842834688 7842867456 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842867456 :
    ThetaLowerSegment 7842867456 7842900224 (784134482958871 / 100000)
      (156827559117343 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842867456 33 20 (1139143 / 50000)
        (2278289 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842867456 7842900224 88559 _ _ (1139143 / 50000) (178177 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842867456 7842900224 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842900224 :
    ThetaLowerSegment 7842900224 7842932992 (156827559117343 / 20000)
      (784141215294001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842900224 33 20 (1139143 / 50000)
        (2278289 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842900224 7842932992 88560 _ _ (1139143 / 50000) (178177 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842900224 7842932992 12 1501 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842932992 :
    ThetaLowerSegment 7842932992 7842965760 (784141215294001 / 100000)
      (784144496025841 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842932992 33 20 (1139143 / 50000)
        (2278289 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842932992 7842965760 88560 _ _ (1139143 / 50000) (178177 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842932992 7842965760 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842965760 :
    ThetaLowerSegment 7842965760 7842998528 (784144496025841 / 100000) (31365910341313 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842965760 33 20 (2278287 / 100000)
        (227829 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842965760 7842998528 88560 _ _ (2278287 / 100000) (445443 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842965760 7842998528 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7842998528 :
    ThetaLowerSegment 7842998528 7843031296 (31365910341313 / 4000) (78415098230893 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7842998528 33 20 (2278287 / 100000)
        (227829 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7842998528 7843031296 88560 _ _ (2278287 / 100000) (445443 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7842998528 7843031296 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843031296 :
    ThetaLowerSegment 7843031296 7843064064 (78415098230893 / 10000) (392077096208361 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843031296 33 20 (142393 / 6250)
        (2278291 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843031296 7843064064 88560 _ _ (142393 / 6250) (1781773 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843031296 7843064064 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843064064 :
    ThetaLowerSegment 7843064064 7843096832 (392077096208361 / 50000)
      (392078724045137 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843064064 33 20 (142393 / 6250)
        (2278291 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843064064 7843096832 88561 _ _ (142393 / 6250) (1781773 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843064064 7843096832 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843096832 :
    ThetaLowerSegment 7843096832 7843129600 (392078724045137 / 50000)
      (392080362134209 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843096832 33 20 (142393 / 6250)
        (2278291 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843096832 7843129600 88561 _ _ (142393 / 6250) (1781773 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843096832 7843129600 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843129600 :
    ThetaLowerSegment 7843129600 7843162368 (392080362134209 / 50000)
      (392082020728601 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843129600 33 20 (2278289 / 100000)
        (569573 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843129600 7843162368 88561 _ _ (2278289 / 100000) (71271 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843129600 7843162368 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843162368 :
    ThetaLowerSegment 7843162368 7843195136 (392082020728601 / 50000) (19604184307893 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843162368 33 20 (2278289 / 100000)
        (569573 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843162368 7843195136 88561 _ _ (2278289 / 100000) (71271 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843162368 7843195136 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843195136 :
    ThetaLowerSegment 7843195136 7843227904 (19604184307893 / 2500) (78417055964343 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843195136 33 20 (227829 / 10000)
        (2278293 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843195136 7843227904 88561 _ _ (227829 / 10000) (1781777 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843195136 7843227904 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843227904 :
    ThetaLowerSegment 7843227904 7843260672 (78417055964343 / 10000) (78417384493761 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843227904 33 20 (227829 / 10000)
        (2278293 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843227904 7843260672 88562 _ _ (227829 / 10000) (1781777 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843227904 7843260672 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843260672 :
    ThetaLowerSegment 7843260672 7843293440 (78417384493761 / 10000) (98022152670609 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843260672 33 20 (2278291 / 100000)
        (1139147 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843260672 7843293440 88562 _ _ (2278291 / 100000) (890889 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843260672 7843293440 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843293440 :
    ThetaLowerSegment 7843293440 7843326208 (98022152670609 / 12500) (392090298896067 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843293440 33 20 (2278291 / 100000)
        (1139147 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843293440 7843326208 88562 _ _ (2278291 / 100000) (890889 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843293440 7843326208 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843326208 :
    ThetaLowerSegment 7843326208 7843358976 (392090298896067 / 50000)
      (156836771605311 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843326208 33 20 (2278291 / 100000)
        (1139147 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843326208 7843358976 88562 _ _ (2278291 / 100000) (890889 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843326208 7843358976 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843358976 :
    ThetaLowerSegment 7843358976 7843391744 (156836771605311 / 20000)
      (784187170663123 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843358976 33 20 (569573 / 25000)
        (455659 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843358976 7843391744 88562 _ _ (569573 / 25000) (89089 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843358976 7843391744 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843391744 :
    ThetaLowerSegment 7843391744 7843424512 (784187170663123 / 100000)
      (784190444568727 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843391744 33 20 (569573 / 25000)
        (455659 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843391744 7843424512 88562 _ _ (569573 / 25000) (89089 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843391744 7843424512 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843424512 :
    ThetaLowerSegment 7843424512 7843457280 (784190444568727 / 100000)
      (156838747796081 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843424512 33 20 (2278293 / 100000)
        (284787 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843424512 7843457280 88563 _ _ (2278293 / 100000) (890891 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843424512 7843457280 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843457280 :
    ThetaLowerSegment 7843457280 7843490048 (156838747796081 / 20000)
      (156839408501051 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843457280 33 20 (2278293 / 100000)
        (284787 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843457280 7843490048 88563 _ _ (2278293 / 100000) (890891 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843457280 7843490048 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843490048 :
    ThetaLowerSegment 7843490048 7843522816 (156839408501051 / 20000)
      (784200382482793 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843490048 33 20 (2278293 / 100000)
        (284787 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843490048 7843522816 88563 _ _ (2278293 / 100000) (890891 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843490048 7843522816 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843522816 :
    ThetaLowerSegment 7843522816 7843555584 (784200382482793 / 100000)
      (156840724899031 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843522816 33 20 (1139147 / 50000)
        (2278297 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843522816 7843555584 88563 _ _ (1139147 / 50000) (1781783 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843522816 7843555584 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843555584 :
    ThetaLowerSegment 7843555584 7843588352 (156840724899031 / 20000)
      (784206946247807 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843555584 33 20 (1139147 / 50000)
        (2278297 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843555584 7843588352 88563 _ _ (1139147 / 50000) (1781783 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843555584 7843588352 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843588352 :
    ThetaLowerSegment 7843588352 7843621120 (784206946247807 / 100000) (49013142462087 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843588352 33 20 (455659 / 20000)
        (1139149 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843588352 7843621120 88564 _ _ (455659 / 20000) (356357 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843588352 7843621120 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843621120 :
    ThetaLowerSegment 7843621120 7843653888 (49013142462087 / 6250) (24506672615171 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843621120 33 20 (455659 / 20000)
        (1139149 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843621120 7843653888 88564 _ _ (455659 / 20000) (356357 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843621120 7843653888 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843653888 :
    ThetaLowerSegment 7843653888 7843686656 (24506672615171 / 3125) (19605420851239 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843653888 33 20 (284787 / 12500)
        (2278299 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843653888 7843686656 88564 _ _ (284787 / 12500) (1781787 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843653888 7843686656 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843686656 :
    ThetaLowerSegment 7843686656 7843719424 (19605420851239 / 2500) (24506875098728 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843686656 33 20 (284787 / 12500)
        (2278299 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843686656 7843719424 88564 _ _ (284787 / 12500) (1781787 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843686656 7843719424 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843719424 :
    ThetaLowerSegment 7843719424 7843752192 (24506875098728 / 3125) (24506977337261 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843719424 33 20 (284787 / 12500)
        (2278299 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843719424 7843752192 88564 _ _ (284787 / 12500) (1781787 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843719424 7843752192 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843752192 :
    ThetaLowerSegment 7843752192 7843784960 (24506977337261 / 3125) (196056627493523 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843752192 33 20 (2278297 / 100000)
        (22783 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843752192 7843784960 88564 _ _ (2278297 / 100000) (445447 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843752192 7843784960 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843784960 :
    ThetaLowerSegment 7843784960 7843817728 (196056627493523 / 25000)
      (156845948575507 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843784960 33 20 (2278297 / 100000)
        (22783 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843784960 7843817728 88565 _ _ (2278297 / 100000) (445447 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843784960 7843817728 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843817728 :
    ThetaLowerSegment 7843817728 7843850496 (156845948575507 / 20000)
      (784233062357721 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843817728 33 20 (1139149 / 50000)
        (2278301 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843817728 7843850496 88565 _ _ (1139149 / 50000) (178179 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843817728 7843850496 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843850496 :
    ThetaLowerSegment 7843850496 7843883264 (784233062357721 / 100000)
      (784236295262583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843850496 33 20 (1139149 / 50000)
        (2278301 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843850496 7843883264 88565 _ _ (1139149 / 50000) (178179 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843850496 7843883264 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843883264 :
    ThetaLowerSegment 7843883264 7843916032 (784236295262583 / 100000)
      (156847917024979 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843883264 33 20 (1139149 / 50000)
        (2278301 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843883264 7843916032 88565 _ _ (1139149 / 50000) (178179 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843883264 7843916032 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843916032 :
    ThetaLowerSegment 7843916032 7843948800 (156847917024979 / 20000) (98030352253897 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843916032 33 20 (2278299 / 100000)
        (1139151 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843916032 7843948800 88565 _ _ (2278299 / 100000) (55681 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843916032 7843948800 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843948800 :
    ThetaLowerSegment 7843948800 7843981568 (98030352253897 / 12500) (98030771460913 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843948800 33 20 (2278299 / 100000)
        (1139151 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843948800 7843981568 88566 _ _ (2278299 / 100000) (55681 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843948800 7843981568 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7843981568 :
    ThetaLowerSegment 7843981568 7844014336 (98030771460913 / 12500) (196062354566201 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7843981568 33 20 (22783 / 1000)
        (2278303 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7843981568 7844014336 88566 _ _ (22783 / 1000) (1781793 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7843981568 7844014336 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844014336 :
    ThetaLowerSegment 7844014336 7844047104 (196062354566201 / 25000) (24507899763347 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844014336 33 20 (22783 / 1000)
        (2278303 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844014336 7844047104 88566 _ _ (22783 / 1000) (1781793 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844014336 7844047104 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844047104 :
    ThetaLowerSegment 7844047104 7844079872 (24507899763347 / 3125) (196064020573437 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844047104 33 20 (2278301 / 100000)
        (71197 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844047104 7844079872 88566 _ _ (2278301 / 100000) (356359 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844047104 7844079872 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844079872 :
    ThetaLowerSegment 7844079872 7844112640 (196064020573437 / 25000)
      (784259483797141 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844079872 33 20 (2278301 / 100000)
        (71197 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844079872 7844112640 88566 _ _ (2278301 / 100000) (356359 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844079872 7844112640 12 1493 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844112640 :
    ThetaLowerSegment 7844112640 7844145408 (784259483797141 / 100000)
      (784262600512909 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844112640 33 20 (2278301 / 100000)
        (71197 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844112640 7844145408 88566 _ _ (2278301 / 100000) (356359 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844112640 7844145408 12 1368 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844145408 :
    ThetaLowerSegment 7844145408 7844178176 (784262600512909 / 100000)
      (784265961008359 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844145408 33 20 (1139151 / 50000)
        (455661 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844145408 7844178176 88567 _ _ (1139151 / 50000) (445449 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844145408 7844178176 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844178176 :
    ThetaLowerSegment 7844178176 7844210944 (784265961008359 / 100000)
      (156853854276233 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844178176 33 20 (1139151 / 50000)
        (455661 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844178176 7844210944 88567 _ _ (1139151 / 50000) (445449 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844178176 7844210944 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844210944 :
    ThetaLowerSegment 7844210944 7844243712 (156853854276233 / 20000) (31370900262857 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844210944 33 20 (2278303 / 100000)
        (1139153 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844210944 7844243712 88567 _ _ (2278303 / 100000) (890899 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844210944 7844243712 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844243712 :
    ThetaLowerSegment 7844243712 7844276480 (31370900262857 / 4000) (392137883411509 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844243712 33 20 (2278303 / 100000)
        (1139153 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844243712 7844276480 88567 _ _ (2278303 / 100000) (890899 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844243712 7844276480 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844276480 :
    ThetaLowerSegment 7844276480 7844309248 (392137883411509 / 50000) (24508718670521 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844276480 33 20 (2278303 / 100000)
        (1139153 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844276480 7844309248 88567 _ _ (2278303 / 100000) (890899 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844276480 7844309248 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844309248 :
    ThetaLowerSegment 7844309248 7844342016 (24508718670521 / 3125) (24508821194201 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844309248 33 20 (71197 / 3125)
        (2278307 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844309248 7844342016 88568 _ _ (71197 / 3125) (8909 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844309248 7844342016 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844342016 :
    ThetaLowerSegment 7844342016 7844374784 (24508821194201 / 3125) (4901784843252 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844342016 33 20 (71197 / 3125)
        (2278307 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844342016 7844374784 88568 _ _ (71197 / 3125) (8909 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844342016 7844374784 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844374784 :
    ThetaLowerSegment 7844374784 7844407552 (4901784843252 / 625) (78428885112291 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844374784 33 20 (455661 / 20000)
        (569577 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844374784 7844407552 88568 _ _ (455661 / 20000) (1781801 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844374784 7844407552 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844407552 :
    ThetaLowerSegment 7844407552 7844440320 (78428885112291 / 10000) (78429209542923 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844407552 33 20 (455661 / 20000)
        (569577 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844407552 7844440320 88568 _ _ (455661 / 20000) (1781801 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844407552 7844440320 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844440320 :
    ThetaLowerSegment 7844440320 7844473088 (78429209542923 / 10000) (49018454319343 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844440320 33 20 (1139153 / 50000)
        (2278309 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844440320 7844473088 88568 _ _ (1139153 / 50000) (1781803 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844440320 7844473088 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844473088 :
    ThetaLowerSegment 7844473088 7844505856 (49018454319343 / 6250) (19607462151939 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844473088 33 20 (1139153 / 50000)
        (2278309 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844473088 7844505856 88569 _ _ (1139153 / 50000) (1781803 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844473088 7844505856 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844505856 :
    ThetaLowerSegment 7844505856 7844538624 (19607462151939 / 2500) (392150861775193 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844505856 33 20 (1139153 / 50000)
        (2278309 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844505856 7844538624 88569 _ _ (1139153 / 50000) (1781803 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844505856 7844538624 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844538624 :
    ThetaLowerSegment 7844538624 7844571392 (392150861775193 / 50000)
      (784305006590773 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844538624 33 20 (2278307 / 100000)
        (227831 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844538624 7844571392 88569 _ _ (2278307 / 100000) (356361 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844538624 7844571392 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844571392 :
    ThetaLowerSegment 7844571392 7844604160 (784305006590773 / 100000)
      (392154151650501 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844571392 33 20 (2278307 / 100000)
        (227831 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844571392 7844604160 88569 _ _ (2278307 / 100000) (356361 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844571392 7844604160 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844604160 :
    ThetaLowerSegment 7844604160 7844636928 (392154151650501 / 50000) (78431157495129 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844604160 33 20 (569577 / 25000)
        (2278311 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844604160 7844636928 88569 _ _ (569577 / 25000) (890903 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844604160 7844636928 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844636928 :
    ThetaLowerSegment 7844636928 7844669696 (78431157495129 / 10000) (392157398239401 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844636928 33 20 (569577 / 25000)
        (2278311 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844636928 7844669696 88569 _ _ (569577 / 25000) (890903 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844636928 7844669696 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844669696 :
    ThetaLowerSegment 7844669696 7844702464 (392157398239401 / 50000)
      (196079493110387 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844669696 33 20 (2278309 / 100000)
        (284789 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844669696 7844702464 88570 _ _ (2278309 / 100000) (111363 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844669696 7844702464 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844702464 :
    ThetaLowerSegment 7844702464 7844735232 (196079493110387 / 25000) (78432124864989 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844702464 33 20 (2278309 / 100000)
        (284789 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844702464 7844735232 88570 _ _ (2278309 / 100000) (111363 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844702464 7844735232 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844735232 :
    ThetaLowerSegment 7844735232 7844768000 (78432124864989 / 10000) (392162282933897 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844735232 33 20 (2278309 / 100000)
        (284789 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844735232 7844768000 88570 _ _ (2278309 / 100000) (111363 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844735232 7844768000 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844768000 :
    ThetaLowerSegment 7844768000 7844800768 (392162282933897 / 50000)
      (196081983872071 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844768000 33 20 (227831 / 10000)
        (2278313 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844768000 7844800768 88570 _ _ (227831 / 10000) (178181 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844768000 7844800768 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844800768 :
    ThetaLowerSegment 7844800768 7844833536 (196081983872071 / 25000) (98041400323103 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844800768 33 20 (227831 / 10000)
        (2278313 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844800768 7844833536 88570 _ _ (227831 / 10000) (178181 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844800768 7844833536 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844833536 :
    ThetaLowerSegment 7844833536 7844866304 (98041400323103 / 12500) (39216728268593 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844833536 33 20 (2278311 / 100000)
        (1139157 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844833536 7844866304 88571 _ _ (2278311 / 100000) (1781811 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844833536 7844866304 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844866304 :
    ThetaLowerSegment 7844866304 7844899072 (39216728268593 / 5000) (392168952687893 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844866304 33 20 (2278311 / 100000)
        (1139157 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844866304 7844899072 88571 _ _ (2278311 / 100000) (1781811 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844866304 7844899072 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844899072 :
    ThetaLowerSegment 7844899072 7844931840 (392168952687893 / 50000)
      (392170624968167 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844899072 33 20 (2278311 / 100000)
        (1139157 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844899072 7844931840 88571 _ _ (2278311 / 100000) (1781811 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844899072 7844931840 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844931840 :
    ThetaLowerSegment 7844931840 7844964608 (392170624968167 / 50000)
      (392172267631119 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844931840 33 20 (284789 / 12500)
        (455663 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844931840 7844964608 88571 _ _ (284789 / 12500) (1781813 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844931840 7844964608 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844964608 :
    ThetaLowerSegment 7844964608 7844997376 (392172267631119 / 50000)
      (392173911433227 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844964608 33 20 (284789 / 12500)
        (455663 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844964608 7844997376 88571 _ _ (284789 / 12500) (1781813 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844964608 7844997376 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7844997376 :
    ThetaLowerSegment 7844997376 7845030144 (392173911433227 / 50000) (98043883967599 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7844997376 33 20 (2278313 / 100000)
        (569579 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7844997376 7845030144 88571 _ _ (2278313 / 100000) (356363 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7844997376 7845030144 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845030144 :
    ThetaLowerSegment 7845030144 7845062912 (98043883967599 / 12500)
      (784354427695841 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845030144 33 20 (2278313 / 100000)
        (569579 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845030144 7845062912 88572 _ _ (2278313 / 100000) (356363 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845030144 7845062912 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845062912 :
    ThetaLowerSegment 7845062912 7845095680 (784354427695841 / 100000)
      (784357765425851 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845062912 33 20 (1139157 / 50000)
        (2278317 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845062912 7845095680 88572 _ _ (1139157 / 50000) (222727 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845062912 7845095680 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845095680 :
    ThetaLowerSegment 7845095680 7845128448 (784357765425851 / 100000)
      (156872191468753 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845095680 33 20 (1139157 / 50000)
        (2278317 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845095680 7845128448 88572 _ _ (1139157 / 50000) (222727 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845095680 7845128448 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845128448 :
    ThetaLowerSegment 7845128448 7845161216 (156872191468753 / 20000)
      (784364176601447 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845128448 33 20 (1139157 / 50000)
        (2278317 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845128448 7845161216 88572 _ _ (1139157 / 50000) (222727 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845128448 7845161216 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845161216 :
    ThetaLowerSegment 7845161216 7845193984 (784364176601447 / 100000)
      (784367493828087 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845161216 33 20 (455663 / 20000)
        (1139159 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845161216 7845193984 88572 _ _ (455663 / 20000) (890909 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845161216 7845193984 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845193984 :
    ThetaLowerSegment 7845193984 7845226752 (784367493828087 / 100000)
      (196092665741063 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845193984 33 20 (455663 / 20000)
        (1139159 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845193984 7845226752 88573 _ _ (455663 / 20000) (890909 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845193984 7845226752 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845226752 :
    ThetaLowerSegment 7845226752 7845259520 (196092665741063 / 25000)
      (196093468847453 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845226752 33 20 (569579 / 25000)
        (2278319 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845226752 7845259520 88573 _ _ (569579 / 25000) (89091 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845226752 7845259520 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845259520 :
    ThetaLowerSegment 7845259520 7845292288 (196093468847453 / 25000)
      (196094289041213 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845259520 33 20 (569579 / 25000)
        (2278319 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845259520 7845292288 88573 _ _ (569579 / 25000) (89091 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845259520 7845292288 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845292288 :
    ThetaLowerSegment 7845292288 7845325056 (196094289041213 / 25000)
      (196095116069921 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845292288 33 20 (569579 / 25000)
        (2278319 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845292288 7845325056 88573 _ _ (569579 / 25000) (89091 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845292288 7845325056 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845325056 :
    ThetaLowerSegment 7845325056 7845357824 (196095116069921 / 25000) (98047973827813 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845325056 33 20 (2278317 / 100000)
        (28479 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845325056 7845357824 88573 _ _ (2278317 / 100000) (1781821 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845325056 7845357824 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845357824 :
    ThetaLowerSegment 7845357824 7845390592 (98047973827813 / 12500) (392193551647711 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845357824 33 20 (2278317 / 100000)
        (28479 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845357824 7845390592 88574 _ _ (2278317 / 100000) (1781821 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845357824 7845390592 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845390592 :
    ThetaLowerSegment 7845390592 7845423360 (392193551647711 / 50000)
      (196097601144551 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845390592 33 20 (1139159 / 50000)
        (2278321 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845390592 7845423360 88574 _ _ (1139159 / 50000) (1781823 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845390592 7845423360 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845423360 :
    ThetaLowerSegment 7845423360 7845456128 (196097601144551 / 25000)
      (392196848373857 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845423360 33 20 (1139159 / 50000)
        (2278321 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845423360 7845456128 88574 _ _ (1139159 / 50000) (1781823 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845423360 7845456128 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845456128 :
    ThetaLowerSegment 7845456128 7845488896 (392196848373857 / 50000)
      (784397025371773 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845456128 33 20 (2278319 / 100000)
        (1139161 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845456128 7845488896 88574 _ _ (2278319 / 100000) (71273 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845456128 7845488896 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845488896 :
    ThetaLowerSegment 7845488896 7845521664 (784397025371773 / 100000)
      (98050039692841 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845488896 33 20 (2278319 / 100000)
        (1139161 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845488896 7845521664 88574 _ _ (2278319 / 100000) (71273 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845488896 7845521664 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845521664 :
    ThetaLowerSegment 7845521664 7845554432 (98050039692841 / 12500)
      (784403577817217 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845521664 33 20 (2278319 / 100000)
        (1139161 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845521664 7845554432 88574 _ _ (2278319 / 100000) (71273 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845521664 7845554432 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845554432 :
    ThetaLowerSegment 7845554432 7845587200 (784403577817217 / 100000)
      (784406904164417 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845554432 33 20 (28479 / 1250)
        (2278323 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845554432 7845587200 88575 _ _ (28479 / 1250) (890913 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845554432 7845587200 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845587200 :
    ThetaLowerSegment 7845587200 7845619968 (784406904164417 / 100000)
      (784410125708897 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845587200 33 20 (28479 / 1250)
        (2278323 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845587200 7845619968 88575 _ _ (28479 / 1250) (890913 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845587200 7845619968 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845619968 :
    ThetaLowerSegment 7845619968 7845652736 (784410125708897 / 100000)
      (784413319914939 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845619968 33 20 (2278321 / 100000)
        (569581 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845619968 7845652736 88575 _ _ (2278321 / 100000) (445457 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845619968 7845652736 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845652736 :
    ThetaLowerSegment 7845652736 7845685504 (784413319914939 / 100000)
      (784416541460833 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845652736 33 20 (2278321 / 100000)
        (569581 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845652736 7845685504 88575 _ _ (2278321 / 100000) (445457 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845652736 7845685504 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845685504 :
    ThetaLowerSegment 7845685504 7845718272 (784416541460833 / 100000) (49026243304439 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845685504 33 20 (2278321 / 100000)
        (569581 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845685504 7845718272 88575 _ _ (2278321 / 100000) (445457 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845685504 7845718272 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845718272 :
    ThetaLowerSegment 7845718272 7845751040 (49026243304439 / 6250) (392211594801479 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845718272 33 20 (1139161 / 50000)
        (91133 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845718272 7845751040 88576 _ _ (1139161 / 50000) (1781829 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845718272 7845751040 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845751040 :
    ThetaLowerSegment 7845751040 7845783808 (392211594801479 / 50000) (78442643849013 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845751040 33 20 (1139161 / 50000)
        (91133 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845751040 7845783808 88576 _ _ (1139161 / 50000) (1781829 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845751040 7845783808 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845783808 :
    ThetaLowerSegment 7845783808 7845816576 (78442643849013 / 10000) (196107410453067 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845783808 33 20 (2278323 / 100000)
        (1139163 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845783808 7845816576 88576 _ _ (2278323 / 100000) (1781831 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845783808 7845816576 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845816576 :
    ThetaLowerSegment 7845816576 7845849344 (196107410453067 / 25000)
      (392216459020371 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845816576 33 20 (2278323 / 100000)
        (1139163 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845816576 7845849344 88576 _ _ (2278323 / 100000) (1781831 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845816576 7845849344 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845849344 :
    ThetaLowerSegment 7845849344 7845882112 (392216459020371 / 50000) (78443622616719 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845849344 33 20 (569581 / 25000)
        (2278327 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845849344 7845882112 88576 _ _ (569581 / 25000) (1781833 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845849344 7845882112 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845882112 :
    ThetaLowerSegment 7845882112 7845914880 (78443622616719 / 10000) (392219785373411 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845882112 33 20 (569581 / 25000)
        (2278327 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845882112 7845914880 88576 _ _ (569581 / 25000) (1781833 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845882112 7845914880 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845914880 :
    ThetaLowerSegment 7845914880 7845947648 (392219785373411 / 50000)
      (392221372226077 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845914880 33 20 (569581 / 25000)
        (2278327 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845914880 7845947648 88577 _ _ (569581 / 25000) (1781833 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845914880 7845947648 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845947648 :
    ThetaLowerSegment 7845947648 7845980416 (392221372226077 / 50000)
      (784445918158879 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845947648 33 20 (91133 / 4000) (284791 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845947648 7845980416 88577 _ _ (91133 / 4000) (890917 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845947648 7845980416 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7845980416 :
    ThetaLowerSegment 7845980416 7846013184 (784445918158879 / 100000)
      (98056160405613 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7845980416 33 20 (91133 / 4000) (284791 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7845980416 7846013184 88577 _ _ (91133 / 4000) (890917 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7845980416 7846013184 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846013184 :
    ThetaLowerSegment 7846013184 7846045952 (98056160405613 / 12500) (196113123921141 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846013184 33 20 (1139163 / 50000)
        (2278329 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846013184 7846045952 88577 _ _ (1139163 / 50000) (445459 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846013184 7846045952 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846045952 :
    ThetaLowerSegment 7846045952 7846078720 (196113123921141 / 25000)
      (196113960066783 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846045952 33 20 (1139163 / 50000)
        (2278329 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846045952 7846078720 88577 _ _ (1139163 / 50000) (445459 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846045952 7846078720 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846078720 :
    ThetaLowerSegment 7846078720 7846111488 (196113960066783 / 25000)
      (392229561667449 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846078720 33 20 (1139163 / 50000)
        (2278329 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846078720 7846111488 88578 _ _ (1139163 / 50000) (445459 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846078720 7846111488 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846111488 :
    ThetaLowerSegment 7846111488 7846144256 (392229561667449 / 50000)
      (156892481280821 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846111488 33 20 (2278327 / 100000)
        (227833 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846111488 7846144256 88578 _ _ (2278327 / 100000) (890919 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846111488 7846144256 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846144256 :
    ThetaLowerSegment 7846144256 7846177024 (156892481280821 / 20000)
      (784465682638331 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846144256 33 20 (2278327 / 100000)
        (227833 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846144256 7846177024 88578 _ _ (2278327 / 100000) (890919 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846144256 7846177024 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846177024 :
    ThetaLowerSegment 7846177024 7846209792 (784465682638331 / 100000)
      (784469059120427 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846177024 33 20 (284791 / 12500)
        (2278331 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846177024 7846209792 88578 _ _ (284791 / 12500) (1781839 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846177024 7846209792 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846209792 :
    ThetaLowerSegment 7846209792 7846242560 (784469059120427 / 100000)
      (784472367252683 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846209792 33 20 (284791 / 12500)
        (2278331 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846209792 7846242560 88578 _ _ (284791 / 12500) (1781839 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846209792 7846242560 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846242560 :
    ThetaLowerSegment 7846242560 7846275328 (784472367252683 / 100000)
      (784475648046443 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846242560 33 20 (2278329 / 100000)
        (569583 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846242560 7846275328 88579 _ _ (2278329 / 100000) (1781841 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846242560 7846275328 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846275328 :
    ThetaLowerSegment 7846275328 7846308096 (784475648046443 / 100000)
      (196119746449607 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846275328 33 20 (2278329 / 100000)
        (569583 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846275328 7846308096 88579 _ _ (2278329 / 100000) (1781841 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846275328 7846308096 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846308096 :
    ThetaLowerSegment 7846308096 7846340864 (196119746449607 / 25000) (24515071115797 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846308096 33 20 (2278329 / 100000)
        (569583 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846308096 7846340864 88579 _ _ (2278329 / 100000) (1781841 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846308096 7846340864 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846340864 :
    ThetaLowerSegment 7846340864 7846373632 (24515071115797 / 3125) (392242795337827 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846340864 33 20 (227833 / 10000)
        (2278333 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846340864 7846373632 88579 _ _ (227833 / 10000) (1781843 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846340864 7846373632 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846373632 :
    ThetaLowerSegment 7846373632 7846406400 (392242795337827 / 50000)
      (392244476745367 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846373632 33 20 (227833 / 10000)
        (2278333 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846373632 7846406400 88579 _ _ (227833 / 10000) (1781843 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846373632 7846406400 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846406400 :
    ThetaLowerSegment 7846406400 7846439168 (392244476745367 / 50000)
      (784492181885761 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846406400 33 20 (2278331 / 100000)
        (1139167 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846406400 7846439168 88579 _ _ (2278331 / 100000) (445461 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846406400 7846439168 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846439168 :
    ThetaLowerSegment 7846439168 7846471936 (784492181885761 / 100000)
      (78449555153731 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846439168 33 20 (2278331 / 100000)
        (1139167 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846439168 7846471936 88580 _ _ (2278331 / 100000) (445461 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846439168 7846471936 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846471936 :
    ThetaLowerSegment 7846471936 7846504704 (78449555153731 / 10000) (196124722892639 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846471936 33 20 (2278331 / 100000)
        (1139167 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846471936 7846504704 88580 _ _ (2278331 / 100000) (445461 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846471936 7846504704 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846504704 :
    ThetaLowerSegment 7846504704 7846537472 (196124722892639 / 25000)
      (196125553344653 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846504704 33 20 (569583 / 25000)
        (455667 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846504704 7846537472 88580 _ _ (569583 / 25000) (890923 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846504704 7846537472 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846537472 :
    ThetaLowerSegment 7846537472 7846570240 (196125553344653 / 25000)
      (196126371265841 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846537472 33 20 (569583 / 25000)
        (455667 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846537472 7846570240 88580 _ _ (569583 / 25000) (890923 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846537472 7846570240 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846570240 :
    ThetaLowerSegment 7846570240 7846603008 (196126371265841 / 25000)
      (784508708904559 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846570240 33 20 (2278333 / 100000)
        (71198 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846570240 7846603008 88580 _ _ (2278333 / 100000) (222731 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846570240 7846603008 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846603008 :
    ThetaLowerSegment 7846603008 7846635776 (784508708904559 / 100000)
      (156902412522147 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846603008 33 20 (2278333 / 100000)
        (71198 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846603008 7846635776 88581 _ _ (2278333 / 100000) (222731 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846603008 7846635776 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846635776 :
    ThetaLowerSegment 7846635776 7846668544 (156902412522147 / 20000)
      (784515395813377 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846635776 33 20 (1139167 / 50000)
        (2278337 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846635776 7846668544 88581 _ _ (1139167 / 50000) (1781849 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846635776 7846668544 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846668544 :
    ThetaLowerSegment 7846668544 7846701312 (784515395813377 / 100000)
      (784518767747697 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846668544 33 20 (1139167 / 50000)
        (2278337 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846668544 7846701312 88581 _ _ (1139167 / 50000) (1781849 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846668544 7846701312 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846701312 :
    ThetaLowerSegment 7846701312 7846734080 (784518767747697 / 100000) (31380882124213 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846701312 33 20 (1139167 / 50000)
        (2278337 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846701312 7846734080 88581 _ _ (1139167 / 50000) (1781849 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846701312 7846734080 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846734080 :
    ThetaLowerSegment 7846734080 7846766848 (31380882124213 / 4000) (39226265897969 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846734080 33 20 (455667 / 20000)
        (1139169 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846734080 7846766848 88581 _ _ (455667 / 20000) (1781851 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846734080 7846766848 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846766848 :
    ThetaLowerSegment 7846766848 7846799616 (39226265897969 / 5000) (78452848484503 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846766848 33 20 (455667 / 20000)
        (1139169 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846766848 7846799616 88581 _ _ (455667 / 20000) (1781851 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846766848 7846799616 12 1390 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846799616 :
    ThetaLowerSegment 7846799616 7846832384 (78452848484503 / 10000) (78453169729879 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846799616 33 20 (71198 / 3125)
        (2278339 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846799616 7846832384 88582 _ _ (71198 / 3125) (1781853 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846799616 7846832384 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846832384 :
    ThetaLowerSegment 7846832384 7846865152 (78453169729879 / 10000) (392267459432947 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846832384 33 20 (71198 / 3125)
        (2278339 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846832384 7846865152 88582 _ _ (71198 / 3125) (1781853 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846832384 7846865152 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846865152 :
    ThetaLowerSegment 7846865152 7846897920 (392267459432947 / 50000)
      (392269151097427 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846865152 33 20 (71198 / 3125)
        (2278339 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846865152 7846897920 88582 _ _ (71198 / 3125) (1781853 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846865152 7846897920 12 1485 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846897920 :
    ThetaLowerSegment 7846897920 7846930688 (392269151097427 / 50000)
      (784541649071907 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846897920 33 20 (2278337 / 100000)
        (113917 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846897920 7846930688 88582 _ _ (2278337 / 100000) (890927 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846897920 7846930688 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846930688 :
    ThetaLowerSegment 7846930688 7846963456 (784541649071907 / 100000) (24517028845068 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846930688 33 20 (2278337 / 100000)
        (113917 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846930688 7846963456 88582 _ _ (2278337 / 100000) (890927 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846930688 7846963456 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846963456 :
    ThetaLowerSegment 7846963456 7846996224 (24517028845068 / 3125) (78454811955039 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846963456 33 20 (1139169 / 50000)
        (2278341 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846963456 7846996224 88583 _ _ (1139169 / 50000) (55683 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846963456 7846996224 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7846996224 :
    ThetaLowerSegment 7846996224 7847028992 (78454811955039 / 10000) (98068918494417 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7846996224 33 20 (1139169 / 50000)
        (2278341 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7846996224 7847028992 88583 _ _ (1139169 / 50000) (55683 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7846996224 7847028992 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847028992 :
    ThetaLowerSegment 7847028992 7847061760 (98068918494417 / 12500) (196138659469213 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847028992 33 20 (2278339 / 100000)
        (1139171 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847028992 7847061760 88583 _ _ (2278339 / 100000) (890929 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847028992 7847061760 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847061760 :
    ThetaLowerSegment 7847061760 7847094528 (196138659469213 / 25000) (7845579004583 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847061760 33 20 (2278339 / 100000)
        (1139171 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847061760 7847094528 88583 _ _ (2278339 / 100000) (890929 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847061760 7847094528 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847094528 :
    ThetaLowerSegment 7847094528 7847127296 (7845579004583 / 1000) (392280606581603 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847094528 33 20 (2278339 / 100000)
        (1139171 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847094528 7847127296 88583 _ _ (2278339 / 100000) (890929 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847094528 7847127296 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847127296 :
    ThetaLowerSegment 7847127296 7847160064 (392280606581603 / 50000)
      (392282225342173 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847127296 33 20 (113917 / 5000)
        (2278343 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847127296 7847160064 88584 _ _ (113917 / 5000) (1781859 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847127296 7847160064 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847160064 :
    ThetaLowerSegment 7847160064 7847192832 (392282225342173 / 50000)
      (392283820180173 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847160064 33 20 (113917 / 5000)
        (2278343 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847160064 7847192832 88584 _ _ (113917 / 5000) (1781859 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847160064 7847192832 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847192832 :
    ThetaLowerSegment 7847192832 7847225600 (392283820180173 / 50000)
      (784570877882907 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847192832 33 20 (2278341 / 100000)
        (284793 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847192832 7847225600 88584 _ _ (2278341 / 100000) (1781861 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847192832 7847225600 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847225600 :
    ThetaLowerSegment 7847225600 7847258368 (784570877882907 / 100000)
      (156914826270771 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847225600 33 20 (2278341 / 100000)
        (284793 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847225600 7847258368 88584 _ _ (2278341 / 100000) (1781861 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847225600 7847258368 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847258368 :
    ThetaLowerSegment 7847258368 7847291136 (156914826270771 / 20000)
      (784577450898149 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847258368 33 20 (1139171 / 50000)
        (455669 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847258368 7847291136 88584 _ _ (1139171 / 50000) (890931 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847258368 7847291136 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847291136 :
    ThetaLowerSegment 7847291136 7847323904 (784577450898149 / 100000)
      (784580706648867 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847291136 33 20 (1139171 / 50000)
        (455669 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847291136 7847323904 88584 _ _ (1139171 / 50000) (890931 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847291136 7847323904 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847323904 :
    ThetaLowerSegment 7847323904 7847356672 (784580706648867 / 100000)
      (784584001131399 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847323904 33 20 (1139171 / 50000)
        (455669 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847323904 7847356672 88585 _ _ (1139171 / 50000) (890931 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847323904 7847356672 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847356672 :
    ThetaLowerSegment 7847356672 7847389440 (784584001131399 / 100000) (24518354767936 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847356672 33 20 (2278343 / 100000)
        (1139173 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847356672 7847389440 88585 _ _ (2278343 / 100000) (222733 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847356672 7847389440 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847389440 :
    ThetaLowerSegment 7847389440 7847422208 (24518354767936 / 3125) (784590580985983 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847389440 33 20 (2278343 / 100000)
        (1139173 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847389440 7847422208 88585 _ _ (2278343 / 100000) (222733 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847389440 7847422208 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847422208 :
    ThetaLowerSegment 7847422208 7847454976 (784590580985983 / 100000)
      (156918780562307 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847422208 33 20 (284793 / 12500)
        (2278347 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847422208 7847454976 88585 _ _ (284793 / 12500) (890933 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847422208 7847454976 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847454976 :
    ThetaLowerSegment 7847454976 7847487744 (156918780562307 / 20000)
      (784597242863839 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847454976 33 20 (284793 / 12500)
        (2278347 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847454976 7847487744 88585 _ _ (284793 / 12500) (890933 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847454976 7847487744 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847487744 :
    ThetaLowerSegment 7847487744 7847520512 (784597242863839 / 100000)
      (784600432545439 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847487744 33 20 (284793 / 12500)
        (2278347 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847487744 7847520512 88586 _ _ (284793 / 12500) (890933 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847487744 7847520512 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847520512 :
    ThetaLowerSegment 7847520512 7847553280 (784600432545439 / 100000)
      (784603713362239 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847520512 33 20 (455669 / 20000)
        (569587 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847520512 7847553280 88586 _ _ (455669 / 20000) (1781867 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847520512 7847553280 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847553280 :
    ThetaLowerSegment 7847553280 7847586048 (784603713362239 / 100000)
      (392303491393657 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847553280 33 20 (455669 / 20000)
        (569587 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847553280 7847586048 88586 _ _ (455669 / 20000) (1781867 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847553280 7847586048 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847586048 :
    ThetaLowerSegment 7847586048 7847618816 (392303491393657 / 50000) (49038144180883 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847586048 33 20 (1139173 / 50000)
        (2278349 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847586048 7847618816 88586 _ _ (1139173 / 50000) (1781869 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847586048 7847618816 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847618816 :
    ThetaLowerSegment 7847618816 7847651584 (49038144180883 / 6250) (49038346953677 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847618816 33 20 (1139173 / 50000)
        (2278349 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847618816 7847651584 88586 _ _ (1139173 / 50000) (1781869 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847618816 7847651584 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847651584 :
    ThetaLowerSegment 7847651584 7847684352 (49038346953677 / 6250) (392308395534133 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847651584 33 20 (2278347 / 100000)
        (45567 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847651584 7847684352 88586 _ _ (2278347 / 100000) (1781871 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847651584 7847684352 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847684352 :
    ThetaLowerSegment 7847684352 7847717120 (392308395534133 / 50000)
      (156924031237357 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847684352 33 20 (2278347 / 100000)
        (45567 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847684352 7847717120 88587 _ _ (2278347 / 100000) (1781871 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847684352 7847717120 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847717120 :
    ThetaLowerSegment 7847717120 7847749888 (156924031237357 / 20000)
      (784623427893077 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847717120 33 20 (2278347 / 100000)
        (45567 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847717120 7847749888 88587 _ _ (2278347 / 100000) (1781871 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847717120 7847749888 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847749888 :
    ThetaLowerSegment 7847749888 7847782656 (784623427893077 / 100000)
      (784626635807061 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847749888 33 20 (569587 / 25000)
        (2278351 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847749888 7847782656 88587 _ _ (569587 / 25000) (111367 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847749888 7847782656 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847782656 :
    ThetaLowerSegment 7847782656 7847815424 (784626635807061 / 100000)
      (784629836886001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847782656 33 20 (569587 / 25000)
        (2278351 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847782656 7847815424 88587 _ _ (569587 / 25000) (111367 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847782656 7847815424 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847815424 :
    ThetaLowerSegment 7847815424 7847848192 (784629836886001 / 100000)
      (392316564550153 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847815424 33 20 (2278349 / 100000)
        (142397 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847815424 7847848192 88587 _ _ (2278349 / 100000) (890937 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847815424 7847848192 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847848192 :
    ThetaLowerSegment 7847848192 7847880960 (392316564550153 / 50000)
      (784636371190933 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847848192 33 20 (2278349 / 100000)
        (142397 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847848192 7847880960 88588 _ _ (2278349 / 100000) (890937 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847848192 7847880960 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847880960 :
    ThetaLowerSegment 7847880960 7847913728 (784636371190933 / 100000)
      (392319781578941 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847880960 33 20 (2278349 / 100000)
        (142397 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847880960 7847913728 88588 _ _ (2278349 / 100000) (890937 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847880960 7847913728 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847913728 :
    ThetaLowerSegment 7847913728 7847946496 (392319781578941 / 50000)
      (392321456166191 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847913728 33 20 (45567 / 2000)
        (2278353 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847913728 7847946496 88588 _ _ (45567 / 2000) (445469 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847913728 7847946496 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847946496 :
    ThetaLowerSegment 7847946496 7847979264 (392321456166191 / 50000)
      (392323105691591 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847946496 33 20 (45567 / 2000)
        (2278353 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847946496 7847979264 88588 _ _ (45567 / 2000) (445469 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847946496 7847979264 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7847979264 :
    ThetaLowerSegment 7847979264 7848012032 (392323105691591 / 50000)
      (392324805341437 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7847979264 33 20 (2278351 / 100000)
        (1139177 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7847979264 7848012032 88588 _ _ (2278351 / 100000) (1781877 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7847979264 7848012032 12 1492 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848012032 :
    ThetaLowerSegment 7848012032 7848044800 (392324805341437 / 50000)
      (156930569643929 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848012032 33 20 (2278351 / 100000)
        (1139177 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848012032 7848044800 88589 _ _ (2278351 / 100000) (1781877 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848012032 7848044800 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848044800 :
    ThetaLowerSegment 7848044800 7848077568 (156930569643929 / 20000)
      (784656115376413 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848044800 33 20 (142397 / 6250)
        (455671 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848044800 7848077568 88589 _ _ (142397 / 6250) (1781879 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848044800 7848077568 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848077568 :
    ThetaLowerSegment 7848077568 7848110336 (784656115376413 / 100000)
      (156931866026217 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848077568 33 20 (142397 / 6250)
        (455671 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848077568 7848110336 88589 _ _ (142397 / 6250) (1781879 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848077568 7848110336 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848110336 :
    ThetaLowerSegment 7848110336 7848143104 (156931866026217 / 20000)
      (784662631463133 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848110336 33 20 (142397 / 6250)
        (455671 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848110336 7848143104 88589 _ _ (142397 / 6250) (1781879 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848110336 7848143104 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848143104 :
    ThetaLowerSegment 7848143104 7848175872 (784662631463133 / 100000)
      (784666021652397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848143104 33 20 (2278353 / 100000)
        (569589 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848143104 7848175872 88589 _ _ (2278353 / 100000) (1781881 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848143104 7848175872 12 1488 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848175872 :
    ThetaLowerSegment 7848175872 7848208640 (784666021652397 / 100000)
      (156933867786873 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848175872 33 20 (2278353 / 100000)
        (569589 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848175872 7848208640 88589 _ _ (2278353 / 100000) (1781881 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848175872 7848208640 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848208640 :
    ThetaLowerSegment 7848208640 7848241408 (156933867786873 / 20000)
      (784672649382727 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848208640 33 20 (1139177 / 50000)
        (2278357 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848208640 7848241408 88590 _ _ (1139177 / 50000) (890941 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848208640 7848241408 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848241408 :
    ThetaLowerSegment 7848241408 7848274176 (784672649382727 / 100000)
      (784675859583513 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848241408 33 20 (1139177 / 50000)
        (2278357 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848241408 7848274176 88590 _ _ (1139177 / 50000) (890941 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848241408 7848274176 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848274176 :
    ThetaLowerSegment 7848274176 7848306944 (784675859583513 / 100000)
      (784679076619361 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848274176 33 20 (1139177 / 50000)
        (2278357 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848274176 7848306944 88590 _ _ (1139177 / 50000) (890941 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848274176 7848306944 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848306944 :
    ThetaLowerSegment 7848306944 7848339712 (784679076619361 / 100000)
      (196170571705389 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848306944 33 20 (455671 / 20000)
        (1139179 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848306944 7848339712 88590 _ _ (455671 / 20000) (445471 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848306944 7848339712 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848339712 :
    ThetaLowerSegment 7848339712 7848372480 (196170571705389 / 25000)
      (392342758764473 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848339712 33 20 (455671 / 20000)
        (1139179 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848339712 7848372480 88590 _ _ (455671 / 20000) (445471 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848339712 7848372480 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848372480 :
    ThetaLowerSegment 7848372480 7848405248 (392342758764473 / 50000)
      (392344418546819 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848372480 33 20 (569589 / 25000)
        (2278359 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848372480 7848405248 88591 _ _ (569589 / 25000) (890943 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848372480 7848405248 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848405248 :
    ThetaLowerSegment 7848405248 7848438016 (392344418546819 / 50000)
      (392346011117663 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848405248 33 20 (569589 / 25000)
        (2278359 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848405248 7848438016 88591 _ _ (569589 / 25000) (890943 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848405248 7848438016 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848438016 :
    ThetaLowerSegment 7848438016 7848470784 (392346011117663 / 50000)
      (784695346358189 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848438016 33 20 (2278357 / 100000)
        (56959 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848438016 7848470784 88591 _ _ (2278357 / 100000) (1781887 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848438016 7848470784 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848470784 :
    ThetaLowerSegment 7848470784 7848503552 (784695346358189 / 100000)
      (156939733640539 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848470784 33 20 (2278357 / 100000)
        (56959 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848470784 7848503552 88591 _ _ (2278357 / 100000) (1781887 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848470784 7848503552 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848503552 :
    ThetaLowerSegment 7848503552 7848536320 (156939733640539 / 20000)
      (392350982492637 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848503552 33 20 (2278357 / 100000)
        (56959 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848503552 7848536320 88591 _ _ (2278357 / 100000) (1781887 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848503552 7848536320 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848536320 :
    ThetaLowerSegment 7848536320 7848569088 (392350982492637 / 50000)
      (392352643415619 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848536320 33 20 (1139179 / 50000)
        (2278361 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848536320 7848569088 88591 _ _ (1139179 / 50000) (1781889 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848536320 7848569088 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848569088 :
    ThetaLowerSegment 7848569088 7848601856 (392352643415619 / 50000) (98088590039593 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848569088 33 20 (1139179 / 50000)
        (2278361 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848569088 7848601856 88592 _ _ (1139179 / 50000) (1781889 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848569088 7848601856 12 1507 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848601856 :
    ThetaLowerSegment 7848601856 7848634624 (98088590039593 / 12500)
      (784712017102217 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848601856 33 20 (2278359 / 100000)
        (1139181 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848601856 7848634624 88592 _ _ (2278359 / 100000) (1781891 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848601856 7848634624 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848634624 :
    ThetaLowerSegment 7848634624 7848667392 (784712017102217 / 100000)
      (196178818219307 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848634624 33 20 (2278359 / 100000)
        (1139181 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848634624 7848667392 88592 _ _ (2278359 / 100000) (1781891 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848634624 7848667392 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848667392 :
    ThetaLowerSegment 7848667392 7848700160 (196178818219307 / 25000) (98089820353453 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848667392 33 20 (2278359 / 100000)
        (1139181 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848667392 7848700160 88592 _ _ (2278359 / 100000) (1781891 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848667392 7848700160 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848700160 :
    ThetaLowerSegment 7848700160 7848732928 (98089820353453 / 12500) (98090227040713 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848700160 33 20 (56959 / 2500)
        (2278363 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848700160 7848732928 88592 _ _ (56959 / 2500) (445473 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848700160 7848732928 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848732928 :
    ThetaLowerSegment 7848732928 7848765696 (98090227040713 / 12500) (98090634867153 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848732928 33 20 (56959 / 2500)
        (2278363 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848732928 7848765696 88593 _ _ (56959 / 2500) (445473 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848732928 7848765696 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848765696 :
    ThetaLowerSegment 7848765696 7848798464 (98090634867153 / 12500)
      (784728325601649 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848765696 33 20 (2278361 / 100000)
        (569591 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848765696 7848798464 88593 _ _ (2278361 / 100000) (890947 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848765696 7848798464 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848798464 :
    ThetaLowerSegment 7848798464 7848831232 (784728325601649 / 100000)
      (98091450520391 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848798464 33 20 (2278361 / 100000)
        (569591 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848798464 7848831232 88593 _ _ (2278361 / 100000) (890947 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848798464 7848831232 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848831232 :
    ThetaLowerSegment 7848831232 7848864000 (98091450520391 / 12500) (196183738338817 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848831232 33 20 (1139181 / 50000)
        (455673 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848831232 7848864000 88593 _ _ (1139181 / 50000) (222737 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848831232 7848864000 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848864000 :
    ThetaLowerSegment 7848864000 7848896768 (196183738338817 / 25000)
      (196184535765517 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848864000 33 20 (1139181 / 50000)
        (455673 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848864000 7848896768 88593 _ _ (1139181 / 50000) (222737 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848864000 7848896768 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848896768 :
    ThetaLowerSegment 7848896768 7848929536 (196184535765517 / 25000)
      (196185355975837 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848896768 33 20 (1139181 / 50000)
        (455673 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848896768 7848929536 88593 _ _ (1139181 / 50000) (222737 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848896768 7848929536 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848929536 :
    ThetaLowerSegment 7848929536 7848962304 (196185355975837 / 25000)
      (392372331867767 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848929536 33 20 (2278363 / 100000)
        (1139183 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848929536 7848962304 88594 _ _ (2278363 / 100000) (1781897 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848929536 7848962304 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848962304 :
    ThetaLowerSegment 7848962304 7848995072 (392372331867767 / 50000)
      (784747928629713 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848962304 33 20 (2278363 / 100000)
        (1139183 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848962304 7848995072 88594 _ _ (2278363 / 100000) (1781897 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848962304 7848995072 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7848995072 :
    ThetaLowerSegment 7848995072 7849027840 (784747928629713 / 100000)
      (156950247818521 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7848995072 33 20 (569591 / 25000)
        (2278367 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7848995072 7849027840 88594 _ _ (569591 / 25000) (1781899 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7848995072 7849027840 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849027840 :
    ThetaLowerSegment 7849027840 7849060608 (156950247818521 / 20000)
      (784754538163677 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849027840 33 20 (569591 / 25000)
        (2278367 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849027840 7849060608 88594 _ _ (569591 / 25000) (1781899 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849027840 7849060608 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849060608 :
    ThetaLowerSegment 7849060608 7849093376 (784754538163677 / 100000)
      (156951557877821 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849060608 33 20 (569591 / 25000)
        (2278367 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849060608 7849093376 88594 _ _ (569591 / 25000) (1781899 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849060608 7849093376 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849093376 :
    ThetaLowerSegment 7849093376 7849126144 (156951557877821 / 20000)
      (156952214958287 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849093376 33 20 (455673 / 20000) (71199 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849093376 7849126144 88595 _ _ (455673 / 20000) (17819 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849093376 7849126144 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849126144 :
    ThetaLowerSegment 7849126144 7849158912 (156952214958287 / 20000) (31390573860943 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849126144 33 20 (455673 / 20000) (71199 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849126144 7849158912 88595 _ _ (455673 / 20000) (17819 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849126144 7849158912 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849158912 :
    ThetaLowerSegment 7849158912 7849191680 (31390573860943 / 4000) (156953520917391 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849158912 33 20 (1139183 / 50000)
        (2278369 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849158912 7849191680 88595 _ _ (1139183 / 50000) (890951 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849158912 7849191680 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849191680 :
    ThetaLowerSegment 7849191680 7849224448 (156953520917391 / 20000)
      (784770823918113 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849191680 33 20 (1139183 / 50000)
        (2278369 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849191680 7849224448 88595 _ _ (1139183 / 50000) (890951 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849191680 7849224448 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849224448 :
    ThetaLowerSegment 7849224448 7849257216 (784770823918113 / 100000)
      (392387083141251 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849224448 33 20 (2278367 / 100000)
        (227837 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849224448 7849257216 88595 _ _ (2278367 / 100000) (111369 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849224448 7849257216 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849257216 :
    ThetaLowerSegment 7849257216 7849289984 (392387083141251 / 50000)
      (392388687111619 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849257216 33 20 (2278367 / 100000)
        (227837 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849257216 7849289984 88596 _ _ (2278367 / 100000) (111369 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849257216 7849289984 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849289984 :
    ThetaLowerSegment 7849289984 7849322752 (392388687111619 / 50000)
      (784780620896213 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849289984 33 20 (2278367 / 100000)
        (227837 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849289984 7849322752 88596 _ _ (2278367 / 100000) (111369 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849289984 7849322752 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849322752 :
    ThetaLowerSegment 7849322752 7849339136 (784780620896213 / 100000)
      (784782345620789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849322752 33 20 (71199 / 3125)
        (2278371 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849322752 7849339136 88596 _ _ (71199 / 3125) (356381 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849322752 7849339136 11 757 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849339136 :
    ThetaLowerSegment 7849339136 7849341184 (784782345620789 / 100000)
      (784782495993077 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849339136 33 20 (71199 / 3125)
        (2278371 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849339136 7849341184 88596 _ _ (71199 / 3125) (356381 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849339136 7849341184 8 66 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

/-- This window supplies its exit bound and covers its real interval from a scalar entrance. -/
public theorem gap_window_7849341184 :
    ThetaLowerSegment 7817341184 7849341184 (156316020818271 / 20000)
      (784782495993077 / 100000) := by
  exact
    ((((((((((cell7817341184.join cell7817373952).join (cell7817406720.join cell7817439488)).join
                                  ((cell7817472256.join cell7817505024).join
                                    (cell7817537792.join cell7817570560))).join
                              (((cell7817603328.join cell7817636096).join
                                    (cell7817668864.join cell7817701632)).join
                                ((cell7817734400.join cell7817767168).join
                                  (cell7817799936.join cell7817832704)))).join
                          ((((cell7817865472.join cell7817898240).join
                                    (cell7817931008.join cell7817963776)).join
                                ((cell7817980160.join cell7817996544).join
                                  (cell7818029312.join cell7818045696))).join
                            (((cell7818062080.join cell7818078464).join
                                  (cell7818094848.join cell7818111232)).join
                              ((cell7818144000.join cell7818160384).join
                                (cell7818176768.join cell7818193152))))).join
                      (((((cell7818209536.join cell7818225920).join
                                    (cell7818258688.join cell7818275072)).join
                                ((cell7818291456.join cell7818324224).join
                                  (cell7818340608.join cell7818356992))).join
                            (((cell7818373376.join cell7818389760).join
                                  (cell7818406144.join cell7818422528)).join
                              ((cell7818438912.join cell7818455296).join
                                (cell7818471680.join cell7818488064)))).join
                        ((((cell7818504448.join cell7818520832).join
                                  (cell7818537216.join cell7818553600)).join
                              ((cell7818569984.join cell7818586368).join
                                (cell7818619136.join cell7818651904))).join
                          (((cell7818684672.join cell7818701056).join
                                (cell7818733824.join cell7818766592)).join
                            ((cell7818799360.join cell7818832128).join
                              (cell7818864896.join cell7818897664)))))).join
                  ((((((cell7818930432.join cell7818963200).join
                                    (cell7818995968.join cell7819028736)).join
                                ((cell7819061504.join cell7819094272).join
                                  (cell7819127040.join cell7819159808))).join
                            (((cell7819192576.join cell7819225344).join
                                  (cell7819258112.join cell7819290880)).join
                              ((cell7819323648.join cell7819356416).join
                                (cell7819389184.join cell7819421952)))).join
                        ((((cell7819454720.join cell7819487488).join
                                  (cell7819520256.join cell7819553024)).join
                              ((cell7819585792.join cell7819618560).join
                                (cell7819651328.join cell7819684096))).join
                          (((cell7819716864.join cell7819749632).join
                                (cell7819782400.join cell7819815168)).join
                            ((cell7819847936.join cell7819880704).join
                              (cell7819913472.join cell7819946240))))).join
                    (((((cell7819979008.join cell7820011776).join
                                  (cell7820044544.join cell7820077312)).join
                              ((cell7820110080.join cell7820142848).join
                                (cell7820175616.join cell7820208384))).join
                          (((cell7820241152.join cell7820273920).join
                                (cell7820306688.join cell7820339456)).join
                            ((cell7820372224.join cell7820404992).join
                              (cell7820437760.join cell7820470528)))).join
                      ((((cell7820503296.join cell7820536064).join
                                (cell7820568832.join cell7820601600)).join
                            ((cell7820634368.join cell7820667136).join
                              (cell7820699904.join cell7820732672))).join
                        (((cell7820765440.join cell7820798208).join
                              (cell7820830976.join cell7820863744)).join
                          ((cell7820896512.join cell7820912896).join
                            (cell7820929280.join cell7820945664))))))).join
              (((((((cell7820978432.join cell7821011200).join
                                    (cell7821043968.join cell7821076736)).join
                                ((cell7821109504.join cell7821142272).join
                                  (cell7821175040.join cell7821207808))).join
                            (((cell7821240576.join cell7821273344).join
                                  (cell7821306112.join cell7821338880)).join
                              ((cell7821371648.join cell7821404416).join
                                (cell7821437184.join cell7821469952)))).join
                        ((((cell7821502720.join cell7821535488).join
                                  (cell7821568256.join cell7821601024)).join
                              ((cell7821633792.join cell7821666560).join
                                (cell7821699328.join cell7821732096))).join
                          (((cell7821764864.join cell7821797632).join
                                (cell7821830400.join cell7821863168)).join
                            ((cell7821895936.join cell7821928704).join
                              (cell7821961472.join cell7821994240))))).join
                    (((((cell7822027008.join cell7822059776).join
                                  (cell7822092544.join cell7822125312)).join
                              ((cell7822158080.join cell7822190848).join
                                (cell7822223616.join cell7822256384))).join
                          (((cell7822289152.join cell7822321920).join
                                (cell7822354688.join cell7822387456)).join
                            ((cell7822420224.join cell7822452992).join
                              (cell7822485760.join cell7822518528)))).join
                      ((((cell7822551296.join cell7822584064).join
                                (cell7822616832.join cell7822649600)).join
                            ((cell7822682368.join cell7822715136).join
                              (cell7822747904.join cell7822780672))).join
                        (((cell7822813440.join cell7822846208).join
                              (cell7822878976.join cell7822911744)).join
                          ((cell7822944512.join cell7822977280).join
                            (cell7823010048.join cell7823042816)))))).join
                ((((((cell7823075584.join cell7823108352).join
                                  (cell7823141120.join cell7823173888)).join
                              ((cell7823206656.join cell7823239424).join
                                (cell7823272192.join cell7823304960))).join
                          (((cell7823337728.join cell7823370496).join
                                (cell7823403264.join cell7823436032)).join
                            ((cell7823468800.join cell7823501568).join
                              (cell7823534336.join cell7823567104)))).join
                      ((((cell7823599872.join cell7823632640).join
                                (cell7823665408.join cell7823698176)).join
                            ((cell7823730944.join cell7823763712).join
                              (cell7823796480.join cell7823829248))).join
                        (((cell7823862016.join cell7823894784).join
                              (cell7823927552.join cell7823960320)).join
                          ((cell7823993088.join cell7824025856).join
                            (cell7824058624.join cell7824091392))))).join
                  (((((cell7824124160.join cell7824156928).join
                                (cell7824189696.join cell7824222464)).join
                            ((cell7824255232.join cell7824288000).join
                              (cell7824320768.join cell7824353536))).join
                        (((cell7824386304.join cell7824419072).join
                              (cell7824451840.join cell7824484608)).join
                          ((cell7824517376.join cell7824550144).join
                            (cell7824582912.join cell7824615680)))).join
                    ((((cell7824648448.join cell7824681216).join
                              (cell7824713984.join cell7824746752)).join
                          ((cell7824779520.join cell7824812288).join
                            (cell7824845056.join cell7824877824))).join
                      (((cell7824910592.join cell7824943360).join
                            (cell7824976128.join cell7825008896)).join
                        ((cell7825041664.join cell7825074432).join
                          (cell7825107200.join cell7825139968)))))))).join
          ((((((((cell7825172736.join cell7825205504).join
                                    (cell7825238272.join cell7825271040)).join
                                ((cell7825303808.join cell7825336576).join
                                  (cell7825369344.join cell7825402112))).join
                            (((cell7825434880.join cell7825467648).join
                                  (cell7825500416.join cell7825533184)).join
                              ((cell7825565952.join cell7825598720).join
                                (cell7825631488.join cell7825664256)))).join
                        ((((cell7825697024.join cell7825729792).join
                                  (cell7825762560.join cell7825795328)).join
                              ((cell7825828096.join cell7825860864).join
                                (cell7825893632.join cell7825926400))).join
                          (((cell7825959168.join cell7825991936).join
                                (cell7826024704.join cell7826057472)).join
                            ((cell7826090240.join cell7826123008).join
                              (cell7826155776.join cell7826188544))))).join
                    (((((cell7826221312.join cell7826254080).join
                                  (cell7826286848.join cell7826319616)).join
                              ((cell7826352384.join cell7826385152).join
                                (cell7826417920.join cell7826450688))).join
                          (((cell7826483456.join cell7826516224).join
                                (cell7826548992.join cell7826581760)).join
                            ((cell7826614528.join cell7826647296).join
                              (cell7826680064.join cell7826712832)))).join
                      ((((cell7826745600.join cell7826778368).join
                                (cell7826811136.join cell7826843904)).join
                            ((cell7826876672.join cell7826909440).join
                              (cell7826942208.join cell7826974976))).join
                        (((cell7827007744.join cell7827040512).join
                              (cell7827073280.join cell7827106048)).join
                          ((cell7827138816.join cell7827171584).join
                            (cell7827204352.join cell7827237120)))))).join
                ((((((cell7827269888.join cell7827302656).join
                                  (cell7827335424.join cell7827368192)).join
                              ((cell7827400960.join cell7827433728).join
                                (cell7827466496.join cell7827499264))).join
                          (((cell7827532032.join cell7827564800).join
                                (cell7827597568.join cell7827630336)).join
                            ((cell7827663104.join cell7827695872).join
                              (cell7827728640.join cell7827761408)))).join
                      ((((cell7827794176.join cell7827826944).join
                                (cell7827859712.join cell7827892480)).join
                            ((cell7827925248.join cell7827958016).join
                              (cell7827990784.join cell7828023552))).join
                        (((cell7828056320.join cell7828089088).join
                              (cell7828121856.join cell7828154624)).join
                          ((cell7828187392.join cell7828220160).join
                            (cell7828252928.join cell7828285696))))).join
                  (((((cell7828318464.join cell7828351232).join
                                (cell7828384000.join cell7828416768)).join
                            ((cell7828449536.join cell7828482304).join
                              (cell7828515072.join cell7828547840))).join
                        (((cell7828580608.join cell7828613376).join
                              (cell7828646144.join cell7828678912)).join
                          ((cell7828711680.join cell7828744448).join
                            (cell7828777216.join cell7828809984)))).join
                    ((((cell7828842752.join cell7828875520).join
                              (cell7828908288.join cell7828941056)).join
                          ((cell7828973824.join cell7829006592).join
                            (cell7829039360.join cell7829072128))).join
                      (((cell7829104896.join cell7829137664).join
                            (cell7829170432.join cell7829203200)).join
                        ((cell7829235968.join cell7829268736).join
                          (cell7829301504.join cell7829334272))))))).join
            (((((((cell7829367040.join cell7829399808).join
                                  (cell7829432576.join cell7829465344)).join
                              ((cell7829498112.join cell7829530880).join
                                (cell7829563648.join cell7829596416))).join
                          (((cell7829629184.join cell7829661952).join
                                (cell7829694720.join cell7829727488)).join
                            ((cell7829760256.join cell7829793024).join
                              (cell7829825792.join cell7829858560)))).join
                      ((((cell7829891328.join cell7829924096).join
                                (cell7829956864.join cell7829989632)).join
                            ((cell7830022400.join cell7830055168).join
                              (cell7830087936.join cell7830120704))).join
                        (((cell7830153472.join cell7830186240).join
                              (cell7830219008.join cell7830251776)).join
                          ((cell7830284544.join cell7830317312).join
                            (cell7830350080.join cell7830382848))))).join
                  (((((cell7830415616.join cell7830448384).join
                                (cell7830481152.join cell7830513920)).join
                            ((cell7830546688.join cell7830579456).join
                              (cell7830612224.join cell7830644992))).join
                        (((cell7830677760.join cell7830710528).join
                              (cell7830743296.join cell7830776064)).join
                          ((cell7830808832.join cell7830841600).join
                            (cell7830874368.join cell7830907136)))).join
                    ((((cell7830939904.join cell7830972672).join
                              (cell7831005440.join cell7831038208)).join
                          ((cell7831070976.join cell7831103744).join
                            (cell7831136512.join cell7831169280))).join
                      (((cell7831202048.join cell7831234816).join
                            (cell7831267584.join cell7831300352)).join
                        ((cell7831333120.join cell7831365888).join
                          (cell7831398656.join cell7831431424)))))).join
              ((((((cell7831464192.join cell7831496960).join
                                (cell7831529728.join cell7831562496)).join
                            ((cell7831595264.join cell7831628032).join
                              (cell7831660800.join cell7831693568))).join
                        (((cell7831726336.join cell7831759104).join
                              (cell7831791872.join cell7831824640)).join
                          ((cell7831857408.join cell7831890176).join
                            (cell7831922944.join cell7831955712)))).join
                    ((((cell7831988480.join cell7832021248).join
                              (cell7832054016.join cell7832086784)).join
                          ((cell7832119552.join cell7832152320).join
                            (cell7832185088.join cell7832217856))).join
                      (((cell7832250624.join cell7832283392).join
                            (cell7832316160.join cell7832348928)).join
                        ((cell7832381696.join cell7832414464).join
                          (cell7832447232.join cell7832480000))))).join
                (((((cell7832512768.join cell7832545536).join
                              (cell7832578304.join cell7832611072)).join
                          ((cell7832643840.join cell7832676608).join
                            (cell7832709376.join cell7832742144))).join
                      (((cell7832774912.join cell7832807680).join
                            (cell7832840448.join cell7832873216)).join
                        ((cell7832905984.join cell7832938752).join
                          (cell7832971520.join cell7833004288)))).join
                  ((((cell7833037056.join cell7833069824).join
                            (cell7833102592.join cell7833135360)).join
                        ((cell7833168128.join cell7833200896).join
                          (cell7833233664.join cell7833266432))).join
                    (((cell7833299200.join cell7833331968).join
                          (cell7833364736.join cell7833397504)).join
                      ((cell7833430272.join cell7833463040).join
                        (cell7833495808.join cell7833528576))))))))).join
      (((((((((cell7833561344.join cell7833594112).join (cell7833626880.join cell7833659648)).join
                                ((cell7833692416.join cell7833725184).join
                                  (cell7833757952.join cell7833790720))).join
                            (((cell7833823488.join cell7833856256).join
                                  (cell7833889024.join cell7833921792)).join
                              ((cell7833954560.join cell7833987328).join
                                (cell7834020096.join cell7834052864)))).join
                        ((((cell7834085632.join cell7834118400).join
                                  (cell7834151168.join cell7834183936)).join
                              ((cell7834216704.join cell7834249472).join
                                (cell7834282240.join cell7834315008))).join
                          (((cell7834347776.join cell7834380544).join
                                (cell7834413312.join cell7834446080)).join
                            ((cell7834478848.join cell7834511616).join
                              (cell7834544384.join cell7834577152))))).join
                    (((((cell7834609920.join cell7834642688).join
                                  (cell7834675456.join cell7834708224)).join
                              ((cell7834740992.join cell7834773760).join
                                (cell7834806528.join cell7834839296))).join
                          (((cell7834872064.join cell7834904832).join
                                (cell7834937600.join cell7834970368)).join
                            ((cell7835003136.join cell7835035904).join
                              (cell7835068672.join cell7835101440)))).join
                      ((((cell7835134208.join cell7835166976).join
                                (cell7835199744.join cell7835232512)).join
                            ((cell7835265280.join cell7835298048).join
                              (cell7835330816.join cell7835363584))).join
                        (((cell7835396352.join cell7835429120).join
                              (cell7835461888.join cell7835494656)).join
                          ((cell7835527424.join cell7835560192).join
                            (cell7835592960.join cell7835625728)))))).join
                ((((((cell7835658496.join cell7835691264).join
                                  (cell7835724032.join cell7835756800)).join
                              ((cell7835789568.join cell7835822336).join
                                (cell7835855104.join cell7835887872))).join
                          (((cell7835920640.join cell7835953408).join
                                (cell7835986176.join cell7836018944)).join
                            ((cell7836051712.join cell7836084480).join
                              (cell7836117248.join cell7836150016)))).join
                      ((((cell7836182784.join cell7836215552).join
                                (cell7836248320.join cell7836281088)).join
                            ((cell7836313856.join cell7836346624).join
                              (cell7836379392.join cell7836412160))).join
                        (((cell7836444928.join cell7836477696).join
                              (cell7836510464.join cell7836543232)).join
                          ((cell7836576000.join cell7836608768).join
                            (cell7836641536.join cell7836674304))))).join
                  (((((cell7836707072.join cell7836739840).join
                                (cell7836772608.join cell7836805376)).join
                            ((cell7836838144.join cell7836870912).join
                              (cell7836903680.join cell7836936448))).join
                        (((cell7836969216.join cell7837001984).join
                              (cell7837034752.join cell7837067520)).join
                          ((cell7837100288.join cell7837133056).join
                            (cell7837165824.join cell7837198592)))).join
                    ((((cell7837231360.join cell7837264128).join
                              (cell7837296896.join cell7837329664)).join
                          ((cell7837362432.join cell7837395200).join
                            (cell7837427968.join cell7837460736))).join
                      (((cell7837493504.join cell7837526272).join
                            (cell7837559040.join cell7837591808)).join
                        ((cell7837624576.join cell7837657344).join
                          (cell7837690112.join cell7837722880))))))).join
            (((((((cell7837755648.join cell7837788416).join
                                  (cell7837821184.join cell7837853952)).join
                              ((cell7837886720.join cell7837919488).join
                                (cell7837952256.join cell7837985024))).join
                          (((cell7838017792.join cell7838050560).join
                                (cell7838083328.join cell7838116096)).join
                            ((cell7838148864.join cell7838181632).join
                              (cell7838214400.join cell7838247168)))).join
                      ((((cell7838279936.join cell7838312704).join
                                (cell7838345472.join cell7838378240)).join
                            ((cell7838411008.join cell7838443776).join
                              (cell7838476544.join cell7838509312))).join
                        (((cell7838542080.join cell7838574848).join
                              (cell7838607616.join cell7838640384)).join
                          ((cell7838673152.join cell7838705920).join
                            (cell7838738688.join cell7838771456))))).join
                  (((((cell7838804224.join cell7838836992).join
                                (cell7838869760.join cell7838902528)).join
                            ((cell7838935296.join cell7838968064).join
                              (cell7839000832.join cell7839033600))).join
                        (((cell7839066368.join cell7839099136).join
                              (cell7839131904.join cell7839164672)).join
                          ((cell7839197440.join cell7839230208).join
                            (cell7839262976.join cell7839295744)))).join
                    ((((cell7839328512.join cell7839361280).join
                              (cell7839394048.join cell7839426816)).join
                          ((cell7839459584.join cell7839492352).join
                            (cell7839525120.join cell7839557888))).join
                      (((cell7839590656.join cell7839623424).join
                            (cell7839656192.join cell7839688960)).join
                        ((cell7839721728.join cell7839754496).join
                          (cell7839787264.join cell7839820032)))))).join
              ((((((cell7839852800.join cell7839885568).join
                                (cell7839918336.join cell7839951104)).join
                            ((cell7839983872.join cell7840016640).join
                              (cell7840049408.join cell7840082176))).join
                        (((cell7840114944.join cell7840147712).join
                              (cell7840180480.join cell7840213248)).join
                          ((cell7840246016.join cell7840278784).join
                            (cell7840311552.join cell7840344320)))).join
                    ((((cell7840377088.join cell7840409856).join
                              (cell7840442624.join cell7840475392)).join
                          ((cell7840508160.join cell7840540928).join
                            (cell7840573696.join cell7840606464))).join
                      (((cell7840639232.join cell7840672000).join
                            (cell7840704768.join cell7840737536)).join
                        ((cell7840770304.join cell7840803072).join
                          (cell7840835840.join cell7840868608))))).join
                (((((cell7840901376.join cell7840934144).join
                              (cell7840966912.join cell7840999680)).join
                          ((cell7841032448.join cell7841065216).join
                            (cell7841097984.join cell7841130752))).join
                      (((cell7841163520.join cell7841196288).join
                            (cell7841229056.join cell7841261824)).join
                        ((cell7841294592.join cell7841327360).join
                          (cell7841360128.join cell7841392896)))).join
                  ((((cell7841425664.join cell7841458432).join
                            (cell7841491200.join cell7841523968)).join
                        ((cell7841556736.join cell7841589504).join
                          (cell7841622272.join cell7841655040))).join
                    (((cell7841687808.join cell7841720576).join
                          (cell7841753344.join cell7841786112)).join
                      ((cell7841818880.join cell7841851648).join
                        (cell7841884416.join cell7841917184)))))))).join
        ((((((((cell7841949952.join cell7841982720).join (cell7842015488.join cell7842048256)).join
                              ((cell7842081024.join cell7842113792).join
                                (cell7842146560.join cell7842179328))).join
                          (((cell7842212096.join cell7842244864).join
                                (cell7842277632.join cell7842310400)).join
                            ((cell7842343168.join cell7842375936).join
                              (cell7842408704.join cell7842441472)))).join
                      ((((cell7842474240.join cell7842507008).join
                                (cell7842539776.join cell7842572544)).join
                            ((cell7842605312.join cell7842638080).join
                              (cell7842670848.join cell7842703616))).join
                        (((cell7842736384.join cell7842769152).join
                              (cell7842801920.join cell7842834688)).join
                          ((cell7842867456.join cell7842900224).join
                            (cell7842932992.join cell7842965760))))).join
                  (((((cell7842998528.join cell7843031296).join
                                (cell7843064064.join cell7843096832)).join
                            ((cell7843129600.join cell7843162368).join
                              (cell7843195136.join cell7843227904))).join
                        (((cell7843260672.join cell7843293440).join
                              (cell7843326208.join cell7843358976)).join
                          ((cell7843391744.join cell7843424512).join
                            (cell7843457280.join cell7843490048)))).join
                    ((((cell7843522816.join cell7843555584).join
                              (cell7843588352.join cell7843621120)).join
                          ((cell7843653888.join cell7843686656).join
                            (cell7843719424.join cell7843752192))).join
                      (((cell7843784960.join cell7843817728).join
                            (cell7843850496.join cell7843883264)).join
                        ((cell7843916032.join cell7843948800).join
                          (cell7843981568.join cell7844014336)))))).join
              ((((((cell7844047104.join cell7844079872).join
                                (cell7844112640.join cell7844145408)).join
                            ((cell7844178176.join cell7844210944).join
                              (cell7844243712.join cell7844276480))).join
                        (((cell7844309248.join cell7844342016).join
                              (cell7844374784.join cell7844407552)).join
                          ((cell7844440320.join cell7844473088).join
                            (cell7844505856.join cell7844538624)))).join
                    ((((cell7844571392.join cell7844604160).join
                              (cell7844636928.join cell7844669696)).join
                          ((cell7844702464.join cell7844735232).join
                            (cell7844768000.join cell7844800768))).join
                      (((cell7844833536.join cell7844866304).join
                            (cell7844899072.join cell7844931840)).join
                        ((cell7844964608.join cell7844997376).join
                          (cell7845030144.join cell7845062912))))).join
                (((((cell7845095680.join cell7845128448).join
                              (cell7845161216.join cell7845193984)).join
                          ((cell7845226752.join cell7845259520).join
                            (cell7845292288.join cell7845325056))).join
                      (((cell7845357824.join cell7845390592).join
                            (cell7845423360.join cell7845456128)).join
                        ((cell7845488896.join cell7845521664).join
                          (cell7845554432.join cell7845587200)))).join
                  ((((cell7845619968.join cell7845652736).join
                            (cell7845685504.join cell7845718272)).join
                        ((cell7845751040.join cell7845783808).join
                          (cell7845816576.join cell7845849344))).join
                    (((cell7845882112.join cell7845914880).join
                          (cell7845947648.join cell7845980416)).join
                      ((cell7846013184.join cell7846045952).join
                        (cell7846078720.join cell7846111488))))))).join
          (((((((cell7846144256.join cell7846177024).join (cell7846209792.join cell7846242560)).join
                            ((cell7846275328.join cell7846308096).join
                              (cell7846340864.join cell7846373632))).join
                        (((cell7846406400.join cell7846439168).join
                              (cell7846471936.join cell7846504704)).join
                          ((cell7846537472.join cell7846570240).join
                            (cell7846603008.join cell7846635776)))).join
                    ((((cell7846668544.join cell7846701312).join
                              (cell7846734080.join cell7846766848)).join
                          ((cell7846799616.join cell7846832384).join
                            (cell7846865152.join cell7846897920))).join
                      (((cell7846930688.join cell7846963456).join
                            (cell7846996224.join cell7847028992)).join
                        ((cell7847061760.join cell7847094528).join
                          (cell7847127296.join cell7847160064))))).join
                (((((cell7847192832.join cell7847225600).join
                              (cell7847258368.join cell7847291136)).join
                          ((cell7847323904.join cell7847356672).join
                            (cell7847389440.join cell7847422208))).join
                      (((cell7847454976.join cell7847487744).join
                            (cell7847520512.join cell7847553280)).join
                        ((cell7847586048.join cell7847618816).join
                          (cell7847651584.join cell7847684352)))).join
                  ((((cell7847717120.join cell7847749888).join
                            (cell7847782656.join cell7847815424)).join
                        ((cell7847848192.join cell7847880960).join
                          (cell7847913728.join cell7847946496))).join
                    (((cell7847979264.join cell7848012032).join
                          (cell7848044800.join cell7848077568)).join
                      ((cell7848110336.join cell7848143104).join
                        (cell7848175872.join cell7848208640)))))).join
            ((((((cell7848241408.join cell7848274176).join
                              (cell7848306944.join cell7848339712)).join
                          ((cell7848372480.join cell7848405248).join
                            (cell7848438016.join cell7848470784))).join
                      (((cell7848503552.join cell7848536320).join
                            (cell7848569088.join cell7848601856)).join
                        ((cell7848634624.join cell7848667392).join
                          (cell7848700160.join cell7848732928)))).join
                  ((((cell7848765696.join cell7848798464).join
                            (cell7848831232.join cell7848864000)).join
                        ((cell7848896768.join cell7848929536).join
                          (cell7848962304.join cell7848995072))).join
                    (((cell7849027840.join cell7849060608).join
                          (cell7849093376.join cell7849126144)).join
                      ((cell7849158912.join cell7849191680).join
                        (cell7849224448.join cell7849257216))))).join
              ((cell7849289984.join cell7849322752).join cell7849339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
