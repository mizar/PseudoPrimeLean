/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartCell
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Finite gap estimate up to 7886980184 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell7881341184 :
    ThetaLowerSegment 7881341184 7881373952 (787980696495567 / 100000) (24624500948231 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881341184 33 20 (91151 / 4000)
        (1139389 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881341184 7881373952 88776 _ _ (91151 / 4000) (1782577 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881341184 7881373952 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881373952 :
    ThetaLowerSegment 7881373952 7881406720 (24624500948231 / 3125) (787987377863867 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881373952 33 20 (91151 / 4000)
        (1139389 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881373952 7881406720 88777 _ _ (91151 / 4000) (1782577 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881373952 7881406720 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881406720 :
    ThetaLowerSegment 7881406720 7881439488 (787987377863867 / 100000)
      (787990661580083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881406720 33 20 (284847 / 12500)
        (2278779 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881406720 7881439488 88777 _ _ (284847 / 12500) (1782579 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881406720 7881439488 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881439488 :
    ThetaLowerSegment 7881439488 7881472256 (787990661580083 / 100000)
      (787993961247731 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881439488 33 20 (284847 / 12500)
        (2278779 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881439488 7881472256 88777 _ _ (284847 / 12500) (1782579 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881439488 7881472256 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881472256 :
    ThetaLowerSegment 7881472256 7881505024 (787993961247731 / 100000)
      (78799721306251 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881472256 33 20 (2278777 / 100000)
        (113939 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881472256 7881505024 88777 _ _ (2278777 / 100000) (1782581 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881472256 7881505024 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881505024 :
    ThetaLowerSegment 7881505024 7881537792 (78799721306251 / 10000) (157600105736609 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881505024 33 20 (2278777 / 100000)
        (113939 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881505024 7881537792 88777 _ _ (2278777 / 100000) (1782581 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881505024 7881537792 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881537792 :
    ThetaLowerSegment 7881537792 7881570560 (157600105736609 / 20000)
      (788003823794587 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881537792 33 20 (2278777 / 100000)
        (113939 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881537792 7881570560 88778 _ _ (2278777 / 100000) (1782581 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881537792 7881570560 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881570560 :
    ThetaLowerSegment 7881570560 7881603328 (788003823794587 / 100000)
      (788007018641343 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881570560 33 20 (1139389 / 50000)
        (2278781 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881570560 7881603328 88778 _ _ (1139389 / 50000) (891291 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881570560 7881603328 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881603328 :
    ThetaLowerSegment 7881603328 7881636096 (788007018641343 / 100000)
      (788010231718323 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881603328 33 20 (1139389 / 50000)
        (2278781 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881603328 7881636096 88778 _ _ (1139389 / 50000) (891291 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881603328 7881636096 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881636096 :
    ThetaLowerSegment 7881636096 7881668864 (788010231718323 / 100000)
      (788013608868801 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881636096 33 20 (2278779 / 100000)
        (1139391 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881636096 7881668864 88778 _ _ (2278779 / 100000) (222823 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881636096 7881668864 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881668864 :
    ThetaLowerSegment 7881668864 7881701632 (788013608868801 / 100000)
      (157603389911763 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881668864 33 20 (2278779 / 100000)
        (1139391 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881668864 7881701632 88778 _ _ (2278779 / 100000) (222823 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881668864 7881701632 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881701632 :
    ThetaLowerSegment 7881701632 7881734400 (157603389911763 / 20000)
      (788020167194763 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881701632 33 20 (2278779 / 100000)
        (1139391 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881701632 7881734400 88778 _ _ (2278779 / 100000) (222823 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881701632 7881734400 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881734400 :
    ThetaLowerSegment 7881734400 7881767168 (788020167194763 / 100000)
      (788023464589423 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881734400 33 20 (113939 / 5000)
        (2278783 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881734400 7881767168 88779 _ _ (113939 / 5000) (891293 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881734400 7881767168 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881767168 :
    ThetaLowerSegment 7881767168 7881799936 (788023464589423 / 100000)
      (788026812117243 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881767168 33 20 (113939 / 5000)
        (2278783 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881767168 7881799936 88779 _ _ (113939 / 5000) (891293 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881767168 7881799936 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881799936 :
    ThetaLowerSegment 7881799936 7881832704 (788026812117243 / 100000)
      (788030130022379 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881799936 33 20 (2278781 / 100000)
        (71212 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881799936 7881832704 88779 _ _ (2278781 / 100000) (1782587 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881799936 7881832704 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881832704 :
    ThetaLowerSegment 7881832704 7881865472 (788030130022379 / 100000)
      (98504167603101 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881832704 33 20 (2278781 / 100000)
        (71212 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881832704 7881865472 88779 _ _ (2278781 / 100000) (1782587 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881832704 7881865472 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881865472 :
    ThetaLowerSegment 7881865472 7881898240 (98504167603101 / 12500) (24626140173249 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881865472 33 20 (1139391 / 50000)
        (455757 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881865472 7881898240 88779 _ _ (1139391 / 50000) (1782589 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881865472 7881898240 12 1380 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881898240 :
    ThetaLowerSegment 7881898240 7881931008 (24626140173249 / 3125) (394019875519287 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881898240 33 20 (1139391 / 50000)
        (455757 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881898240 7881931008 88780 _ _ (1139391 / 50000) (1782589 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881898240 7881931008 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881931008 :
    ThetaLowerSegment 7881931008 7881963776 (394019875519287 / 50000) (24626345263629 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881931008 33 20 (1139391 / 50000)
        (455757 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881931008 7881963776 88780 _ _ (1139391 / 50000) (1782589 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881931008 7881963776 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881963776 :
    ThetaLowerSegment 7881963776 7881996544 (24626345263629 / 3125) (788046318489733 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881963776 33 20 (2278783 / 100000)
        (1139393 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881963776 7881996544 88780 _ _ (2278783 / 100000) (1782591 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881963776 7881996544 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881996544 :
    ThetaLowerSegment 7881996544 7882029312 (788046318489733 / 100000)
      (788049618167517 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881996544 33 20 (2278783 / 100000)
        (1139393 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881996544 7882029312 88780 _ _ (2278783 / 100000) (1782591 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881996544 7882029312 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882029312 :
    ThetaLowerSegment 7882029312 7882062080 (788049618167517 / 100000)
      (788052897337693 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882029312 33 20 (71212 / 3125)
        (2278787 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882029312 7882062080 88780 _ _ (71212 / 3125) (55706 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882029312 7882062080 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882062080 :
    ThetaLowerSegment 7882062080 7882094848 (788052897337693 / 100000)
      (788056146883677 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882062080 33 20 (71212 / 3125)
        (2278787 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882062080 7882094848 88780 _ _ (71212 / 3125) (55706 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882062080 7882094848 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882094848 :
    ThetaLowerSegment 7882094848 7882127616 (788056146883677 / 100000)
      (788059350853981 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882094848 33 20 (71212 / 3125)
        (2278787 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882094848 7882127616 88781 _ _ (71212 / 3125) (55706 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882094848 7882127616 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882127616 :
    ThetaLowerSegment 7882127616 7882160384 (788059350853981 / 100000)
      (394031344637003 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882127616 33 20 (455757 / 20000)
        (569697 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882127616 7882160384 88781 _ _ (455757 / 20000) (891297 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882127616 7882160384 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882160384 :
    ThetaLowerSegment 7882160384 7882193152 (394031344637003 / 50000)
      (788065977560761 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882160384 33 20 (455757 / 20000)
        (569697 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882160384 7882193152 88781 _ _ (455757 / 20000) (891297 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882160384 7882193152 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882193152 :
    ThetaLowerSegment 7882193152 7882225920 (788065977560761 / 100000)
      (788069240782313 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882193152 33 20 (1139393 / 50000)
        (2278789 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882193152 7882225920 88781 _ _ (1139393 / 50000) (445649 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882193152 7882225920 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882225920 :
    ThetaLowerSegment 7882225920 7882258688 (788069240782313 / 100000)
      (788072499446293 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882225920 33 20 (1139393 / 50000)
        (2278789 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882225920 7882258688 88781 _ _ (1139393 / 50000) (445649 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882225920 7882258688 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882258688 :
    ThetaLowerSegment 7882258688 7882291456 (788072499446293 / 100000)
      (197018952630951 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882258688 33 20 (2278787 / 100000)
        (227879 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882258688 7882291456 88782 _ _ (2278787 / 100000) (1782597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882258688 7882291456 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882291456 :
    ThetaLowerSegment 7882291456 7882324224 (197018952630951 / 25000)
      (788079016777113 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882291456 33 20 (2278787 / 100000)
        (227879 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882291456 7882324224 88782 _ _ (2278787 / 100000) (1782597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882291456 7882324224 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882324224 :
    ThetaLowerSegment 7882324224 7882356992 (788079016777113 / 100000)
      (197020547781851 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882324224 33 20 (2278787 / 100000)
        (227879 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882324224 7882356992 88782 _ _ (2278787 / 100000) (1782597 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882324224 7882356992 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882356992 :
    ThetaLowerSegment 7882356992 7882389760 (197020547781851 / 25000) (98510690624281 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882356992 33 20 (569697 / 25000)
        (2278791 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882356992 7882389760 88782 _ _ (569697 / 25000) (1782599 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882356992 7882389760 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882389760 :
    ThetaLowerSegment 7882389760 7882422528 (98510690624281 / 12500) (98511105363697 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882389760 33 20 (569697 / 25000)
        (2278791 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882389760 7882422528 88782 _ _ (569697 / 25000) (1782599 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882389760 7882422528 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882422528 :
    ThetaLowerSegment 7882422528 7882455296 (98511105363697 / 12500)
      (788092163105149 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882422528 33 20 (2278789 / 100000)
        (284849 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882422528 7882455296 88783 _ _ (2278789 / 100000) (8913 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882422528 7882455296 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882455296 :
    ThetaLowerSegment 7882455296 7882488064 (788092163105149 / 100000)
      (157619099850449 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882455296 33 20 (2278789 / 100000)
        (284849 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882455296 7882488064 88783 _ _ (2278789 / 100000) (8913 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882455296 7882488064 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882488064 :
    ThetaLowerSegment 7882488064 7882520832 (157619099850449 / 20000)
      (394049382378441 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882488064 33 20 (2278789 / 100000)
        (284849 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882488064 7882520832 88783 _ _ (2278789 / 100000) (8913 / 500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882488064 7882520832 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882520832 :
    ThetaLowerSegment 7882520832 7882553600 (394049382378441 / 50000) (24628187591171 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882520832 33 20 (227879 / 10000)
        (2278793 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882520832 7882553600 88783 _ _ (227879 / 10000) (891301 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882520832 7882553600 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882553600 :
    ThetaLowerSegment 7882553600 7882586368 (24628187591171 / 3125) (24628287857931 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882553600 33 20 (227879 / 10000)
        (2278793 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882553600 7882586368 88783 _ _ (227879 / 10000) (891301 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882553600 7882586368 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882586368 :
    ThetaLowerSegment 7882586368 7882619136 (24628287857931 / 3125) (394054189486641 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882586368 33 20 (2278791 / 100000)
        (1139397 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882586368 7882619136 88783 _ _ (2278791 / 100000) (445651 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882586368 7882619136 12 1390 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882619136 :
    ThetaLowerSegment 7882619136 7882651904 (394054189486641 / 50000) (24628486112748 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882619136 33 20 (2278791 / 100000)
        (1139397 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882619136 7882651904 88784 _ _ (2278791 / 100000) (445651 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882619136 7882651904 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882651904 :
    ThetaLowerSegment 7882651904 7882684672 (24628486112748 / 3125) (49257176462229 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882651904 33 20 (284849 / 12500)
        (455759 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882651904 7882684672 88784 _ _ (284849 / 12500) (356521 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882651904 7882684672 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882684672 :
    ThetaLowerSegment 7882684672 7882717440 (49257176462229 / 6250) (98514757694887 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882684672 33 20 (284849 / 12500)
        (455759 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882684672 7882717440 88784 _ _ (284849 / 12500) (356521 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882684672 7882717440 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882717440 :
    ThetaLowerSegment 7882717440 7882750208 (98514757694887 / 12500) (98515169586541 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882717440 33 20 (284849 / 12500)
        (455759 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882717440 7882750208 88784 _ _ (284849 / 12500) (356521 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882717440 7882750208 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882750208 :
    ThetaLowerSegment 7882750208 7882782976 (98515169586541 / 12500)
      (788124699681659 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882750208 33 20 (2278793 / 100000)
        (569699 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882750208 7882782976 88784 _ _ (2278793 / 100000) (1782607 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882750208 7882782976 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882782976 :
    ThetaLowerSegment 7882782976 7882815744 (788124699681659 / 100000)
      (394064003105151 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882782976 33 20 (2278793 / 100000)
        (569699 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882782976 7882815744 88785 _ _ (2278793 / 100000) (1782607 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882782976 7882815744 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882815744 :
    ThetaLowerSegment 7882815744 7882848512 (394064003105151 / 50000) (7881313492011 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882815744 33 20 (1139397 / 50000)
        (2278797 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882815744 7882848512 88785 _ _ (1139397 / 50000) (1782609 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882815744 7882848512 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882848512 :
    ThetaLowerSegment 7882848512 7882881280 (7881313492011 / 1000) (15762691929651 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882848512 33 20 (1139397 / 50000)
        (2278797 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882848512 7882881280 88785 _ _ (1139397 / 50000) (1782609 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882848512 7882881280 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882881280 :
    ThetaLowerSegment 7882881280 7882914048 (15762691929651 / 2000) (394068957203307 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882881280 33 20 (1139397 / 50000)
        (2278797 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882881280 7882914048 88785 _ _ (1139397 / 50000) (1782609 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882881280 7882914048 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882914048 :
    ThetaLowerSegment 7882914048 7882946816 (394068957203307 / 50000) (98517651193023 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882914048 33 20 (455759 / 20000)
        (1139399 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882914048 7882946816 88785 _ _ (455759 / 20000) (178261 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882914048 7882946816 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882946816 :
    ThetaLowerSegment 7882946816 7882979584 (98517651193023 / 12500) (394072275128827 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882946816 33 20 (455759 / 20000)
        (1139399 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882946816 7882979584 88785 _ _ (455759 / 20000) (178261 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882946816 7882979584 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7882979584 :
    ThetaLowerSegment 7882979584 7883012352 (394072275128827 / 50000)
      (394073919280141 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7882979584 33 20 (569699 / 25000)
        (2278799 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7882979584 7883012352 88786 _ _ (569699 / 25000) (445653 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7882979584 7883012352 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883012352 :
    ThetaLowerSegment 7883012352 7883045120 (394073919280141 / 50000)
      (394075565710251 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883012352 33 20 (569699 / 25000)
        (2278799 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883012352 7883045120 88786 _ _ (569699 / 25000) (445653 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883012352 7883045120 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883045120 :
    ThetaLowerSegment 7883045120 7883077888 (394075565710251 / 50000)
      (788154451627731 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883045120 33 20 (2278797 / 100000) (5697 / 250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883045120 7883077888 88786 _ _ (2278797 / 100000) (891307 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883045120 7883077888 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883077888 :
    ThetaLowerSegment 7883077888 7883110656 (788154451627731 / 100000) (49259865297279 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883077888 33 20 (2278797 / 100000) (5697 / 250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883077888 7883110656 88786 _ _ (2278797 / 100000) (891307 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883077888 7883110656 12 1489 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883110656 :
    ThetaLowerSegment 7883110656 7883143424 (49259865297279 / 6250) (788161051023843 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883110656 33 20 (2278797 / 100000) (5697 / 250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883110656 7883143424 88786 _ _ (2278797 / 100000) (891307 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883110656 7883143424 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883143424 :
    ThetaLowerSegment 7883143424 7883176192 (788161051023843 / 100000)
      (788164446432863 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883143424 33 20 (1139399 / 50000)
        (2278801 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883143424 7883176192 88787 _ _ (1139399 / 50000) (356523 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883143424 7883176192 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883176192 :
    ThetaLowerSegment 7883176192 7883208960 (788164446432863 / 100000)
      (788167768920347 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883176192 33 20 (1139399 / 50000)
        (2278801 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883176192 7883208960 88787 _ _ (1139399 / 50000) (356523 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883176192 7883208960 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883208960 :
    ThetaLowerSegment 7883208960 7883241728 (788167768920347 / 100000)
      (788171068621299 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883208960 33 20 (2278799 / 100000)
        (1139401 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883208960 7883241728 88787 _ _ (2278799 / 100000) (1782617 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883208960 7883241728 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883241728 :
    ThetaLowerSegment 7883241728 7883274496 (788171068621299 / 100000)
      (394087239991701 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883241728 33 20 (2278799 / 100000)
        (1139401 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883241728 7883274496 88787 _ _ (2278799 / 100000) (1782617 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883241728 7883274496 12 1497 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883274496 :
    ThetaLowerSegment 7883274496 7883307264 (394087239991701 / 50000)
      (197044393648111 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883274496 33 20 (2278799 / 100000)
        (1139401 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883274496 7883307264 88787 _ _ (2278799 / 100000) (1782617 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883274496 7883307264 12 1358 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883307264 :
    ThetaLowerSegment 7883307264 7883340032 (197044393648111 / 25000)
      (197045210028211 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883307264 33 20 (5697 / 250) (2278803 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883307264 7883340032 88787 _ _ (5697 / 250) (1782619 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883307264 7883340032 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883340032 :
    ThetaLowerSegment 7883340032 7883372800 (197045210028211 / 25000)
      (197046040650811 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883340032 33 20 (5697 / 250) (2278803 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883340032 7883372800 88788 _ _ (5697 / 250) (1782619 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883340032 7883372800 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883372800 :
    ThetaLowerSegment 7883372800 7883405568 (197046040650811 / 25000)
      (788187482816301 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883372800 33 20 (2278801 / 100000)
        (569701 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883372800 7883405568 88788 _ _ (2278801 / 100000) (89131 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883372800 7883405568 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883405568 :
    ThetaLowerSegment 7883405568 7883438336 (788187482816301 / 100000)
      (788190764289741 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883405568 33 20 (2278801 / 100000)
        (569701 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883405568 7883438336 88788 _ _ (2278801 / 100000) (89131 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883405568 7883438336 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883438336 :
    ThetaLowerSegment 7883438336 7883471104 (788190764289741 / 100000) (49262121451071 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883438336 33 20 (2278801 / 100000)
        (569701 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883438336 7883471104 88788 _ _ (2278801 / 100000) (89131 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883438336 7883471104 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883471104 :
    ThetaLowerSegment 7883471104 7883503872 (49262121451071 / 6250) (394098627158221 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883471104 33 20 (1139401 / 50000)
        (455761 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883471104 7883503872 88788 _ _ (1139401 / 50000) (891311 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883471104 7883503872 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883503872 :
    ThetaLowerSegment 7883503872 7883536640 (394098627158221 / 50000) (24631267526817 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883503872 33 20 (1139401 / 50000)
        (455761 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883503872 7883536640 88789 _ _ (1139401 / 50000) (891311 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883503872 7883536640 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883536640 :
    ThetaLowerSegment 7883536640 7883569408 (24631267526817 / 3125) (98525491685823 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883536640 33 20 (2278803 / 100000)
        (1139403 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883536640 7883569408 88789 _ _ (2278803 / 100000) (55707 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883536640 7883569408 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883569408 :
    ThetaLowerSegment 7883569408 7883602176 (98525491685823 / 12500)
      (788207294721009 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883569408 33 20 (2278803 / 100000)
        (1139403 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883569408 7883602176 88789 _ _ (2278803 / 100000) (55707 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883569408 7883602176 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883602176 :
    ThetaLowerSegment 7883602176 7883634944 (788207294721009 / 100000)
      (788210592150397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883602176 33 20 (569701 / 25000)
        (2278807 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883602176 7883634944 88789 _ _ (569701 / 25000) (14261 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883602176 7883634944 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883634944 :
    ThetaLowerSegment 7883634944 7883667712 (788210592150397 / 100000)
      (788213848561313 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883634944 33 20 (569701 / 25000)
        (2278807 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883634944 7883667712 88789 _ _ (569701 / 25000) (14261 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883634944 7883667712 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883667712 :
    ThetaLowerSegment 7883667712 7883700480 (788213848561313 / 100000)
      (788217075347777 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883667712 33 20 (569701 / 25000)
        (2278807 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883667712 7883700480 88790 _ _ (569701 / 25000) (14261 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883667712 7883700480 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883700480 :
    ThetaLowerSegment 7883700480 7883733248 (788217075347777 / 100000)
      (788220315808487 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883700480 33 20 (455761 / 20000)
        (284851 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883700480 7883733248 88790 _ _ (455761 / 20000) (1782627 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883700480 7883733248 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883733248 :
    ThetaLowerSegment 7883733248 7883766016 (788220315808487 / 100000)
      (788223519808317 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883733248 33 20 (455761 / 20000)
        (284851 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883733248 7883766016 88790 _ _ (455761 / 20000) (1782627 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883733248 7883766016 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883766016 :
    ThetaLowerSegment 7883766016 7883798784 (788223519808317 / 100000)
      (157645354788657 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883766016 33 20 (1139403 / 50000)
        (2278809 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883766016 7883798784 88790 _ _ (1139403 / 50000) (1782629 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883766016 7883798784 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883798784 :
    ThetaLowerSegment 7883798784 7883831552 (157645354788657 / 20000)
      (788229984780939 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883798784 33 20 (1139403 / 50000)
        (2278809 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883798784 7883831552 88790 _ _ (1139403 / 50000) (1782629 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883798784 7883831552 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883831552 :
    ThetaLowerSegment 7883831552 7883864320 (788229984780939 / 100000)
      (788233261703967 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883831552 33 20 (1139403 / 50000)
        (2278809 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883831552 7883864320 88790 _ _ (1139403 / 50000) (1782629 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883831552 7883864320 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883864320 :
    ThetaLowerSegment 7883864320 7883897088 (788233261703967 / 100000)
      (394118268174813 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883864320 33 20 (2278807 / 100000)
        (227881 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883864320 7883897088 88791 _ _ (2278807 / 100000) (178263 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883864320 7883897088 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883897088 :
    ThetaLowerSegment 7883897088 7883929856 (394118268174813 / 50000)
      (197059930530453 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883897088 33 20 (2278807 / 100000)
        (227881 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883897088 7883929856 88791 _ _ (2278807 / 100000) (178263 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883897088 7883929856 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883929856 :
    ThetaLowerSegment 7883929856 7883962624 (197059930530453 / 25000)
      (197060735519379 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883929856 33 20 (284851 / 12500)
        (2278811 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883929856 7883962624 88791 _ _ (284851 / 12500) (222829 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883929856 7883962624 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883962624 :
    ThetaLowerSegment 7883962624 7883995392 (197060735519379 / 25000)
      (197061552472047 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883962624 33 20 (284851 / 12500)
        (2278811 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883962624 7883995392 88791 _ _ (284851 / 12500) (222829 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883962624 7883995392 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7883995392 :
    ThetaLowerSegment 7883995392 7884028160 (197061552472047 / 25000)
      (157649904199533 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7883995392 33 20 (2278809 / 100000)
        (569703 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7883995392 7884028160 88791 _ _ (2278809 / 100000) (891317 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7883995392 7884028160 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884028160 :
    ThetaLowerSegment 7884028160 7884060928 (157649904199533 / 20000)
      (788252670311703 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884028160 33 20 (2278809 / 100000)
        (569703 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884028160 7884060928 88792 _ _ (2278809 / 100000) (891317 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884028160 7884060928 12 1382 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884060928 :
    ThetaLowerSegment 7884060928 7884093696 (788252670311703 / 100000)
      (197064009028149 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884060928 33 20 (2278809 / 100000)
        (569703 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884060928 7884093696 88792 _ _ (2278809 / 100000) (891317 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884060928 7884093696 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884093696 :
    ThetaLowerSegment 7884093696 7884126464 (197064009028149 / 25000)
      (394129673611763 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884093696 33 20 (227881 / 10000)
        (2278813 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884093696 7884126464 88792 _ _ (227881 / 10000) (356527 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884093696 7884126464 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884126464 :
    ThetaLowerSegment 7884126464 7884159232 (394129673611763 / 50000)
      (197065649771349 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884126464 33 20 (227881 / 10000)
        (2278813 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884126464 7884159232 88792 _ _ (227881 / 10000) (356527 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884126464 7884159232 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884159232 :
    ThetaLowerSegment 7884159232 7884192000 (197065649771349 / 25000)
      (394132974468783 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884159232 33 20 (2278811 / 100000)
        (1139407 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884159232 7884192000 88792 _ _ (2278811 / 100000) (1782637 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884159232 7884192000 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884192000 :
    ThetaLowerSegment 7884192000 7884224768 (394132974468783 / 50000)
      (788269223588973 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884192000 33 20 (2278811 / 100000)
        (1139407 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884192000 7884224768 88792 _ _ (2278811 / 100000) (1782637 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884192000 7884224768 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884224768 :
    ThetaLowerSegment 7884224768 7884257536 (788269223588973 / 100000)
      (394136255956623 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884224768 33 20 (2278811 / 100000)
        (1139407 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884224768 7884257536 88793 _ _ (2278811 / 100000) (1782637 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884224768 7884257536 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884257536 :
    ThetaLowerSegment 7884257536 7884290304 (394136255956623 / 50000)
      (394137886446609 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884257536 33 20 (569703 / 25000)
        (455763 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884257536 7884290304 88793 _ _ (569703 / 25000) (891319 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884257536 7884290304 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884290304 :
    ThetaLowerSegment 7884290304 7884323072 (394137886446609 / 50000)
      (394139524912437 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884290304 33 20 (569703 / 25000)
        (455763 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884290304 7884323072 88793 _ _ (569703 / 25000) (891319 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884290304 7884323072 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884323072 :
    ThetaLowerSegment 7884323072 7884355840 (394139524912437 / 50000)
      (157656464895831 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884323072 33 20 (2278813 / 100000)
        (71213 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884323072 7884355840 88793 _ _ (2278813 / 100000) (22283 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884323072 7884355840 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884355840 :
    ThetaLowerSegment 7884355840 7884388608 (157656464895831 / 20000)
      (394142838306539 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884355840 33 20 (2278813 / 100000)
        (71213 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884355840 7884388608 88793 _ _ (2278813 / 100000) (22283 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884355840 7884388608 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884388608 :
    ThetaLowerSegment 7884388608 7884421376 (394142838306539 / 50000)
      (197072230980757 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884388608 33 20 (1139407 / 50000)
        (2278817 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884388608 7884421376 88794 _ _ (1139407 / 50000) (891321 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884388608 7884421376 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884421376 :
    ThetaLowerSegment 7884421376 7884454144 (197072230980757 / 25000) (49268263123301 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884421376 33 20 (1139407 / 50000)
        (2278817 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884421376 7884454144 88794 _ _ (1139407 / 50000) (891321 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884421376 7884454144 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884454144 :
    ThetaLowerSegment 7884454144 7884486912 (49268263123301 / 6250) (39414775256893 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884454144 33 20 (1139407 / 50000)
        (2278817 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884454144 7884486912 88794 _ _ (1139407 / 50000) (891321 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884454144 7884486912 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884486912 :
    ThetaLowerSegment 7884486912 7884519680 (39414775256893 / 5000) (39414933862417 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884486912 33 20 (455763 / 20000)
        (1139409 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884486912 7884519680 88794 _ _ (455763 / 20000) (1782643 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884486912 7884519680 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884519680 :
    ThetaLowerSegment 7884519680 7884552448 (39414933862417 / 5000) (157660383088891 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884519680 33 20 (455763 / 20000)
        (1139409 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884519680 7884552448 88794 _ _ (455763 / 20000) (1782643 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884519680 7884552448 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884552448 :
    ThetaLowerSegment 7884552448 7884585216 (157660383088891 / 20000)
      (157661039387899 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884552448 33 20 (71213 / 3125)
        (2278819 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884552448 7884585216 88795 _ _ (71213 / 3125) (356529 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884552448 7884585216 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884585216 :
    ThetaLowerSegment 7884585216 7884617984 (157661039387899 / 20000)
      (788308653903367 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884585216 33 20 (71213 / 3125)
        (2278819 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884585216 7884617984 88795 _ _ (71213 / 3125) (356529 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884585216 7884617984 12 1517 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884617984 :
    ThetaLowerSegment 7884617984 7884650752 (788308653903367 / 100000)
      (788311889822087 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884617984 33 20 (71213 / 3125)
        (2278819 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884617984 7884650752 88795 _ _ (71213 / 3125) (356529 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884617984 7884650752 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884650752 :
    ThetaLowerSegment 7884650752 7884683520 (788311889822087 / 100000)
      (157663040644401 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884650752 33 20 (2278817 / 100000)
        (113941 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884650752 7884683520 88795 _ _ (2278817 / 100000) (1782647 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884650752 7884683520 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884683520 :
    ThetaLowerSegment 7884683520 7884716288 (157663040644401 / 20000)
      (394159243498651 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884683520 33 20 (2278817 / 100000)
        (113941 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884683520 7884716288 88795 _ _ (2278817 / 100000) (1782647 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884683520 7884716288 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884716288 :
    ThetaLowerSegment 7884716288 7884749056 (394159243498651 / 50000) (78832173659177 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884716288 33 20 (1139409 / 50000)
        (2278821 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884716288 7884749056 88795 _ _ (1139409 / 50000) (222831 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884716288 7884749056 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884749056 :
    ThetaLowerSegment 7884749056 7884781824 (78832173659177 / 10000) (197081243698037 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884749056 33 20 (1139409 / 50000)
        (2278821 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884749056 7884781824 88796 _ _ (1139409 / 50000) (222831 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884749056 7884781824 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884781824 :
    ThetaLowerSegment 7884781824 7884814592 (197081243698037 / 25000) (24635260572781 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884781824 33 20 (2278819 / 100000)
        (1139411 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884781824 7884814592 88796 _ _ (2278819 / 100000) (35653 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884781824 7884814592 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884814592 :
    ThetaLowerSegment 7884814592 7884847360 (24635260572781 / 3125) (788331631222447 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884814592 33 20 (2278819 / 100000)
        (1139411 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884814592 7884847360 88796 _ _ (2278819 / 100000) (35653 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884814592 7884847360 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884847360 :
    ThetaLowerSegment 7884847360 7884880128 (788331631222447 / 100000)
      (788334981086377 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884847360 33 20 (2278819 / 100000)
        (1139411 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884847360 7884880128 88796 _ _ (2278819 / 100000) (35653 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884847360 7884880128 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884880128 :
    ThetaLowerSegment 7884880128 7884912896 (788334981086377 / 100000)
      (788338239798977 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884880128 33 20 (113941 / 5000)
        (2278823 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884880128 7884912896 88796 _ _ (113941 / 5000) (445663 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884880128 7884912896 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884912896 :
    ThetaLowerSegment 7884912896 7884945664 (788338239798977 / 100000)
      (788341646634877 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884912896 33 20 (113941 / 5000)
        (2278823 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884912896 7884945664 88797 _ _ (113941 / 5000) (445663 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884912896 7884945664 12 1495 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884945664 :
    ThetaLowerSegment 7884945664 7884978432 (788341646634877 / 100000)
      (788345005617031 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884945664 33 20 (2278821 / 100000)
        (284853 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884945664 7884978432 88797 _ _ (2278821 / 100000) (1782653 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884945664 7884978432 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7884978432 :
    ThetaLowerSegment 7884978432 7885011200 (788345005617031 / 100000)
      (394174133304941 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7884978432 33 20 (2278821 / 100000)
        (284853 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7884978432 7885011200 88797 _ _ (2278821 / 100000) (1782653 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7884978432 7885011200 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885011200 :
    ThetaLowerSegment 7885011200 7885043968 (394174133304941 / 50000)
      (788351468353387 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885011200 33 20 (2278821 / 100000)
        (284853 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885011200 7885043968 88797 _ _ (2278821 / 100000) (1782653 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885011200 7885043968 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885043968 :
    ThetaLowerSegment 7885043968 7885076736 (788351468353387 / 100000)
      (157670942679183 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885043968 33 20 (1139411 / 50000)
        (91153 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885043968 7885076736 88797 _ _ (1139411 / 50000) (356531 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885043968 7885076736 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885076736 :
    ThetaLowerSegment 7885076736 7885109504 (157670942679183 / 20000) (31534314326811 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885076736 33 20 (1139411 / 50000)
        (91153 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885076736 7885109504 88797 _ _ (1139411 / 50000) (356531 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885076736 7885109504 12 1380 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885109504 :
    ThetaLowerSegment 7885109504 7885142272 (31534314326811 / 4000) (4927257051758 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885109504 33 20 (2278823 / 100000)
        (1139413 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885109504 7885142272 88798 _ _ (2278823 / 100000) (1782657 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885109504 7885142272 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885142272 :
    ThetaLowerSegment 7885142272 7885175040 (4927257051758 / 625) (78836443257463 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885142272 33 20 (2278823 / 100000)
        (1139413 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885142272 7885175040 88798 _ _ (2278823 / 100000) (1782657 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885142272 7885175040 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885175040 :
    ThetaLowerSegment 7885175040 7885207808 (78836443257463 / 10000) (394183852482947 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885175040 33 20 (284853 / 12500)
        (2278827 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885175040 7885207808 88798 _ _ (284853 / 12500) (891329 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885175040 7885207808 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885207808 :
    ThetaLowerSegment 7885207808 7885240576 (394183852482947 / 50000) (78837092722303 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885207808 33 20 (284853 / 12500)
        (2278827 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885207808 7885240576 88798 _ _ (284853 / 12500) (891329 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885207808 7885240576 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885240576 :
    ThetaLowerSegment 7885240576 7885273344 (78837092722303 / 10000) (394187082715967 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885240576 33 20 (284853 / 12500)
        (2278827 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885240576 7885273344 88798 _ _ (284853 / 12500) (891329 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885240576 7885273344 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885273344 :
    ThetaLowerSegment 7885273344 7885306112 (394187082715967 / 50000)
      (394188737142917 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885273344 33 20 (91153 / 4000) (569707 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885273344 7885306112 88799 _ _ (91153 / 4000) (89133 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885273344 7885306112 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885306112 :
    ThetaLowerSegment 7885306112 7885338880 (394188737142917 / 50000)
      (394190446261667 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885306112 33 20 (91153 / 4000) (569707 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885306112 7885338880 88799 _ _ (91153 / 4000) (89133 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885306112 7885338880 12 1500 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885338880 :
    ThetaLowerSegment 7885338880 7885371648 (394190446261667 / 50000)
      (197096054332617 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885338880 33 20 (1139413 / 50000)
        (2278829 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885338880 7885371648 88799 _ _ (1139413 / 50000) (891331 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885338880 7885371648 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885371648 :
    ThetaLowerSegment 7885371648 7885404416 (197096054332617 / 25000)
      (197096867873499 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885371648 33 20 (1139413 / 50000)
        (2278829 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885371648 7885404416 88799 _ _ (1139413 / 50000) (891331 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885371648 7885404416 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885404416 :
    ThetaLowerSegment 7885404416 7885437184 (197096867873499 / 25000)
      (394195377641131 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885404416 33 20 (1139413 / 50000)
        (2278829 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885404416 7885437184 88799 _ _ (1139413 / 50000) (891331 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885404416 7885437184 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885437184 :
    ThetaLowerSegment 7885437184 7885469952 (394195377641131 / 50000)
      (788394020841353 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885437184 33 20 (2278827 / 100000)
        (227883 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885437184 7885469952 88799 _ _ (2278827 / 100000) (1782663 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885437184 7885469952 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885469952 :
    ThetaLowerSegment 7885469952 7885502720 (788394020841353 / 100000)
      (197099335273073 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885469952 33 20 (2278827 / 100000)
        (227883 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885469952 7885502720 88800 _ _ (2278827 / 100000) (1782663 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885469952 7885502720 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885502720 :
    ThetaLowerSegment 7885502720 7885535488 (197099335273073 / 25000)
      (197100128305217 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885502720 33 20 (569707 / 25000)
        (2278831 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885502720 7885535488 88800 _ _ (569707 / 25000) (356533 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885502720 7885535488 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885535488 :
    ThetaLowerSegment 7885535488 7885568256 (197100128305217 / 25000) (24637620080893 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885535488 33 20 (569707 / 25000)
        (2278831 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885535488 7885568256 88800 _ _ (569707 / 25000) (356533 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885535488 7885568256 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885568256 :
    ThetaLowerSegment 7885568256 7885601024 (24637620080893 / 3125) (394203541541707 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885568256 33 20 (2278829 / 100000)
        (142427 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885568256 7885601024 88800 _ _ (2278829 / 100000) (1782667 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885568256 7885601024 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885601024 :
    ThetaLowerSegment 7885601024 7885633792 (394203541541707 / 50000)
      (788410344087713 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885601024 33 20 (2278829 / 100000)
        (142427 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885601024 7885633792 88800 _ _ (2278829 / 100000) (1782667 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885601024 7885633792 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885633792 :
    ThetaLowerSegment 7885633792 7885666560 (788410344087713 / 100000) (31536543930221 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885633792 33 20 (2278829 / 100000)
        (142427 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885633792 7885666560 88801 _ _ (2278829 / 100000) (1782667 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885633792 7885666560 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885666560 :
    ThetaLowerSegment 7885666560 7885699328 (31536543930221 / 4000) (157683381423337 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885666560 33 20 (227883 / 10000)
        (2278833 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885666560 7885699328 88801 _ _ (227883 / 10000) (445667 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885666560 7885699328 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885699328 :
    ThetaLowerSegment 7885699328 7885732096 (157683381423337 / 20000) (31536806451437 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885699328 33 20 (227883 / 10000)
        (2278833 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885699328 7885732096 88801 _ _ (227883 / 10000) (445667 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885699328 7885732096 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885732096 :
    ThetaLowerSegment 7885732096 7885764864 (31536806451437 / 4000) (788423479263861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885732096 33 20 (2278831 / 100000)
        (1139417 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885732096 7885764864 88801 _ _ (2278831 / 100000) (178267 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885732096 7885764864 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885764864 :
    ThetaLowerSegment 7885764864 7885797632 (788423479263861 / 100000) (24638338909289 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885764864 33 20 (2278831 / 100000)
        (1139417 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885764864 7885797632 88801 _ _ (2278831 / 100000) (178267 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885764864 7885797632 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885797632 :
    ThetaLowerSegment 7885797632 7885830400 (24638338909289 / 3125) (788430101546747 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885797632 33 20 (2278831 / 100000)
        (1139417 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885797632 7885830400 88802 _ _ (2278831 / 100000) (178267 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885797632 7885830400 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885830400 :
    ThetaLowerSegment 7885830400 7885863168 (788430101546747 / 100000)
      (788433319257531 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885830400 33 20 (142427 / 6250)
        (455767 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885830400 7885863168 88802 _ _ (142427 / 6250) (1782671 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885830400 7885863168 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885863168 :
    ThetaLowerSegment 7885863168 7885895936 (788433319257531 / 100000)
      (788436607612107 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885863168 33 20 (142427 / 6250)
        (455767 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885863168 7885895936 88802 _ _ (142427 / 6250) (1782671 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885863168 7885895936 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885895936 :
    ThetaLowerSegment 7885895936 7885928704 (788436607612107 / 100000)
      (157687966887927 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885895936 33 20 (2278833 / 100000)
        (569709 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885895936 7885928704 88802 _ _ (2278833 / 100000) (1782673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885895936 7885928704 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885928704 :
    ThetaLowerSegment 7885928704 7885961472 (157687966887927 / 20000) (98555404592163 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885928704 33 20 (2278833 / 100000)
        (569709 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885928704 7885961472 88802 _ _ (2278833 / 100000) (1782673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885928704 7885961472 12 1493 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885961472 :
    ThetaLowerSegment 7885961472 7885994240 (98555404592163 / 12500) (39422327280141 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885961472 33 20 (2278833 / 100000)
        (569709 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885961472 7885994240 88802 _ _ (2278833 / 100000) (1782673 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885961472 7885994240 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7885994240 :
    ThetaLowerSegment 7885994240 7886027008 (39422327280141 / 5000) (24639055815774 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7885994240 33 20 (1139417 / 50000)
        (2278837 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7885994240 7886027008 88803 _ _ (1139417 / 50000) (71307 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7885994240 7886027008 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886027008 :
    ThetaLowerSegment 7886027008 7886059776 (24639055815774 / 3125) (197113263488181 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886027008 33 20 (1139417 / 50000)
        (2278837 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886027008 7886059776 88803 _ _ (1139417 / 50000) (71307 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886027008 7886059776 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886059776 :
    ThetaLowerSegment 7886059776 7886092544 (197113263488181 / 25000)
      (197114056522761 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886059776 33 20 (455767 / 20000)
        (1139419 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886059776 7886092544 88803 _ _ (455767 / 20000) (445669 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886059776 7886092544 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886092544 :
    ThetaLowerSegment 7886092544 7886125312 (197114056522761 / 25000) (98557437312263 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886092544 33 20 (455767 / 20000)
        (1139419 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886092544 7886125312 88803 _ _ (455767 / 20000) (445669 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886092544 7886125312 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886125312 :
    ThetaLowerSegment 7886125312 7886158080 (98557437312263 / 12500) (19711565854411 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886125312 33 20 (569709 / 25000)
        (2278839 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886125312 7886158080 88803 _ _ (569709 / 25000) (891339 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886125312 7886158080 12 1376 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886158080 :
    ThetaLowerSegment 7886158080 7886190848 (19711565854411 / 2500) (49279122864667 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886158080 33 20 (569709 / 25000)
        (2278839 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886158080 7886190848 88804 _ _ (569709 / 25000) (891339 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886158080 7886190848 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886190848 :
    ThetaLowerSegment 7886190848 7886223616 (49279122864667 / 6250) (4927932625078 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886190848 33 20 (569709 / 25000)
        (2278839 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886190848 7886223616 88804 _ _ (569709 / 25000) (891339 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886190848 7886223616 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886223616 :
    ThetaLowerSegment 7886223616 7886256384 (4927932625078 / 625) (49279529067273 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886223616 33 20 (2278837 / 100000)
        (56971 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886223616 7886256384 88804 _ _ (2278837 / 100000) (44567 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886223616 7886256384 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886256384 :
    ThetaLowerSegment 7886256384 7886289152 (49279529067273 / 6250) (788475685073049 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886256384 33 20 (2278837 / 100000)
        (56971 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886256384 7886289152 88804 _ _ (2278837 / 100000) (44567 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886256384 7886289152 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886289152 :
    ThetaLowerSegment 7886289152 7886321920 (788475685073049 / 100000)
      (788479012176529 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886289152 33 20 (1139419 / 50000)
        (2278841 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886289152 7886321920 88804 _ _ (1139419 / 50000) (1782681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886289152 7886321920 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886321920 :
    ThetaLowerSegment 7886321920 7886354688 (788479012176529 / 100000)
      (788482398529797 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886321920 33 20 (1139419 / 50000)
        (2278841 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886321920 7886354688 88804 _ _ (1139419 / 50000) (1782681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886321920 7886354688 12 1486 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886354688 :
    ThetaLowerSegment 7886354688 7886387456 (788482398529797 / 100000)
      (788485686893031 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886354688 33 20 (1139419 / 50000)
        (2278841 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886354688 7886387456 88805 _ _ (1139419 / 50000) (1782681 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886354688 7886387456 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886387456 :
    ThetaLowerSegment 7886387456 7886420224 (788485686893031 / 100000)
      (197122207353003 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886387456 33 20 (2278839 / 100000)
        (1139421 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886387456 7886420224 88805 _ _ (2278839 / 100000) (1782683 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886387456 7886420224 12 1379 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886420224 :
    ThetaLowerSegment 7886420224 7886452992 (197122207353003 / 25000)
      (788492136007401 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886420224 33 20 (2278839 / 100000)
        (1139421 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886420224 7886452992 88805 _ _ (2278839 / 100000) (1782683 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886420224 7886452992 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886452992 :
    ThetaLowerSegment 7886452992 7886485760 (788492136007401 / 100000)
      (788495360566001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886452992 33 20 (56971 / 2500)
        (2278843 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886452992 7886485760 88805 _ _ (56971 / 2500) (356537 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886452992 7886485760 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886485760 :
    ThetaLowerSegment 7886485760 7886518528 (788495360566001 / 100000)
      (788498710460801 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886485760 33 20 (56971 / 2500)
        (2278843 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886485760 7886518528 88805 _ _ (56971 / 2500) (356537 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886485760 7886518528 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886518528 :
    ThetaLowerSegment 7886518528 7886551296 (788498710460801 / 100000)
      (78850196692459 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886518528 33 20 (2278841 / 100000)
        (569711 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886518528 7886551296 88806 _ _ (2278841 / 100000) (891343 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886518528 7886551296 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886551296 :
    ThetaLowerSegment 7886551296 7886584064 (78850196692459 / 10000)
      (788505177811559 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886551296 33 20 (2278841 / 100000)
        (569711 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886551296 7886584064 88806 _ _ (2278841 / 100000) (891343 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886551296 7886584064 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886584064 :
    ThetaLowerSegment 7886584064 7886616832 (788505177811559 / 100000)
      (394254187512741 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886584064 33 20 (2278841 / 100000)
        (569711 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886584064 7886616832 88806 _ _ (2278841 / 100000) (891343 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886584064 7886616832 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886616832 :
    ThetaLowerSegment 7886616832 7886649600 (394254187512741 / 50000)
      (394255748519511 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886616832 33 20 (1139421 / 50000)
        (455769 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886616832 7886649600 88806 _ _ (1139421 / 50000) (55709 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886616832 7886649600 12 1370 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886649600 :
    ThetaLowerSegment 7886649600 7886682368 (394255748519511 / 50000) (9856434418803 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886649600 33 20 (1139421 / 50000)
        (455769 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886649600 7886682368 88806 _ _ (1139421 / 50000) (55709 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886649600 7886682368 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886682368 :
    ThetaLowerSegment 7886682368 7886715136 (9856434418803 / 1250) (788518101124607 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886682368 33 20 (2278843 / 100000)
        (1139423 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886682368 7886715136 88806 _ _ (2278843 / 100000) (178269 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886682368 7886715136 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886715136 :
    ThetaLowerSegment 7886715136 7886747904 (788518101124607 / 100000)
      (788521478369933 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886715136 33 20 (2278843 / 100000)
        (1139423 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886715136 7886747904 88807 _ _ (2278843 / 100000) (178269 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886715136 7886747904 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886747904 :
    ThetaLowerSegment 7886747904 7886780672 (788521478369933 / 100000)
      (394262351466389 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886747904 33 20 (2278843 / 100000)
        (1139423 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886747904 7886780672 88807 _ _ (2278843 / 100000) (178269 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886747904 7886780672 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886780672 :
    ThetaLowerSegment 7886780672 7886813440 (394262351466389 / 50000)
      (394264000210023 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886780672 33 20 (569711 / 25000)
        (2278847 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886780672 7886813440 88807 _ _ (569711 / 25000) (1782691 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886780672 7886813440 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886813440 :
    ThetaLowerSegment 7886813440 7886846208 (394264000210023 / 50000)
      (394265606795043 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886813440 33 20 (569711 / 25000)
        (2278847 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886813440 7886846208 88807 _ _ (569711 / 25000) (1782691 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886813440 7886846208 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886846208 :
    ThetaLowerSegment 7886846208 7886878976 (394265606795043 / 50000)
      (788534520194181 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886846208 33 20 (455769 / 20000) (71214 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886846208 7886878976 88807 _ _ (455769 / 20000) (1782693 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886846208 7886878976 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886878976 :
    ThetaLowerSegment 7886878976 7886911744 (788534520194181 / 100000)
      (788537902000161 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886878976 33 20 (455769 / 20000) (71214 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886878976 7886911744 88808 _ _ (455769 / 20000) (1782693 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886878976 7886911744 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886911744 :
    ThetaLowerSegment 7886911744 7886944512 (788537902000161 / 100000)
      (788541153913403 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886911744 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886911744 7886944512 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886911744 7886944512 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886944512 :
    ThetaLowerSegment 7886944512 7886977280 (788541153913403 / 100000)
      (788544465076641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886944512 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886944512 7886977280 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886944512 7886977280 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886977280 :
    ThetaLowerSegment 7886977280 7886979328 (788544465076641 / 100000)
      (788544670172781 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886977280 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886977280 7886979328 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886977280 7886979328 8 90 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886979328 :
    ThetaLowerSegment 7886979328 7886979840 (788544670172781 / 100000)
      (788544720307393 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886979328 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886979328 7886979840 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886979328 7886979840 6 22 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886979840 :
    ThetaLowerSegment 7886979840 7886980096 (788544720307393 / 100000)
      (788544749932391 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886979840 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886979840 7886980096 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886979840 7886980096 5 13 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886980096 :
    ThetaLowerSegment 7886980096 7886980160 (788544749932391 / 100000)
      (788544761326621 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886980096 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886980096 7886980160 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886980096 7886980160 3 5 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886980160 :
    ThetaLowerSegment 7886980160 7886980176 (788544761326621 / 100000)
      (788544761326621 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886980160 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886980160 7886980176 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886980160 7886980176 1 0 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7886980176 :
    ThetaLowerSegment 7886980176 7886980184 (788544761326621 / 100000)
      (788544761326621 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7886980176 33 20 (1139423 / 50000)
        (2278849 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7886980176 7886980184 88808 _ _ (1139423 / 50000) (356539 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7886980176 7886980184 0 0 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

/-- This window supplies its exit bound and covers its real interval from a scalar entrance. -/
public theorem gap_window_7886980184 :
    ThetaLowerSegment 7881341184 7886980184 (787980696495567 / 100000)
      (788544761326621 / 100000) := by
  exact
    ((((((((cell7881341184.join cell7881373952).join (cell7881406720.join cell7881439488)).join
                          ((cell7881472256.join cell7881505024).join
                            (cell7881537792.join cell7881570560))).join
                      (((cell7881603328.join cell7881636096).join
                            (cell7881668864.join cell7881701632)).join
                        ((cell7881734400.join cell7881767168).join
                          (cell7881799936.join cell7881832704)))).join
                  ((((cell7881865472.join cell7881898240).join
                            (cell7881931008.join cell7881963776)).join
                        ((cell7881996544.join cell7882029312).join
                          (cell7882062080.join cell7882094848))).join
                    (((cell7882127616.join cell7882160384).join
                          (cell7882193152.join cell7882225920)).join
                      ((cell7882258688.join cell7882291456).join
                        (cell7882324224.join cell7882356992))))).join
              (((((cell7882389760.join cell7882422528).join
                            (cell7882455296.join cell7882488064)).join
                        ((cell7882520832.join cell7882553600).join
                          (cell7882586368.join cell7882619136))).join
                    (((cell7882651904.join cell7882684672).join
                          (cell7882717440.join cell7882750208)).join
                      ((cell7882782976.join cell7882815744).join
                        (cell7882848512.join cell7882881280)))).join
                ((((cell7882914048.join cell7882946816).join
                          (cell7882979584.join cell7883012352)).join
                      ((cell7883045120.join cell7883077888).join
                        (cell7883110656.join cell7883143424))).join
                  (((cell7883176192.join cell7883208960).join
                        (cell7883241728.join cell7883274496)).join
                    ((cell7883307264.join cell7883340032).join
                      (cell7883372800.join cell7883405568)))))).join
          ((((((cell7883438336.join cell7883471104).join (cell7883503872.join cell7883536640)).join
                        ((cell7883569408.join cell7883602176).join
                          (cell7883634944.join cell7883667712))).join
                    (((cell7883700480.join cell7883733248).join
                          (cell7883766016.join cell7883798784)).join
                      ((cell7883831552.join cell7883864320).join
                        (cell7883897088.join cell7883929856)))).join
                ((((cell7883962624.join cell7883995392).join
                          (cell7884028160.join cell7884060928)).join
                      ((cell7884093696.join cell7884126464).join
                        (cell7884159232.join cell7884192000))).join
                  (((cell7884224768.join cell7884257536).join
                        (cell7884290304.join cell7884323072)).join
                    ((cell7884355840.join cell7884388608).join
                      (cell7884421376.join cell7884454144))))).join
            (((((cell7884486912.join cell7884519680).join (cell7884552448.join cell7884585216)).join
                      ((cell7884617984.join cell7884650752).join
                        (cell7884683520.join cell7884716288))).join
                  (((cell7884749056.join cell7884781824).join
                        (cell7884814592.join cell7884847360)).join
                    ((cell7884880128.join cell7884912896).join
                      (cell7884945664.join cell7884978432)))).join
              ((((cell7885011200.join cell7885043968).join
                        (cell7885076736.join cell7885109504)).join
                    ((cell7885142272.join cell7885175040).join
                      (cell7885207808.join cell7885240576))).join
                (((cell7885273344.join cell7885306112).join
                      (cell7885338880.join cell7885371648)).join
                  ((cell7885404416.join cell7885437184).join
                    (cell7885469952.join cell7885502720))))))).join
      ((((((cell7885535488.join cell7885568256).join (cell7885601024.join cell7885633792)).join
                    ((cell7885666560.join cell7885699328).join
                      (cell7885732096.join cell7885764864))).join
                (((cell7885797632.join cell7885830400).join
                      (cell7885863168.join cell7885895936)).join
                  ((cell7885928704.join cell7885961472).join
                    (cell7885994240.join cell7886027008)))).join
            ((((cell7886059776.join cell7886092544).join (cell7886125312.join cell7886158080)).join
                  ((cell7886190848.join cell7886223616).join
                    (cell7886256384.join cell7886289152))).join
              (((cell7886321920.join cell7886354688).join (cell7886387456.join cell7886420224)).join
                ((cell7886452992.join cell7886485760).join
                  (cell7886518528.join cell7886551296))))).join
        (((((cell7886584064.join cell7886616832).join (cell7886649600.join cell7886682368)).join
                  ((cell7886715136.join cell7886747904).join
                    (cell7886780672.join cell7886813440))).join
              (((cell7886846208.join cell7886878976).join (cell7886911744.join cell7886944512)).join
                ((cell7886977280.join cell7886979328).join
                  (cell7886979840.join cell7886980096)))).join
          (cell7886980160.join cell7886980176))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
