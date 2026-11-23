/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartCell
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Finite gap estimate up to 7881341184 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell7849341184 :
    ThetaLowerSegment 7849341184 7849373952 (784782495993077 / 100000)
      (784785763172789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849341184 33 20 (71199 / 3125)
        (2278371 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849341184 7849373952 88596 _ _ (71199 / 3125) (356381 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849341184 7849373952 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849373952 :
    ThetaLowerSegment 7849373952 7849406720 (784785763172789 / 100000)
      (784789100981909 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849373952 33 20 (71199 / 3125)
        (2278371 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849373952 7849406720 88596 _ _ (71199 / 3125) (356381 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849373952 7849406720 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849406720 :
    ThetaLowerSegment 7849406720 7849439488 (784789100981909 / 100000)
      (784792422843911 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849406720 33 20 (2278369 / 100000)
        (569593 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849406720 7849439488 88596 _ _ (2278369 / 100000) (1781907 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849406720 7849439488 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849439488 :
    ThetaLowerSegment 7849439488 7849472256 (784792422843911 / 100000)
      (156959134359621 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849439488 33 20 (2278369 / 100000)
        (569593 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849439488 7849472256 88597 _ _ (2278369 / 100000) (1781907 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849439488 7849472256 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849472256 :
    ThetaLowerSegment 7849472256 7849505024 (156959134359621 / 20000)
      (156959797365291 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849472256 33 20 (227837 / 10000)
        (2278373 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849472256 7849505024 88597 _ _ (227837 / 10000) (1781909 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849472256 7849505024 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849505024 :
    ThetaLowerSegment 7849505024 7849537792 (156959797365291 / 20000)
      (156960428473781 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849505024 33 20 (227837 / 10000)
        (2278373 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849505024 7849537792 88597 _ _ (227837 / 10000) (1781909 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849505024 7849537792 12 1385 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849537792 :
    ThetaLowerSegment 7849537792 7849570560 (156960428473781 / 20000)
      (784805477904049 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849537792 33 20 (2278371 / 100000)
        (1139187 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849537792 7849570560 88597 _ _ (2278371 / 100000) (178191 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849537792 7849570560 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849570560 :
    ThetaLowerSegment 7849570560 7849603328 (784805477904049 / 100000)
      (784808690407159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849570560 33 20 (2278371 / 100000)
        (1139187 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849570560 7849603328 88597 _ _ (2278371 / 100000) (178191 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849570560 7849603328 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849603328 :
    ThetaLowerSegment 7849603328 7849636096 (784808690407159 / 100000)
      (392405995883369 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849603328 33 20 (2278371 / 100000)
        (1139187 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849603328 7849636096 88597 _ _ (2278371 / 100000) (178191 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849603328 7849636096 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849636096 :
    ThetaLowerSegment 7849636096 7849668864 (392405995883369 / 50000) (78481524072521 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849636096 33 20 (569593 / 25000) (18227 / 800) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849636096 7849668864 88598 _ _ (569593 / 25000) (222739 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849636096 7849668864 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849668864 :
    ThetaLowerSegment 7849668864 7849701632 (78481524072521 / 10000) (392409296105211 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849668864 33 20 (569593 / 25000) (18227 / 800) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849668864 7849701632 88598 _ _ (569593 / 25000) (222739 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849668864 7849701632 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849701632 :
    ThetaLowerSegment 7849701632 7849734400 (392409296105211 / 50000)
      (196205480797937 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849701632 33 20 (2278373 / 100000)
        (284797 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849701632 7849734400 88598 _ _ (2278373 / 100000) (890957 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849701632 7849734400 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849734400 :
    ThetaLowerSegment 7849734400 7849767168 (196205480797937 / 25000) (78482509924371 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849734400 33 20 (2278373 / 100000)
        (284797 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849734400 7849767168 88598 _ _ (2278373 / 100000) (890957 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849734400 7849767168 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849767168 :
    ThetaLowerSegment 7849767168 7849799936 (78482509924371 / 10000) (196207080215783 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849767168 33 20 (2278373 / 100000)
        (284797 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849767168 7849799936 88598 _ _ (2278373 / 100000) (890957 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849767168 7849799936 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849799936 :
    ThetaLowerSegment 7849799936 7849832704 (196207080215783 / 25000) (15696632809081 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849799936 33 20 (1139187 / 50000)
        (2278377 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849799936 7849832704 88599 _ _ (1139187 / 50000) (356383 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849799936 7849832704 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849832704 :
    ThetaLowerSegment 7849832704 7849865472 (15696632809081 / 2000) (24526090507828 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849832704 33 20 (1139187 / 50000)
        (2278377 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849832704 7849865472 88599 _ _ (1139187 / 50000) (356383 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849832704 7849865472 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849865472 :
    ThetaLowerSegment 7849865472 7849898240 (24526090507828 / 3125) (784838170275371 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849865472 33 20 (18227 / 800) (1139189 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849865472 7849898240 88599 _ _ (18227 / 800) (1781917 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849865472 7849898240 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849898240 :
    ThetaLowerSegment 7849898240 7849931008 (784838170275371 / 100000)
      (392420708479873 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849898240 33 20 (18227 / 800) (1139189 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849898240 7849931008 88599 _ _ (18227 / 800) (1781917 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849898240 7849931008 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849931008 :
    ThetaLowerSegment 7849931008 7849963776 (392420708479873 / 50000)
      (392422365998413 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849931008 33 20 (284797 / 12500)
        (2278379 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849931008 7849963776 88599 _ _ (284797 / 12500) (1781919 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849931008 7849963776 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849963776 :
    ThetaLowerSegment 7849963776 7849996544 (392422365998413 / 50000)
      (392424013264261 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849963776 33 20 (284797 / 12500)
        (2278379 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849963776 7849996544 88600 _ _ (284797 / 12500) (1781919 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849963776 7849996544 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7849996544 :
    ThetaLowerSegment 7849996544 7850029312 (392424013264261 / 50000)
      (392425603570709 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7849996544 33 20 (284797 / 12500)
        (2278379 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7849996544 7850029312 88600 _ _ (284797 / 12500) (1781919 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7849996544 7850029312 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850029312 :
    ThetaLowerSegment 7850029312 7850062080 (392425603570709 / 50000)
      (392427225775133 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850029312 33 20 (2278377 / 100000)
        (113919 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850029312 7850062080 88600 _ _ (2278377 / 100000) (11137 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850029312 7850062080 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850062080 :
    ThetaLowerSegment 7850062080 7850094848 (392427225775133 / 50000)
      (392428829752541 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850062080 33 20 (2278377 / 100000)
        (113919 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850062080 7850094848 88600 _ _ (2278377 / 100000) (11137 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850062080 7850094848 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850094848 :
    ThetaLowerSegment 7850094848 7850127616 (392428829752541 / 50000)
      (392430515752261 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850094848 33 20 (1139189 / 50000)
        (2278381 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850094848 7850127616 88600 _ _ (1139189 / 50000) (890961 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850094848 7850127616 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850127616 :
    ThetaLowerSegment 7850127616 7850160384 (392430515752261 / 50000)
      (392432137957397 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850127616 33 20 (1139189 / 50000)
        (2278381 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850127616 7850160384 88600 _ _ (1139189 / 50000) (890961 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850127616 7850160384 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850160384 :
    ThetaLowerSegment 7850160384 7850193152 (392432137957397 / 50000)
      (392433787503069 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850160384 33 20 (1139189 / 50000)
        (2278381 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850160384 7850193152 88601 _ _ (1139189 / 50000) (890961 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850160384 7850193152 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850193152 :
    ThetaLowerSegment 7850193152 7850225920 (392433787503069 / 50000)
      (156974158871133 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850193152 33 20 (2278379 / 100000)
        (1139191 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850193152 7850225920 88601 _ _ (2278379 / 100000) (445481 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850193152 7850225920 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850225920 :
    ThetaLowerSegment 7850225920 7850258688 (156974158871133 / 20000)
      (392437000017459 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850225920 33 20 (2278379 / 100000)
        (1139191 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850225920 7850258688 88601 _ _ (2278379 / 100000) (445481 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850225920 7850258688 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850258688 :
    ThetaLowerSegment 7850258688 7850291456 (392437000017459 / 50000)
      (392438654121339 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850258688 33 20 (113919 / 5000)
        (2278383 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850258688 7850291456 88601 _ _ (113919 / 5000) (71277 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850258688 7850291456 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850291456 :
    ThetaLowerSegment 7850291456 7850324224 (392438654121339 / 50000)
      (392440292276559 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850291456 33 20 (113919 / 5000)
        (2278383 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850291456 7850324224 88601 _ _ (113919 / 5000) (71277 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850291456 7850324224 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850324224 :
    ThetaLowerSegment 7850324224 7850356992 (392440292276559 / 50000)
      (196220951545963 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850324224 33 20 (2278381 / 100000)
        (142399 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850324224 7850356992 88602 _ _ (2278381 / 100000) (1781927 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850324224 7850356992 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850356992 :
    ThetaLowerSegment 7850356992 7850389760 (196220951545963 / 25000)
      (392443577701961 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850356992 33 20 (2278381 / 100000)
        (142399 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850356992 7850389760 88602 _ _ (2278381 / 100000) (1781927 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850356992 7850389760 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850389760 :
    ThetaLowerSegment 7850389760 7850422528 (392443577701961 / 50000)
      (784890370199513 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850389760 33 20 (2278381 / 100000)
        (142399 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850389760 7850422528 88602 _ _ (2278381 / 100000) (1781927 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850389760 7850422528 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850422528 :
    ThetaLowerSegment 7850422528 7850455296 (784890370199513 / 100000)
      (784893589553279 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850422528 33 20 (1139191 / 50000)
        (455677 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850422528 7850455296 88602 _ _ (1139191 / 50000) (1781929 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850422528 7850455296 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850455296 :
    ThetaLowerSegment 7850455296 7850488064 (784893589553279 / 100000)
      (156979370894937 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850455296 33 20 (1139191 / 50000)
        (455677 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850455296 7850488064 88602 _ _ (1139191 / 50000) (1781929 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850455296 7850488064 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850488064 :
    ThetaLowerSegment 7850488064 7850520832 (156979370894937 / 20000)
      (156980027069241 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850488064 33 20 (2278383 / 100000)
        (1139193 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850488064 7850520832 88602 _ _ (2278383 / 100000) (178193 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850488064 7850520832 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850520832 :
    ThetaLowerSegment 7850520832 7850553600 (156980027069241 / 20000)
      (784903429888023 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850520832 33 20 (2278383 / 100000)
        (1139193 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850520832 7850553600 88603 _ _ (2278383 / 100000) (178193 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850520832 7850553600 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850553600 :
    ThetaLowerSegment 7850553600 7850586368 (784903429888023 / 100000)
      (392453379302793 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850553600 33 20 (2278383 / 100000)
        (1139193 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850553600 7850586368 88603 _ _ (2278383 / 100000) (178193 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850553600 7850586368 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850586368 :
    ThetaLowerSegment 7850586368 7850619136 (392453379302793 / 50000)
      (392455034548769 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850586368 33 20 (142399 / 6250)
        (2278387 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850586368 7850619136 88603 _ _ (142399 / 6250) (445483 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850586368 7850619136 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850619136 :
    ThetaLowerSegment 7850619136 7850651904 (392455034548769 / 50000)
      (392456696629897 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850619136 33 20 (142399 / 6250)
        (2278387 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850619136 7850651904 88603 _ _ (142399 / 6250) (445483 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850619136 7850651904 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850651904 :
    ThetaLowerSegment 7850651904 7850684672 (392456696629897 / 50000)
      (784916639958419 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850651904 33 20 (455677 / 20000)
        (569597 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850651904 7850684672 88603 _ _ (455677 / 20000) (1781933 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850651904 7850684672 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850684672 :
    ThetaLowerSegment 7850684672 7850717440 (784916639958419 / 100000)
      (784919970957289 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850684672 33 20 (455677 / 20000)
        (569597 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850684672 7850717440 88604 _ _ (455677 / 20000) (1781933 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850684672 7850717440 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850717440 :
    ThetaLowerSegment 7850717440 7850750208 (784919970957289 / 100000)
      (784923258668287 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850717440 33 20 (1139193 / 50000)
        (2278389 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850717440 7850750208 88604 _ _ (1139193 / 50000) (356387 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850717440 7850750208 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850750208 :
    ThetaLowerSegment 7850750208 7850782976 (784923258668287 / 100000)
      (156985302440699 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850750208 33 20 (1139193 / 50000)
        (2278389 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850750208 7850782976 88604 _ _ (1139193 / 50000) (356387 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850750208 7850782976 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850782976 :
    ThetaLowerSegment 7850782976 7850815744 (156985302440699 / 20000)
      (784929761181931 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850782976 33 20 (1139193 / 50000)
        (2278389 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850782976 7850815744 88604 _ _ (1139193 / 50000) (356387 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850782976 7850815744 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850815744 :
    ThetaLowerSegment 7850815744 7850848512 (784929761181931 / 100000)
      (784933028388889 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850815744 33 20 (2278387 / 100000)
        (227839 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850815744 7850848512 88604 _ _ (2278387 / 100000) (1781937 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850815744 7850848512 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850848512 :
    ThetaLowerSegment 7850848512 7850881280 (784933028388889 / 100000)
      (784936313822943 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850848512 33 20 (2278387 / 100000)
        (227839 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850848512 7850881280 88605 _ _ (2278387 / 100000) (1781937 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850848512 7850881280 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850881280 :
    ThetaLowerSegment 7850881280 7850914048 (784936313822943 / 100000)
      (784939519514859 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850881280 33 20 (569597 / 25000)
        (2278391 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850881280 7850914048 88605 _ _ (569597 / 25000) (890969 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850881280 7850914048 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850914048 :
    ThetaLowerSegment 7850914048 7850946816 (784939519514859 / 100000)
      (784942820899071 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850914048 33 20 (569597 / 25000)
        (2278391 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850914048 7850946816 88605 _ _ (569597 / 25000) (890969 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850914048 7850946816 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850946816 :
    ThetaLowerSegment 7850946816 7850979584 (784942820899071 / 100000)
      (784946113169731 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850946816 33 20 (569597 / 25000)
        (2278391 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850946816 7850979584 88605 _ _ (569597 / 25000) (890969 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850946816 7850979584 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7850979584 :
    ThetaLowerSegment 7850979584 7851012352 (784946113169731 / 100000) (9811866314909 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7850979584 33 20 (2278389 / 100000)
        (284799 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7850979584 7851012352 88605 _ _ (2278389 / 100000) (89097 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7850979584 7851012352 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851012352 :
    ThetaLowerSegment 7851012352 7851045120 (9811866314909 / 1250) (78495251772121 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851012352 33 20 (2278389 / 100000)
        (284799 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851012352 7851045120 88605 _ _ (2278389 / 100000) (89097 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851012352 7851045120 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851045120 :
    ThetaLowerSegment 7851045120 7851077888 (78495251772121 / 10000) (78495579860281 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851045120 33 20 (227839 / 10000)
        (2278393 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851045120 7851077888 88606 _ _ (227839 / 10000) (890971 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851045120 7851077888 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851077888 :
    ThetaLowerSegment 7851077888 7851110656 (78495579860281 / 10000) (4905994147098 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851077888 33 20 (227839 / 10000)
        (2278393 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851077888 7851110656 88606 _ _ (227839 / 10000) (890971 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851077888 7851110656 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851110656 :
    ThetaLowerSegment 7851110656 7851143424 (4905994147098 / 625) (784962337583547 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851110656 33 20 (2278391 / 100000)
        (1139197 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851110656 7851143424 88606 _ _ (2278391 / 100000) (1781943 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851110656 7851143424 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851143424 :
    ThetaLowerSegment 7851143424 7851176192 (784962337583547 / 100000)
      (784965572898767 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851143424 33 20 (2278391 / 100000)
        (1139197 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851143424 7851176192 88606 _ _ (2278391 / 100000) (1781943 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851143424 7851176192 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851176192 :
    ThetaLowerSegment 7851176192 7851208960 (784965572898767 / 100000)
      (156993783515351 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851176192 33 20 (2278391 / 100000)
        (1139197 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851176192 7851208960 88606 _ _ (2278391 / 100000) (1781943 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851176192 7851208960 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851208960 :
    ThetaLowerSegment 7851208960 7851241728 (156993783515351 / 20000)
      (784972150615003 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851208960 33 20 (284799 / 12500)
        (455679 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851208960 7851241728 88607 _ _ (284799 / 12500) (356389 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851208960 7851241728 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851241728 :
    ThetaLowerSegment 7851241728 7851274496 (784972150615003 / 100000) (6279803470223 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851241728 33 20 (284799 / 12500)
        (455679 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851241728 7851274496 88607 _ _ (284799 / 12500) (356389 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851241728 7851274496 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851274496 :
    ThetaLowerSegment 7851274496 7851307264 (6279803470223 / 800) (392489365306273 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851274496 33 20 (2278393 / 100000)
        (569599 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851274496 7851307264 88607 _ _ (2278393 / 100000) (1781947 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851274496 7851307264 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851307264 :
    ThetaLowerSegment 7851307264 7851340032 (392489365306273 / 50000)
      (784981977322571 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851307264 33 20 (2278393 / 100000)
        (569599 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851307264 7851340032 88607 _ _ (2278393 / 100000) (1781947 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851307264 7851340032 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851340032 :
    ThetaLowerSegment 7851340032 7851372800 (784981977322571 / 100000)
      (784985217198839 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851340032 33 20 (1139197 / 50000)
        (2278397 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851340032 7851372800 88607 _ _ (1139197 / 50000) (445487 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851340032 7851372800 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851372800 :
    ThetaLowerSegment 7851372800 7851405568 (784985217198839 / 100000)
      (784988573273201 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851372800 33 20 (1139197 / 50000)
        (2278397 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851372800 7851405568 88607 _ _ (1139197 / 50000) (445487 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851372800 7851405568 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851405568 :
    ThetaLowerSegment 7851405568 7851438336 (784988573273201 / 100000)
      (784991813149469 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851405568 33 20 (1139197 / 50000)
        (2278397 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851405568 7851438336 88608 _ _ (1139197 / 50000) (445487 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851405568 7851438336 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851438336 :
    ThetaLowerSegment 7851438336 7851471104 (784991813149469 / 100000)
      (196248776357561 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851438336 33 20 (455679 / 20000)
        (1139199 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851438336 7851471104 88608 _ _ (455679 / 20000) (35639 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851438336 7851471104 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851471104 :
    ThetaLowerSegment 7851471104 7851503872 (196248776357561 / 25000)
      (196249578352601 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851471104 33 20 (455679 / 20000)
        (1139199 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851471104 7851503872 88608 _ _ (455679 / 20000) (35639 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851471104 7851503872 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851503872 :
    ThetaLowerSegment 7851503872 7851536640 (196249578352601 / 25000)
      (196250392879171 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851503872 33 20 (569599 / 25000)
        (2278399 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851503872 7851536640 88608 _ _ (569599 / 25000) (55686 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851503872 7851536640 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851536640 :
    ThetaLowerSegment 7851536640 7851569408 (196250392879171 / 25000)
      (196251208544939 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851536640 33 20 (569599 / 25000)
        (2278399 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851536640 7851569408 88608 _ _ (569599 / 25000) (55686 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851536640 7851569408 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851569408 :
    ThetaLowerSegment 7851569408 7851602176 (196251208544939 / 25000) (39250409626773 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851569408 33 20 (569599 / 25000)
        (2278399 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851569408 7851602176 88609 _ _ (569599 / 25000) (55686 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851569408 7851602176 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851602176 :
    ThetaLowerSegment 7851602176 7851634944 (39250409626773 / 5000) (49063216519597 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851602176 33 20 (2278397 / 100000) (2848 / 125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851602176 7851634944 88609 _ _ (2278397 / 100000) (1781953 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851602176 7851634944 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851634944 :
    ThetaLowerSegment 7851634944 7851667712 (49063216519597 / 6250) (15700294630697 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851634944 33 20 (2278397 / 100000) (2848 / 125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851634944 7851667712 88609 _ _ (2278397 / 100000) (1781953 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851634944 7851667712 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851667712 :
    ThetaLowerSegment 7851667712 7851700480 (15700294630697 / 2000) (392508999378791 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851667712 33 20 (1139199 / 50000)
        (2278401 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851667712 7851700480 88609 _ _ (1139199 / 50000) (356391 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851667712 7851700480 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851700480 :
    ThetaLowerSegment 7851700480 7851733248 (392508999378791 / 50000)
      (392510605649381 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851700480 33 20 (1139199 / 50000)
        (2278401 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851700480 7851733248 88609 _ _ (1139199 / 50000) (356391 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851700480 7851733248 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851733248 :
    ThetaLowerSegment 7851733248 7851766016 (392510605649381 / 50000)
      (392512287107843 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851733248 33 20 (2278399 / 100000)
        (1139201 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851733248 7851766016 88610 _ _ (2278399 / 100000) (1781957 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851733248 7851766016 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851766016 :
    ThetaLowerSegment 7851766016 7851798784 (392512287107843 / 50000) (24532118620996 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851766016 33 20 (2278399 / 100000)
        (1139201 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851766016 7851798784 88610 _ _ (2278399 / 100000) (1781957 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851766016 7851798784 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851798784 :
    ThetaLowerSegment 7851798784 7851831552 (24532118620996 / 3125) (785031074488033 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851798784 33 20 (2278399 / 100000)
        (1139201 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851798784 7851831552 88610 _ _ (2278399 / 100000) (1781957 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851798784 7851831552 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851831552 :
    ThetaLowerSegment 7851831552 7851864320 (785031074488033 / 100000)
      (785034282475233 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851831552 33 20 (2848 / 125) (2278403 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851831552 7851864320 88610 _ _ (2848 / 125) (890979 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851831552 7851864320 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851864320 :
    ThetaLowerSegment 7851864320 7851897088 (785034282475233 / 100000)
      (785037542865633 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851864320 33 20 (2848 / 125) (2278403 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851864320 7851897088 88610 _ _ (2848 / 125) (890979 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851864320 7851897088 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851897088 :
    ThetaLowerSegment 7851897088 7851929856 (785037542865633 / 100000)
      (157008183891183 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851897088 33 20 (2278401 / 100000)
        (569601 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851897088 7851929856 88610 _ _ (2278401 / 100000) (44549 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851897088 7851929856 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851929856 :
    ThetaLowerSegment 7851929856 7851962624 (157008183891183 / 20000) (98130524189769 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851929856 33 20 (2278401 / 100000)
        (569601 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851929856 7851962624 88611 _ _ (2278401 / 100000) (44549 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851929856 7851962624 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851962624 :
    ThetaLowerSegment 7851962624 7851995392 (98130524189769 / 12500) (24532733005887 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851962624 33 20 (2278401 / 100000)
        (569601 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851962624 7851995392 88611 _ _ (2278401 / 100000) (44549 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851962624 7851995392 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7851995392 :
    ThetaLowerSegment 7851995392 7852028160 (24532733005887 / 3125) (196262696803027 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7851995392 33 20 (1139201 / 50000)
        (455681 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7851995392 7852028160 88611 _ _ (1139201 / 50000) (890981 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7851995392 7852028160 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852028160 :
    ThetaLowerSegment 7852028160 7852060928 (196262696803027 / 25000)
      (392527076205931 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852028160 33 20 (1139201 / 50000)
        (455681 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852028160 7852060928 88611 _ _ (1139201 / 50000) (890981 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852028160 7852060928 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852060928 :
    ThetaLowerSegment 7852060928 7852093696 (392527076205931 / 50000)
      (785057408249749 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852060928 33 20 (2278403 / 100000)
        (1139203 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852060928 7852093696 88611 _ _ (2278403 / 100000) (1781963 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852060928 7852093696 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852093696 :
    ThetaLowerSegment 7852093696 7852126464 (785057408249749 / 100000)
      (98132586428559 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852093696 33 20 (2278403 / 100000)
        (1139203 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852093696 7852126464 88612 _ _ (2278403 / 100000) (1781963 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852093696 7852126464 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852126464 :
    ThetaLowerSegment 7852126464 7852159232 (98132586428559 / 12500) (196266000487371 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852126464 33 20 (569601 / 25000)
        (2278407 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852126464 7852159232 88612 _ _ (569601 / 25000) (356393 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852126464 7852159232 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852159232 :
    ThetaLowerSegment 7852159232 7852192000 (196266000487371 / 25000) (24533349527496 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852159232 33 20 (569601 / 25000)
        (2278407 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852159232 7852192000 88612 _ _ (569601 / 25000) (356393 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852159232 7852192000 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852192000 :
    ThetaLowerSegment 7852192000 7852224768 (24533349527496 / 3125) (98133819045123 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852192000 33 20 (569601 / 25000)
        (2278407 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852192000 7852224768 88612 _ _ (569601 / 25000) (356393 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852192000 7852224768 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852224768 :
    ThetaLowerSegment 7852224768 7852257536 (98133819045123 / 12500)
      (785073703395099 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852224768 33 20 (455681 / 20000)
        (284801 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852224768 7852257536 88612 _ _ (455681 / 20000) (890983 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852224768 7852257536 12 1383 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852257536 :
    ThetaLowerSegment 7852257536 7852290304 (785073703395099 / 100000)
      (392538495566757 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852257536 33 20 (455681 / 20000)
        (284801 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852257536 7852290304 88612 _ _ (455681 / 20000) (890983 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852257536 7852290304 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852290304 :
    ThetaLowerSegment 7852290304 7852323072 (392538495566757 / 50000)
      (392540122348641 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852290304 33 20 (1139203 / 50000)
        (2278409 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852290304 7852323072 88613 _ _ (1139203 / 50000) (111373 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852290304 7852323072 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852323072 :
    ThetaLowerSegment 7852323072 7852355840 (392540122348641 / 50000) (39254176621857 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852323072 33 20 (1139203 / 50000)
        (2278409 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852323072 7852355840 88613 _ _ (1139203 / 50000) (111373 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852323072 7852355840 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852355840 :
    ThetaLowerSegment 7852355840 7852388608 (39254176621857 / 5000) (392543387304439 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852355840 33 20 (1139203 / 50000)
        (2278409 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852355840 7852388608 88613 _ _ (1139203 / 50000) (111373 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852355840 7852388608 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852388608 :
    ThetaLowerSegment 7852388608 7852421376 (392543387304439 / 50000)
      (157017988774603 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852388608 33 20 (2278407 / 100000)
        (227841 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852388608 7852421376 88613 _ _ (2278407 / 100000) (178197 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852388608 7852421376 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852421376 :
    ThetaLowerSegment 7852421376 7852454144 (157017988774603 / 20000)
      (157018649512633 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852421376 33 20 (2278407 / 100000)
        (227841 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852421376 7852454144 88613 _ _ (2278407 / 100000) (178197 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852421376 7852454144 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852454144 :
    ThetaLowerSegment 7852454144 7852486912 (157018649512633 / 20000)
      (785096512521829 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852454144 33 20 (284801 / 12500)
        (2278411 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852454144 7852486912 88614 _ _ (284801 / 12500) (1781971 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852454144 7852486912 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852486912 :
    ThetaLowerSegment 7852486912 7852519680 (785096512521829 / 100000)
      (785099793429349 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852486912 33 20 (284801 / 12500)
        (2278411 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852486912 7852519680 88614 _ _ (284801 / 12500) (1781971 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852486912 7852519680 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852519680 :
    ThetaLowerSegment 7852519680 7852552448 (785099793429349 / 100000)
      (196275763458157 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852519680 33 20 (2278409 / 100000)
        (569603 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852519680 7852552448 88614 _ _ (2278409 / 100000) (1781973 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852519680 7852552448 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852552448 :
    ThetaLowerSegment 7852552448 7852585216 (196275763458157 / 25000)
      (196276551787671 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852552448 33 20 (2278409 / 100000)
        (569603 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852552448 7852585216 88614 _ _ (2278409 / 100000) (1781973 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852552448 7852585216 12 1384 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852585216 :
    ThetaLowerSegment 7852585216 7852617984 (196276551787671 / 25000)
      (785109449326691 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852585216 33 20 (2278409 / 100000)
        (569603 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852585216 7852617984 88614 _ _ (2278409 / 100000) (1781973 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852585216 7852617984 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852617984 :
    ThetaLowerSegment 7852617984 7852650752 (785109449326691 / 100000)
      (785112629987051 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852617984 33 20 (227841 / 10000)
        (2278413 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852617984 7852650752 88614 _ _ (227841 / 10000) (71279 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852617984 7852650752 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852650752 :
    ThetaLowerSegment 7852650752 7852683520 (785112629987051 / 100000)
      (785115990641801 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852650752 33 20 (227841 / 10000)
        (2278413 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852650752 7852683520 88615 _ _ (227841 / 10000) (71279 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852650752 7852683520 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852683520 :
    ThetaLowerSegment 7852683520 7852716288 (785115990641801 / 100000)
      (785119203201311 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852683520 33 20 (2278411 / 100000)
        (1139207 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852683520 7852716288 88615 _ _ (2278411 / 100000) (222747 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852683520 7852716288 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852716288 :
    ThetaLowerSegment 7852716288 7852749056 (785119203201311 / 100000)
      (392561193070739 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852716288 33 20 (2278411 / 100000)
        (1139207 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852716288 7852749056 88615 _ _ (2278411 / 100000) (222747 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852716288 7852749056 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852749056 :
    ThetaLowerSegment 7852749056 7852781824 (392561193070739 / 50000)
      (785125746797703 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852749056 33 20 (2278411 / 100000)
        (1139207 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852749056 7852781824 88615 _ _ (2278411 / 100000) (222747 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852749056 7852781824 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852781824 :
    ThetaLowerSegment 7852781824 7852814592 (785125746797703 / 100000)
      (785128977585919 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852781824 33 20 (569603 / 25000)
        (455683 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852781824 7852814592 88615 _ _ (569603 / 25000) (890989 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852781824 7852814592 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852814592 :
    ThetaLowerSegment 7852814592 7852847360 (785128977585919 / 100000)
      (785132274448083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852814592 33 20 (569603 / 25000)
        (455683 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852814592 7852847360 88616 _ _ (569603 / 25000) (890989 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852814592 7852847360 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852847360 :
    ThetaLowerSegment 7852847360 7852880128 (785132274448083 / 100000)
      (392567771985369 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852847360 33 20 (2278413 / 100000)
        (142401 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852847360 7852880128 88616 _ _ (2278413 / 100000) (89099 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852847360 7852880128 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852880128 :
    ThetaLowerSegment 7852880128 7852912896 (392567771985369 / 50000) (24535588704873 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852880128 33 20 (2278413 / 100000)
        (142401 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852880128 7852912896 88616 _ _ (2278413 / 100000) (89099 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852880128 7852912896 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852912896 :
    ThetaLowerSegment 7852912896 7852945664 (24535588704873 / 3125) (78514207618223 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852912896 33 20 (1139207 / 50000)
        (2278417 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852912896 7852945664 88616 _ _ (1139207 / 50000) (1781981 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852912896 7852945664 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852945664 :
    ThetaLowerSegment 7852945664 7852978432 (78514207618223 / 10000) (392572696776507 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852945664 33 20 (1139207 / 50000)
        (2278417 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852945664 7852978432 88616 _ _ (1139207 / 50000) (1781981 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852945664 7852978432 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7852978432 :
    ThetaLowerSegment 7852978432 7853011200 (392572696776507 / 50000)
      (392574316728861 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7852978432 33 20 (1139207 / 50000)
        (2278417 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7852978432 7853011200 88617 _ _ (1139207 / 50000) (1781981 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7852978432 7853011200 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853011200 :
    ThetaLowerSegment 7853011200 7853043968 (392574316728861 / 50000) (49072000629297 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853011200 33 20 (455683 / 20000)
        (1139209 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853011200 7853043968 88617 _ _ (455683 / 20000) (1781983 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853011200 7853043968 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853043968 :
    ThetaLowerSegment 7853043968 7853076736 (49072000629297 / 6250) (98144418208539 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853043968 33 20 (455683 / 20000)
        (1139209 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853043968 7853076736 88617 _ _ (455683 / 20000) (1781983 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853043968 7853076736 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853076736 :
    ThetaLowerSegment 7853076736 7853109504 (98144418208539 / 12500) (98144830317033 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853076736 33 20 (142401 / 6250)
        (2278419 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853076736 7853109504 88617 _ _ (142401 / 6250) (356397 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853076736 7853109504 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853109504 :
    ThetaLowerSegment 7853109504 7853142272 (98144830317033 / 12500) (98145242710329 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853109504 33 20 (142401 / 6250)
        (2278419 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853109504 7853142272 88617 _ _ (142401 / 6250) (356397 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853109504 7853142272 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853142272 :
    ThetaLowerSegment 7853142272 7853175040 (98145242710329 / 12500) (98145665356497 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853142272 33 20 (142401 / 6250)
        (2278419 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853142272 7853175040 88617 _ _ (142401 / 6250) (356397 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853142272 7853175040 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853175040 :
    ThetaLowerSegment 7853175040 7853207808 (98145665356497 / 12500) (196292148664697 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853175040 33 20 (2278417 / 100000)
        (113921 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853175040 7853207808 88618 _ _ (2278417 / 100000) (890993 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853175040 7853207808 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853207808 :
    ThetaLowerSegment 7853207808 7853240576 (196292148664697 / 25000)
      (785171859630349 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853207808 33 20 (2278417 / 100000)
        (113921 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853207808 7853240576 88618 _ _ (2278417 / 100000) (890993 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853207808 7853240576 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853240576 :
    ThetaLowerSegment 7853240576 7853273344 (785171859630349 / 100000) (6281401434283 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853240576 33 20 (1139209 / 50000)
        (2278421 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853240576 7853273344 88618 _ _ (1139209 / 50000) (445497 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853240576 7853273344 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853273344 :
    ThetaLowerSegment 7853273344 7853306112 (6281401434283 / 800) (785178519446163 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853273344 33 20 (1139209 / 50000)
        (2278421 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853273344 7853306112 88618 _ _ (1139209 / 50000) (445497 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853273344 7853306112 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853306112 :
    ThetaLowerSegment 7853306112 7853338880 (785178519446163 / 100000) (24536928911928 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853306112 33 20 (2278419 / 100000)
        (1139211 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853306112 7853338880 88618 _ _ (2278419 / 100000) (178199 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853306112 7853338880 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853338880 :
    ThetaLowerSegment 7853338880 7853371648 (24536928911928 / 3125) (392592455205729 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853338880 33 20 (2278419 / 100000)
        (1139211 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853338880 7853371648 88619 _ _ (2278419 / 100000) (178199 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853338880 7853371648 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853371648 :
    ThetaLowerSegment 7853371648 7853404416 (392592455205729 / 50000)
      (785188211840589 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853371648 33 20 (2278419 / 100000)
        (1139211 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853371648 7853404416 88619 _ _ (2278419 / 100000) (178199 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853371648 7853404416 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853404416 :
    ThetaLowerSegment 7853404416 7853437184 (785188211840589 / 100000)
      (785191495043809 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853404416 33 20 (113921 / 5000)
        (2278423 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853404416 7853437184 88619 _ _ (113921 / 5000) (1781991 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853404416 7853437184 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853437184 :
    ThetaLowerSegment 7853437184 7853469952 (785191495043809 / 100000)
      (785194796474389 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853437184 33 20 (113921 / 5000)
        (2278423 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853437184 7853469952 88619 _ _ (113921 / 5000) (1781991 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853437184 7853469952 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853469952 :
    ThetaLowerSegment 7853469952 7853502720 (785194796474389 / 100000)
      (785198063730103 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853469952 33 20 (2278421 / 100000)
        (284803 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853469952 7853502720 88619 _ _ (2278421 / 100000) (1781993 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853469952 7853502720 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853502720 :
    ThetaLowerSegment 7853502720 7853535488 (785198063730103 / 100000) (1570402766779 / 200) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853502720 33 20 (2278421 / 100000)
        (284803 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853502720 7853535488 88619 _ _ (2278421 / 100000) (1781993 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853502720 7853535488 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853535488 :
    ThetaLowerSegment 7853535488 7853568256 (1570402766779 / 200) (39260233215787 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853535488 33 20 (2278421 / 100000)
        (284803 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853535488 7853568256 88620 _ _ (2278421 / 100000) (1781993 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853535488 7853568256 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853568256 :
    ThetaLowerSegment 7853568256 7853601024 (39260233215787 / 5000) (392603985153031 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853568256 33 20 (1139211 / 50000)
        (91137 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853568256 7853601024 88620 _ _ (1139211 / 50000) (356399 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853568256 7853601024 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853601024 :
    ThetaLowerSegment 7853601024 7853633792 (392603985153031 / 50000) (49075701350891 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853601024 33 20 (1139211 / 50000)
        (91137 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853601024 7853633792 88620 _ _ (1139211 / 50000) (356399 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853601024 7853633792 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853633792 :
    ThetaLowerSegment 7853633792 7853666560 (49075701350891 / 6250) (785214500264953 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853633792 33 20 (2278423 / 100000)
        (1139213 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853633792 7853666560 88620 _ _ (2278423 / 100000) (445499 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853633792 7853666560 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853666560 :
    ThetaLowerSegment 7853666560 7853699328 (785214500264953 / 100000) (9815221382037 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853666560 33 20 (2278423 / 100000)
        (1139213 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853666560 7853699328 88620 _ _ (2278423 / 100000) (445499 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853666560 7853699328 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853699328 :
    ThetaLowerSegment 7853699328 7853732096 (9815221382037 / 1250) (24538154987362 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853699328 33 20 (284803 / 12500)
        (2278427 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853699328 7853732096 88621 _ _ (284803 / 12500) (890999 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853699328 7853732096 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853732096 :
    ThetaLowerSegment 7853732096 7853764864 (24538154987362 / 3125) (98153013262391 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853732096 33 20 (284803 / 12500)
        (2278427 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853732096 7853764864 88621 _ _ (284803 / 12500) (890999 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853732096 7853764864 12 1381 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853764864 :
    ThetaLowerSegment 7853764864 7853797632 (98153013262391 / 12500) (98153436479649 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853764864 33 20 (284803 / 12500)
        (2278427 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853764864 7853797632 88621 _ _ (284803 / 12500) (890999 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853764864 7853797632 12 1486 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853797632 :
    ThetaLowerSegment 7853797632 7853830400 (98153436479649 / 12500)
      (785230683910617 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853797632 33 20 (91137 / 4000) (569607 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853797632 7853830400 88621 _ _ (91137 / 4000) (891 / 50) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853797632 7853830400 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853830400 :
    ThetaLowerSegment 7853830400 7853863168 (785230683910617 / 100000)
      (392617070140671 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853830400 33 20 (91137 / 4000) (569607 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853830400 7853863168 88621 _ _ (91137 / 4000) (891 / 50) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853830400 7853863168 12 1517 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853863168 :
    ThetaLowerSegment 7853863168 7853895936 (392617070140671 / 50000)
      (392618760732763 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853863168 33 20 (1139213 / 50000)
        (2278429 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853863168 7853895936 88622 _ _ (1139213 / 50000) (1782001 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853863168 7853895936 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853895936 :
    ThetaLowerSegment 7853895936 7853928704 (392618760732763 / 50000)
      (392620421705317 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853895936 33 20 (1139213 / 50000)
        (2278429 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853895936 7853928704 88622 _ _ (1139213 / 50000) (1782001 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853895936 7853928704 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853928704 :
    ThetaLowerSegment 7853928704 7853961472 (392620421705317 / 50000)
      (392622110018983 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853928704 33 20 (1139213 / 50000)
        (2278429 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853928704 7853961472 88622 _ _ (1139213 / 50000) (1782001 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853928704 7853961472 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853961472 :
    ThetaLowerSegment 7853961472 7853994240 (392622110018983 / 50000)
      (392623736815861 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853961472 33 20 (2278427 / 100000)
        (227843 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853961472 7853994240 88622 _ _ (2278427 / 100000) (1782003 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853961472 7853994240 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7853994240 :
    ThetaLowerSegment 7853994240 7854027008 (392623736815861 / 50000)
      (785250702162781 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7853994240 33 20 (2278427 / 100000)
        (227843 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7853994240 7854027008 88622 _ _ (2278427 / 100000) (1782003 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7853994240 7854027008 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854027008 :
    ThetaLowerSegment 7854027008 7854059776 (785250702162781 / 100000)
      (157050786594737 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854027008 33 20 (569607 / 25000)
        (2278431 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854027008 7854059776 88622 _ _ (569607 / 25000) (445501 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854027008 7854059776 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854059776 :
    ThetaLowerSegment 7854059776 7854092544 (157050786594737 / 20000)
      (785257113659173 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854059776 33 20 (569607 / 25000)
        (2278431 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854059776 7854092544 88623 _ _ (569607 / 25000) (445501 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854059776 7854092544 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854092544 :
    ThetaLowerSegment 7854092544 7854125312 (785257113659173 / 100000)
      (157052082564873 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854092544 33 20 (2278429 / 100000)
        (71201 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854092544 7854125312 88623 _ _ (2278429 / 100000) (891003 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854092544 7854125312 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854125312 :
    ThetaLowerSegment 7854125312 7854158080 (157052082564873 / 20000)
      (785263634522971 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854125312 33 20 (2278429 / 100000)
        (71201 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854125312 7854158080 88623 _ _ (2278429 / 100000) (891003 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854125312 7854158080 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854158080 :
    ThetaLowerSegment 7854158080 7854190848 (785263634522971 / 100000)
      (98158355603679 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854158080 33 20 (2278429 / 100000)
        (71201 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854158080 7854190848 88623 _ _ (2278429 / 100000) (891003 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854158080 7854190848 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854190848 :
    ThetaLowerSegment 7854190848 7854223616 (98158355603679 / 12500) (392635084529401 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854190848 33 20 (227843 / 10000)
        (2278433 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854190848 7854223616 88623 _ _ (227843 / 10000) (222751 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854190848 7854223616 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854223616 :
    ThetaLowerSegment 7854223616 7854256384 (392635084529401 / 50000)
      (392636677151971 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854223616 33 20 (227843 / 10000)
        (2278433 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854223616 7854256384 88624 _ _ (227843 / 10000) (222751 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854223616 7854256384 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854256384 :
    ThetaLowerSegment 7854256384 7854289152 (392636677151971 / 50000)
      (785276632966151 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854256384 33 20 (2278431 / 100000)
        (1139217 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854256384 7854289152 88624 _ _ (2278431 / 100000) (1782009 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854256384 7854289152 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854289152 :
    ThetaLowerSegment 7854289152 7854321920 (785276632966151 / 100000) (24539997807994 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854289152 33 20 (2278431 / 100000)
        (1139217 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854289152 7854321920 88624 _ _ (2278431 / 100000) (1782009 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854289152 7854321920 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854321920 :
    ThetaLowerSegment 7854321920 7854354688 (24539997807994 / 3125) (785283153835673 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854321920 33 20 (2278431 / 100000)
        (1139217 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854321920 7854354688 88624 _ _ (2278431 / 100000) (1782009 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854321920 7854354688 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854354688 :
    ThetaLowerSegment 7854354688 7854387456 (785283153835673 / 100000)
      (785286427942457 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854354688 33 20 (71201 / 3125) (455687 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854354688 7854387456 88624 _ _ (71201 / 3125) (1782011 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854354688 7854387456 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854387456 :
    ThetaLowerSegment 7854387456 7854420224 (785286427942457 / 100000)
      (785289806857113 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854387456 33 20 (71201 / 3125) (455687 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854387456 7854420224 88624 _ _ (71201 / 3125) (1782011 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854387456 7854420224 12 1483 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854420224 :
    ThetaLowerSegment 7854420224 7854452992 (785289806857113 / 100000)
      (392646540482667 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854420224 33 20 (2278433 / 100000)
        (569609 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854420224 7854452992 88625 _ _ (2278433 / 100000) (1782013 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854420224 7854452992 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854452992 :
    ThetaLowerSegment 7854452992 7854485760 (392646540482667 / 50000)
      (157059239116649 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854452992 33 20 (2278433 / 100000)
        (569609 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854452992 7854485760 88625 _ _ (2278433 / 100000) (1782013 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854452992 7854485760 12 1367 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854485760 :
    ThetaLowerSegment 7854485760 7854518528 (157059239116649 / 20000)
      (785299399061449 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854485760 33 20 (1139217 / 50000)
        (2278437 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854485760 7854518528 88625 _ _ (1139217 / 50000) (891007 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854485760 7854518528 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854518528 :
    ThetaLowerSegment 7854518528 7854551296 (785299399061449 / 100000) (31412111665987 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854518528 33 20 (1139217 / 50000)
        (2278437 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854518528 7854551296 88625 _ _ (1139217 / 50000) (891007 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854518528 7854551296 12 1489 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854551296 :
    ThetaLowerSegment 7854551296 7854584064 (31412111665987 / 4000) (785306029304389 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854551296 33 20 (1139217 / 50000)
        (2278437 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854551296 7854584064 88625 _ _ (1139217 / 50000) (891007 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854551296 7854584064 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854584064 :
    ThetaLowerSegment 7854584064 7854616832 (785306029304389 / 100000)
      (196327307626391 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854584064 33 20 (455687 / 20000)
        (1139219 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854584064 7854616832 88626 _ _ (455687 / 20000) (55688 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854584064 7854616832 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854616832 :
    ThetaLowerSegment 7854616832 7854649600 (196327307626391 / 25000)
      (785312454491089 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854616832 33 20 (455687 / 20000)
        (1139219 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854616832 7854649600 88626 _ _ (455687 / 20000) (55688 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854616832 7854649600 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854649600 :
    ThetaLowerSegment 7854649600 7854682368 (785312454491089 / 100000)
      (785315762780161 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854649600 33 20 (569609 / 25000)
        (2278439 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854649600 7854682368 88626 _ _ (569609 / 25000) (891009 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854649600 7854682368 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854682368 :
    ThetaLowerSegment 7854682368 7854715136 (785315762780161 / 100000)
      (785319084739849 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854682368 33 20 (569609 / 25000)
        (2278439 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854682368 7854715136 88626 _ _ (569609 / 25000) (891009 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854682368 7854715136 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854715136 :
    ThetaLowerSegment 7854715136 7854747904 (785319084739849 / 100000)
      (785322297334609 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854715136 33 20 (569609 / 25000)
        (2278439 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854715136 7854747904 88626 _ _ (569609 / 25000) (891009 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854715136 7854747904 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854747904 :
    ThetaLowerSegment 7854747904 7854780672 (785322297334609 / 100000) (24541426813412 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854747904 33 20 (2278437 / 100000)
        (56961 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854747904 7854780672 88627 _ _ (2278437 / 100000) (1782019 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854747904 7854780672 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854780672 :
    ThetaLowerSegment 7854780672 7854813440 (24541426813412 / 3125) (785328959484397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854780672 33 20 (2278437 / 100000)
        (56961 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854780672 7854813440 88627 _ _ (2278437 / 100000) (1782019 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854780672 7854813440 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854813440 :
    ThetaLowerSegment 7854813440 7854846208 (785328959484397 / 100000)
      (785332194866357 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854813440 33 20 (1139219 / 50000)
        (2278441 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854813440 7854846208 88627 _ _ (1139219 / 50000) (1782021 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854813440 7854846208 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854846208 :
    ThetaLowerSegment 7854846208 7854878976 (785332194866357 / 100000)
      (157067091062227 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854846208 33 20 (1139219 / 50000)
        (2278441 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854846208 7854878976 88627 _ _ (1139219 / 50000) (1782021 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854846208 7854878976 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854878976 :
    ThetaLowerSegment 7854878976 7854911744 (157067091062227 / 20000)
      (785338658796369 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854878976 33 20 (2278439 / 100000)
        (1139221 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854878976 7854911744 88627 _ _ (2278439 / 100000) (1782023 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854878976 7854911744 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854911744 :
    ThetaLowerSegment 7854911744 7854944512 (785338658796369 / 100000)
      (785341798485311 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854911744 33 20 (2278439 / 100000)
        (1139221 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854911744 7854944512 88627 _ _ (2278439 / 100000) (1782023 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854911744 7854944512 12 1378 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854944512 :
    ThetaLowerSegment 7854944512 7854977280 (785341798485311 / 100000)
      (157069018621621 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854944512 33 20 (2278439 / 100000)
        (1139221 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854944512 7854977280 88628 _ _ (2278439 / 100000) (1782023 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854944512 7854977280 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7854977280 :
    ThetaLowerSegment 7854977280 7855010048 (157069018621621 / 20000) (31413933413129 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7854977280 33 20 (56961 / 2500)
        (2278443 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7854977280 7855010048 88628 _ _ (56961 / 2500) (222753 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7854977280 7855010048 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855010048 :
    ThetaLowerSegment 7855010048 7855042816 (31413933413129 / 4000) (157070331914437 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855010048 33 20 (56961 / 2500)
        (2278443 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855010048 7855042816 88628 _ _ (56961 / 2500) (222753 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855010048 7855042816 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855042816 :
    ThetaLowerSegment 7855042816 7855075584 (157070331914437 / 20000) (49084679083667 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855042816 33 20 (2278441 / 100000)
        (569611 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855042816 7855075584 88628 _ _ (2278441 / 100000) (891013 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855042816 7855075584 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855075584 :
    ThetaLowerSegment 7855075584 7855108352 (49084679083667 / 6250) (19633954113031 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855075584 33 20 (2278441 / 100000)
        (569611 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855075584 7855108352 88628 _ _ (2278441 / 100000) (891013 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855075584 7855108352 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855108352 :
    ThetaLowerSegment 7855108352 7855141120 (19633954113031 / 2500) (392680807040457 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855108352 33 20 (2278441 / 100000)
        (569611 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855108352 7855141120 88629 _ _ (2278441 / 100000) (891013 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855108352 7855141120 12 1514 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855141120 :
    ThetaLowerSegment 7855141120 7855173888 (392680807040457 / 50000) (78536495883377 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855141120 33 20 (1139221 / 50000)
        (455689 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855141120 7855173888 88629 _ _ (1139221 / 50000) (445507 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855141120 7855173888 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855173888 :
    ThetaLowerSegment 7855173888 7855206656 (78536495883377 / 10000) (392684101667589 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855173888 33 20 (1139221 / 50000)
        (455689 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855173888 7855206656 88629 _ _ (1139221 / 50000) (445507 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855173888 7855206656 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855206656 :
    ThetaLowerSegment 7855206656 7855239424 (392684101667589 / 50000) (15707432602269 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855206656 33 20 (2278443 / 100000)
        (1139223 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855206656 7855239424 88629 _ _ (2278443 / 100000) (1782029 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855206656 7855239424 12 1504 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855239424 :
    ThetaLowerSegment 7855239424 7855272192 (15707432602269 / 2000) (98171857618203 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855239424 33 20 (2278443 / 100000)
        (1139223 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855239424 7855272192 88629 _ _ (2278443 / 100000) (1782029 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855239424 7855272192 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855272192 :
    ThetaLowerSegment 7855272192 7855304960 (98171857618203 / 12500) (39268904702883 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855272192 33 20 (569611 / 25000)
        (2278447 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855272192 7855304960 88629 _ _ (569611 / 25000) (1782031 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855272192 7855304960 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855304960 :
    ThetaLowerSegment 7855304960 7855337728 (39268904702883 / 5000) (196345319830593 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855304960 33 20 (569611 / 25000)
        (2278447 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855304960 7855337728 88630 _ _ (569611 / 25000) (1782031 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855304960 7855337728 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855337728 :
    ThetaLowerSegment 7855337728 7855370496 (196345319830593 / 25000) (49086530603123 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855337728 33 20 (569611 / 25000)
        (2278447 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855337728 7855370496 88630 _ _ (569611 / 25000) (1782031 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855337728 7855370496 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855370496 :
    ThetaLowerSegment 7855370496 7855403264 (49086530603123 / 6250) (785387891368353 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855370496 33 20 (455689 / 20000)
        (142403 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855370496 7855403264 88630 _ _ (455689 / 20000) (1782033 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855370496 7855403264 12 1493 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855403264 :
    ThetaLowerSegment 7855403264 7855436032 (785387891368353 / 100000)
      (392695564519349 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855403264 33 20 (455689 / 20000)
        (142403 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855403264 7855436032 88630 _ _ (455689 / 20000) (1782033 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855403264 7855436032 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855436032 :
    ThetaLowerSegment 7855436032 7855468800 (392695564519349 / 50000)
      (196348597373731 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855436032 33 20 (1139223 / 50000)
        (2278449 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855436032 7855468800 88630 _ _ (1139223 / 50000) (891017 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855436032 7855468800 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855468800 :
    ThetaLowerSegment 7855468800 7855501568 (196348597373731 / 25000) (49087351840321 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855468800 33 20 (1139223 / 50000)
        (2278449 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855468800 7855501568 88631 _ _ (1139223 / 50000) (891017 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855468800 7855501568 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855501568 :
    ThetaLowerSegment 7855501568 7855534336 (49087351840321 / 6250) (392700456342911 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855501568 33 20 (1139223 / 50000)
        (2278449 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855501568 7855534336 88631 _ _ (1139223 / 50000) (891017 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855501568 7855534336 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855534336 :
    ThetaLowerSegment 7855534336 7855567104 (392700456342911 / 50000) (78540424833223 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855534336 33 20 (2278447 / 100000)
        (45569 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855534336 7855567104 88631 _ _ (2278447 / 100000) (445509 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855534336 7855567104 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855567104 :
    ThetaLowerSegment 7855567104 7855599872 (78540424833223 / 10000) (24543983439259 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855567104 33 20 (2278447 / 100000)
        (45569 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855567104 7855599872 88631 _ _ (2278447 / 100000) (445509 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855567104 7855599872 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855599872 :
    ThetaLowerSegment 7855599872 7855632640 (24543983439259 / 3125) (49088172366047 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855599872 33 20 (142403 / 6250)
        (2278451 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855599872 7855632640 88631 _ _ (142403 / 6250) (1782037 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855599872 7855632640 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855632640 :
    ThetaLowerSegment 7855632640 7855665408 (49088172366047 / 6250) (9817675940963 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855632640 33 20 (142403 / 6250)
        (2278451 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855632640 7855665408 88632 _ _ (142403 / 6250) (1782037 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855632640 7855665408 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855665408 :
    ThetaLowerSegment 7855665408 7855698176 (9817675940963 / 1250) (785417335737559 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855665408 33 20 (2278449 / 100000)
        (569613 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855665408 7855698176 88632 _ _ (2278449 / 100000) (1782039 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855665408 7855698176 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855698176 :
    ThetaLowerSegment 7855698176 7855730944 (785417335737559 / 100000)
      (196355157024091 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855698176 33 20 (2278449 / 100000)
        (569613 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855698176 7855730944 88632 _ _ (2278449 / 100000) (1782039 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855698176 7855730944 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855730944 :
    ThetaLowerSegment 7855730944 7855763712 (196355157024091 / 25000)
      (196355981822629 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855730944 33 20 (2278449 / 100000)
        (569613 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855730944 7855763712 88632 _ _ (2278449 / 100000) (1782039 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855730944 7855763712 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855763712 :
    ThetaLowerSegment 7855763712 7855796480 (196355981822629 / 25000)
      (196356788393929 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855763712 33 20 (45569 / 2000)
        (2278453 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855763712 7855796480 88632 _ _ (45569 / 2000) (1782041 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855763712 7855796480 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855796480 :
    ThetaLowerSegment 7855796480 7855829248 (196356788393929 / 25000)
      (392715248030933 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855796480 33 20 (45569 / 2000)
        (2278453 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855796480 7855829248 88632 _ _ (45569 / 2000) (1782041 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855796480 7855829248 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855829248 :
    ThetaLowerSegment 7855829248 7855862016 (392715248030933 / 50000)
      (196358443118601 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855829248 33 20 (2278451 / 100000)
        (1139227 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855829248 7855862016 88633 _ _ (2278451 / 100000) (891021 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855829248 7855862016 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855862016 :
    ThetaLowerSegment 7855862016 7855894784 (196358443118601 / 25000)
      (392718574569393 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855862016 33 20 (2278451 / 100000)
        (1139227 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855862016 7855894784 88633 _ _ (2278451 / 100000) (891021 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855862016 7855894784 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855894784 :
    ThetaLowerSegment 7855894784 7855927552 (392718574569393 / 50000)
      (392720225307867 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855894784 33 20 (569613 / 25000)
        (455691 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855894784 7855927552 88633 _ _ (569613 / 25000) (445511 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855894784 7855927552 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855927552 :
    ThetaLowerSegment 7855927552 7855960320 (392720225307867 / 50000)
      (392721881742471 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855927552 33 20 (569613 / 25000)
        (455691 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855927552 7855960320 88633 _ _ (569613 / 25000) (445511 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855927552 7855960320 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855960320 :
    ThetaLowerSegment 7855960320 7855993088 (392721881742471 / 50000)
      (392723522227911 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855960320 33 20 (569613 / 25000)
        (455691 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855960320 7855993088 88633 _ _ (569613 / 25000) (445511 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855960320 7855993088 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7855993088 :
    ThetaLowerSegment 7855993088 7856025856 (392723522227911 / 50000)
      (392725153600259 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7855993088 33 20 (2278453 / 100000)
        (284807 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7855993088 7856025856 88634 _ _ (2278453 / 100000) (891023 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7855993088 7856025856 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856025856 :
    ThetaLowerSegment 7856025856 7856058624 (392725153600259 / 50000)
      (196363391347077 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856025856 33 20 (2278453 / 100000)
        (284807 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856025856 7856058624 88634 _ _ (2278453 / 100000) (891023 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856025856 7856058624 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856058624 :
    ThetaLowerSegment 7856058624 7856091392 (196363391347077 / 25000)
      (196364218425879 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856058624 33 20 (1139227 / 50000)
        (2278457 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856058624 7856091392 88634 _ _ (1139227 / 50000) (1782047 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856058624 7856091392 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856091392 :
    ThetaLowerSegment 7856091392 7856124160 (196364218425879 / 25000)
      (196365022720141 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856091392 33 20 (1139227 / 50000)
        (2278457 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856091392 7856124160 88634 _ _ (1139227 / 50000) (1782047 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856091392 7856124160 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856124160 :
    ThetaLowerSegment 7856124160 7856156928 (196365022720141 / 25000) (98182927747539 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856124160 33 20 (1139227 / 50000)
        (2278457 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856124160 7856156928 88634 _ _ (1139227 / 50000) (1782047 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856124160 7856156928 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856156928 :
    ThetaLowerSegment 7856156928 7856189696 (98182927747539 / 12500)
      (785466718904697 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856156928 33 20 (455691 / 20000)
        (1139229 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856156928 7856189696 88634 _ _ (455691 / 20000) (1782049 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856156928 7856189696 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856189696 :
    ThetaLowerSegment 7856189696 7856222464 (785466718904697 / 100000)
      (392735003357631 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856189696 33 20 (455691 / 20000)
        (1139229 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856189696 7856222464 88635 _ _ (455691 / 20000) (1782049 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856189696 7856222464 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856222464 :
    ThetaLowerSegment 7856222464 7856255232 (392735003357631 / 50000)
      (392736617643707 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856222464 33 20 (284807 / 12500)
        (2278459 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856222464 7856255232 88635 _ _ (284807 / 12500) (1782051 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856222464 7856255232 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856255232 :
    ThetaLowerSegment 7856255232 7856288000 (392736617643707 / 50000)
      (392738222815959 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856255232 33 20 (284807 / 12500)
        (2278459 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856255232 7856288000 88635 _ _ (284807 / 12500) (1782051 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856255232 7856288000 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856288000 :
    ThetaLowerSegment 7856288000 7856320768 (392738222815959 / 50000)
      (392739908874139 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856288000 33 20 (2278457 / 100000)
        (113923 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856288000 7856320768 88635 _ _ (2278457 / 100000) (445513 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856288000 7856320768 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856320768 :
    ThetaLowerSegment 7856320768 7856353536 (392739908874139 / 50000)
      (392741622273803 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856320768 33 20 (2278457 / 100000)
        (113923 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856320768 7856353536 88635 _ _ (2278457 / 100000) (445513 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856320768 7856353536 12 1504 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856353536 :
    ThetaLowerSegment 7856353536 7856386304 (392741622273803 / 50000) (49092909269391 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856353536 33 20 (2278457 / 100000)
        (113923 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856353536 7856386304 88636 _ _ (2278457 / 100000) (445513 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856353536 7856386304 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856386304 :
    ThetaLowerSegment 7856386304 7856419072 (49092909269391 / 6250) (392744890721079 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856386304 33 20 (1139229 / 50000)
        (2278461 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856386304 7856419072 88636 _ _ (1139229 / 50000) (891027 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856386304 7856419072 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856419072 :
    ThetaLowerSegment 7856419072 7856451840 (392744890721079 / 50000) (98186644479807 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856419072 33 20 (1139229 / 50000)
        (2278461 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856419072 7856451840 88636 _ _ (1139229 / 50000) (891027 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856419072 7856451840 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856451840 :
    ThetaLowerSegment 7856451840 7856484608 (98186644479807 / 12500) (24546763080992 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856451840 33 20 (2278459 / 100000)
        (1139231 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856451840 7856484608 88636 _ _ (2278459 / 100000) (222757 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856451840 7856484608 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856484608 :
    ThetaLowerSegment 7856484608 7856517376 (24546763080992 / 3125) (392749847507893 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856484608 33 20 (2278459 / 100000)
        (1139231 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856484608 7856517376 88636 _ _ (2278459 / 100000) (222757 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856484608 7856517376 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856517376 :
    ThetaLowerSegment 7856517376 7856550144 (392749847507893 / 50000) (98187883961503 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856517376 33 20 (2278459 / 100000)
        (1139231 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856517376 7856550144 88636 _ _ (2278459 / 100000) (222757 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856517376 7856550144 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856550144 :
    ThetaLowerSegment 7856550144 7856582912 (98187883961503 / 12500) (196376594434371 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856550144 33 20 (113923 / 5000)
        (2278463 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856550144 7856582912 88637 _ _ (113923 / 5000) (1782057 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856550144 7856582912 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856582912 :
    ThetaLowerSegment 7856582912 7856615680 (196376594434371 / 25000) (98188703067873 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856582912 33 20 (113923 / 5000)
        (2278463 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856582912 7856615680 88637 _ _ (113923 / 5000) (1782057 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856582912 7856615680 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856615680 :
    ThetaLowerSegment 7856615680 7856648448 (98188703067873 / 12500)
      (785512866792987 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856615680 33 20 (2278461 / 100000)
        (71202 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856615680 7856648448 88637 _ _ (2278461 / 100000) (1782059 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856615680 7856648448 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856648448 :
    ThetaLowerSegment 7856648448 7856681216 (785512866792987 / 100000) (6284129510313 / 800) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856648448 33 20 (2278461 / 100000)
        (71202 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856648448 7856681216 88637 _ _ (2278461 / 100000) (1782059 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856648448 7856681216 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856681216 :
    ThetaLowerSegment 7856681216 7856713984 (6284129510313 / 800) (785519417369779 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856681216 33 20 (1139231 / 50000)
        (455693 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856681216 7856713984 88637 _ _ (1139231 / 50000) (1782061 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856681216 7856713984 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856713984 :
    ThetaLowerSegment 7856713984 7856746752 (785519417369779 / 100000)
      (157104543316551 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856713984 33 20 (1139231 / 50000)
        (455693 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856713984 7856746752 88638 _ _ (1139231 / 50000) (1782061 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856713984 7856746752 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856746752 :
    ThetaLowerSegment 7856746752 7856779520 (157104543316551 / 20000)
      (785525965669567 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856746752 33 20 (1139231 / 50000)
        (455693 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856746752 7856779520 88638 _ _ (1139231 / 50000) (1782061 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856746752 7856779520 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856779520 :
    ThetaLowerSegment 7856779520 7856812288 (785525965669567 / 100000)
      (392764642695079 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856779520 33 20 (2278463 / 100000)
        (1139233 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856779520 7856812288 88638 _ _ (2278463 / 100000) (891031 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856779520 7856812288 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856812288 :
    ThetaLowerSegment 7856812288 7856845056 (392764642695079 / 50000) (24547891417642 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856812288 33 20 (2278463 / 100000)
        (1139233 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856812288 7856845056 88638 _ _ (2278463 / 100000) (891031 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856812288 7856845056 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856845056 :
    ThetaLowerSegment 7856845056 7856877824 (24547891417642 / 3125) (24547997864632 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856845056 33 20 (71202 / 3125)
        (2278467 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856845056 7856877824 88638 _ _ (71202 / 3125) (111379 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856845056 7856877824 12 1495 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856877824 :
    ThetaLowerSegment 7856877824 7856910592 (24547997864632 / 3125) (24548096265796 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856877824 33 20 (71202 / 3125)
        (2278467 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856877824 7856910592 88639 _ _ (71202 / 3125) (111379 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856877824 7856910592 12 1382 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856910592 :
    ThetaLowerSegment 7856910592 7856943360 (24548096265796 / 3125) (24548198725474 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856910592 33 20 (71202 / 3125)
        (2278467 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856910592 7856943360 88639 _ _ (71202 / 3125) (111379 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856910592 7856943360 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856943360 :
    ThetaLowerSegment 7856943360 7856976128 (24548198725474 / 3125) (785545583243143 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856943360 33 20 (455693 / 20000)
        (569617 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856943360 7856976128 88639 _ _ (455693 / 20000) (891033 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856943360 7856976128 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7856976128 :
    ThetaLowerSegment 7856976128 7857008896 (785545583243143 / 100000) (49096805296183 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7856976128 33 20 (455693 / 20000)
        (569617 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7856976128 7857008896 88639 _ _ (455693 / 20000) (891033 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7856976128 7857008896 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857008896 :
    ThetaLowerSegment 7857008896 7857041664 (49096805296183 / 6250) (196388047128657 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857008896 33 20 (1139233 / 50000)
        (2278469 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857008896 7857041664 88639 _ _ (1139233 / 50000) (1782067 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857008896 7857041664 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857041664 :
    ThetaLowerSegment 7857041664 7857074432 (196388047128657 / 25000)
      (392777715385873 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857041664 33 20 (1139233 / 50000)
        (2278469 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857041664 7857074432 88639 _ _ (1139233 / 50000) (1782067 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857041664 7857074432 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857074432 :
    ThetaLowerSegment 7857074432 7857107200 (392777715385873 / 50000)
      (392779333097443 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857074432 33 20 (2278467 / 100000)
        (227847 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857074432 7857107200 88640 _ _ (2278467 / 100000) (1782069 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857074432 7857107200 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857107200 :
    ThetaLowerSegment 7857107200 7857139968 (392779333097443 / 50000)
      (785561976807437 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857107200 33 20 (2278467 / 100000)
        (227847 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857107200 7857139968 88640 _ _ (2278467 / 100000) (1782069 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857107200 7857139968 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857139968 :
    ThetaLowerSegment 7857139968 7857172736 (785561976807437 / 100000)
      (785565216787511 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857139968 33 20 (2278467 / 100000)
        (227847 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857139968 7857172736 88640 _ _ (2278467 / 100000) (1782069 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857139968 7857172736 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857172736 :
    ThetaLowerSegment 7857172736 7857205504 (785565216787511 / 100000)
      (785568418035051 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857172736 33 20 (569617 / 25000)
        (2278471 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857172736 7857205504 88640 _ _ (569617 / 25000) (1782071 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857172736 7857205504 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857205504 :
    ThetaLowerSegment 7857205504 7857238272 (785568418035051 / 100000)
      (785571658016547 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857205504 33 20 (569617 / 25000)
        (2278471 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857205504 7857238272 88640 _ _ (569617 / 25000) (1782071 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857205504 7857238272 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857238272 :
    ThetaLowerSegment 7857238272 7857271040 (785571658016547 / 100000)
      (392787468366719 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857238272 33 20 (2278469 / 100000)
        (284809 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857238272 7857271040 88641 _ _ (2278469 / 100000) (222759 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857238272 7857271040 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857271040 :
    ThetaLowerSegment 7857271040 7857303808 (392787468366719 / 50000)
      (157115631242027 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857271040 33 20 (2278469 / 100000)
        (284809 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857271040 7857303808 88641 _ _ (2278469 / 100000) (222759 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857271040 7857303808 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857303808 :
    ThetaLowerSegment 7857303808 7857336576 (157115631242027 / 20000)
      (196395382655681 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857303808 33 20 (2278469 / 100000)
        (284809 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857303808 7857336576 88641 _ _ (2278469 / 100000) (222759 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857303808 7857336576 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857336576 :
    ThetaLowerSegment 7857336576 7857369344 (196395382655681 / 25000)
      (196396207461821 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857336576 33 20 (227847 / 10000)
        (2278473 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857336576 7857369344 88641 _ _ (227847 / 10000) (891037 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857336576 7857369344 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857369344 :
    ThetaLowerSegment 7857369344 7857402112 (196396207461821 / 25000)
      (196397011761731 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857369344 33 20 (227847 / 10000)
        (2278473 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857369344 7857402112 88641 _ _ (227847 / 10000) (891037 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857369344 7857402112 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857402112 :
    ThetaLowerSegment 7857402112 7857434880 (196397011761731 / 25000)
      (392795661744111 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857402112 33 20 (2278471 / 100000)
        (1139237 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857402112 7857434880 88641 _ _ (2278471 / 100000) (71283 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857402112 7857434880 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857434880 :
    ThetaLowerSegment 7857434880 7857467648 (392795661744111 / 50000) (24549830108562 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857434880 33 20 (2278471 / 100000)
        (1139237 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857434880 7857467648 88642 _ _ (2278471 / 100000) (71283 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857434880 7857467648 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857467648 :
    ThetaLowerSegment 7857467648 7857500416 (24549830108562 / 3125) (19639942865019 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857467648 33 20 (284809 / 12500) (91139 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857467648 7857500416 88642 _ _ (284809 / 12500) (1782077 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857467648 7857500416 12 1383 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857500416 :
    ThetaLowerSegment 7857500416 7857533184 (19639942865019 / 2500) (24550030329289 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857500416 33 20 (284809 / 12500) (91139 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857500416 7857533184 88642 _ _ (284809 / 12500) (1782077 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857500416 7857533184 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857533184 :
    ThetaLowerSegment 7857533184 7857565952 (24550030329289 / 3125) (98200536853487 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857533184 33 20 (284809 / 12500) (91139 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857533184 7857565952 88642 _ _ (284809 / 12500) (1782077 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857533184 7857565952 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857565952 :
    ThetaLowerSegment 7857565952 7857598720 (98200536853487 / 12500)
      (785607518867191 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857565952 33 20 (2278473 / 100000)
        (569619 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857565952 7857598720 88642 _ _ (2278473 / 100000) (1782079 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857565952 7857598720 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857598720 :
    ThetaLowerSegment 7857598720 7857631488 (785607518867191 / 100000)
      (785610763412743 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857598720 33 20 (2278473 / 100000)
        (569619 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857598720 7857631488 88643 _ _ (2278473 / 100000) (1782079 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857598720 7857631488 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857631488 :
    ThetaLowerSegment 7857631488 7857664256 (785610763412743 / 100000)
      (785614033022933 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857631488 33 20 (1139237 / 50000)
        (2278477 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857631488 7857664256 88643 _ _ (1139237 / 50000) (11138 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857631488 7857664256 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857664256 :
    ThetaLowerSegment 7857664256 7857697024 (785614033022933 / 100000)
      (785617261620591 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857664256 33 20 (1139237 / 50000)
        (2278477 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857664256 7857697024 88643 _ _ (1139237 / 50000) (11138 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857664256 7857697024 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857697024 :
    ThetaLowerSegment 7857697024 7857729792 (785617261620591 / 100000)
      (785620572243313 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857697024 33 20 (1139237 / 50000)
        (2278477 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857697024 7857729792 88643 _ _ (1139237 / 50000) (11138 / 625) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857697024 7857729792 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857729792 :
    ThetaLowerSegment 7857729792 7857762560 (785620572243313 / 100000)
      (98202987636911 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857729792 33 20 (91139 / 4000)
        (1139239 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857729792 7857762560 88643 _ _ (91139 / 4000) (891041 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857729792 7857762560 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857762560 :
    ThetaLowerSegment 7857762560 7857795328 (98202987636911 / 12500)
      (785627184377763 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857762560 33 20 (91139 / 4000)
        (1139239 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857762560 7857795328 88644 _ _ (91139 / 4000) (891041 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857762560 7857795328 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857795328 :
    ThetaLowerSegment 7857795328 7857828096 (785627184377763 / 100000)
      (157126089431079 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857795328 33 20 (569619 / 25000)
        (2278479 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857795328 7857828096 88644 _ _ (569619 / 25000) (445521 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857795328 7857828096 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857828096 :
    ThetaLowerSegment 7857828096 7857860864 (157126089431079 / 20000)
      (157126722847407 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857828096 33 20 (569619 / 25000)
        (2278479 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857828096 7857860864 88644 _ _ (569619 / 25000) (445521 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857828096 7857860864 12 1390 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857860864 :
    ThetaLowerSegment 7857860864 7857893632 (157126722847407 / 20000)
      (785636890686961 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857860864 33 20 (2278477 / 100000)
        (28481 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857860864 7857893632 88644 _ _ (2278477 / 100000) (356417 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857860864 7857893632 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857893632 :
    ThetaLowerSegment 7857893632 7857926400 (785636890686961 / 100000)
      (785640171693841 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857893632 33 20 (2278477 / 100000)
        (28481 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857893632 7857926400 88644 _ _ (2278477 / 100000) (356417 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857893632 7857926400 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857926400 :
    ThetaLowerSegment 7857926400 7857959168 (785640171693841 / 100000)
      (785643466371583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857926400 33 20 (2278477 / 100000)
        (28481 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857926400 7857959168 88644 _ _ (2278477 / 100000) (356417 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857926400 7857959168 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857959168 :
    ThetaLowerSegment 7857959168 7857991936 (785643466371583 / 100000)
      (785646777000117 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857959168 33 20 (1139239 / 50000)
        (2278481 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857959168 7857991936 88645 _ _ (1139239 / 50000) (1782087 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857959168 7857991936 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7857991936 :
    ThetaLowerSegment 7857991936 7858024704 (785646777000117 / 100000)
      (785650089907129 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7857991936 33 20 (1139239 / 50000)
        (2278481 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7857991936 7858024704 88645 _ _ (1139239 / 50000) (1782087 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7857991936 7858024704 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858024704 :
    ThetaLowerSegment 7858024704 7858057472 (785650089907129 / 100000)
      (196413331906447 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858024704 33 20 (2278479 / 100000)
        (1139241 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858024704 7858057472 88645 _ _ (2278479 / 100000) (1782089 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858024704 7858057472 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858057472 :
    ThetaLowerSegment 7858057472 7858090240 (196413331906447 / 25000)
      (157131323094197 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858057472 33 20 (2278479 / 100000)
        (1139241 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858057472 7858090240 88645 _ _ (2278479 / 100000) (1782089 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858057472 7858090240 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858090240 :
    ThetaLowerSegment 7858090240 7858123008 (157131323094197 / 20000)
      (196414972411327 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858090240 33 20 (2278479 / 100000)
        (1139241 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858090240 7858123008 88645 _ _ (2278479 / 100000) (1782089 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858090240 7858123008 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858123008 :
    ThetaLowerSegment 7858123008 7858155776 (196414972411327 / 25000)
      (196415769309707 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858123008 33 20 (28481 / 1250)
        (2278483 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858123008 7858155776 88646 _ _ (28481 / 1250) (178209 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858123008 7858155776 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858155776 :
    ThetaLowerSegment 7858155776 7858188544 (196415769309707 / 25000)
      (196416603233387 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858155776 33 20 (28481 / 1250)
        (2278483 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858155776 7858188544 88646 _ _ (28481 / 1250) (178209 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858155776 7858188544 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858188544 :
    ThetaLowerSegment 7858188544 7858221312 (196416603233387 / 25000) (24552179359869 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858188544 33 20 (2278481 / 100000)
        (569621 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858188544 7858221312 88646 _ _ (2278481 / 100000) (445523 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858188544 7858221312 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858221312 :
    ThetaLowerSegment 7858221312 7858254080 (24552179359869 / 3125) (785672931667689 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858221312 33 20 (2278481 / 100000)
        (569621 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858221312 7858254080 88646 _ _ (2278481 / 100000) (445523 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858221312 7858254080 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858254080 :
    ThetaLowerSegment 7858254080 7858286848 (785672931667689 / 100000)
      (785676189896949 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858254080 33 20 (1139241 / 50000)
        (455697 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858254080 7858286848 88646 _ _ (1139241 / 50000) (891047 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858254080 7858286848 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858286848 :
    ThetaLowerSegment 7858286848 7858319616 (785676189896949 / 100000)
      (785679475467993 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858286848 33 20 (1139241 / 50000)
        (455697 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858286848 7858319616 88646 _ _ (1139241 / 50000) (891047 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858286848 7858319616 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858319616 :
    ThetaLowerSegment 7858319616 7858352384 (785679475467993 / 100000)
      (785682706355469 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858319616 33 20 (1139241 / 50000)
        (455697 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858319616 7858352384 88647 _ _ (1139241 / 50000) (891047 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858319616 7858352384 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858352384 :
    ThetaLowerSegment 7858352384 7858385152 (785682706355469 / 100000)
      (785685914459533 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858352384 33 20 (2278483 / 100000)
        (1139243 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858352384 7858385152 88647 _ _ (2278483 / 100000) (356419 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858352384 7858385152 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858385152 :
    ThetaLowerSegment 7858385152 7858417920 (785685914459533 / 100000)
      (785689213702917 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858385152 33 20 (2278483 / 100000)
        (1139243 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858385152 7858417920 88647 _ _ (2278483 / 100000) (356419 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858385152 7858417920 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858417920 :
    ThetaLowerSegment 7858417920 7858450688 (785689213702917 / 100000)
      (785692519783201 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858417920 33 20 (569621 / 25000)
        (2278487 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858417920 7858450688 88647 _ _ (569621 / 25000) (1782097 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858417920 7858450688 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858450688 :
    ThetaLowerSegment 7858450688 7858483456 (785692519783201 / 100000)
      (785695841812873 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858450688 33 20 (569621 / 25000)
        (2278487 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858450688 7858483456 88647 _ _ (569621 / 25000) (1782097 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858450688 7858483456 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858483456 :
    ThetaLowerSegment 7858483456 7858516224 (785695841812873 / 100000)
      (785699056753797 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858483456 33 20 (569621 / 25000)
        (2278487 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858483456 7858516224 88648 _ _ (569621 / 25000) (1782097 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858483456 7858516224 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858516224 :
    ThetaLowerSegment 7858516224 7858548992 (785699056753797 / 100000)
      (392851174582311 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858516224 33 20 (455697 / 20000)
        (284811 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858516224 7858548992 88648 _ _ (455697 / 20000) (1782099 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858516224 7858548992 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858548992 :
    ThetaLowerSegment 7858548992 7858581760 (392851174582311 / 50000)
      (785705564106957 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858548992 33 20 (455697 / 20000)
        (284811 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858548992 7858581760 88648 _ _ (455697 / 20000) (1782099 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858548992 7858581760 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858581760 :
    ThetaLowerSegment 7858581760 7858614528 (785705564106957 / 100000)
      (785708767658273 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858581760 33 20 (1139243 / 50000)
        (2278489 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858581760 7858614528 88648 _ _ (1139243 / 50000) (17821 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858581760 7858614528 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858614528 :
    ThetaLowerSegment 7858614528 7858647296 (785708767658273 / 100000)
      (785712028171739 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858614528 33 20 (1139243 / 50000)
        (2278489 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858614528 7858647296 88648 _ _ (1139243 / 50000) (17821 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858614528 7858647296 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858647296 :
    ThetaLowerSegment 7858647296 7858680064 (785712028171739 / 100000)
      (98214412225073 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858647296 33 20 (2278487 / 100000)
        (227849 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858647296 7858680064 88649 _ _ (2278487 / 100000) (891051 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858647296 7858680064 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858680064 :
    ThetaLowerSegment 7858680064 7858712832 (98214412225073 / 12500) (24553703879318 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858680064 33 20 (2278487 / 100000)
        (227849 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858680064 7858712832 88649 _ _ (2278487 / 100000) (891051 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858680064 7858712832 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858712832 :
    ThetaLowerSegment 7858712832 7858745600 (24553703879318 / 3125) (785721884906501 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858712832 33 20 (2278487 / 100000)
        (227849 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858712832 7858745600 88649 _ _ (2278487 / 100000) (891051 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858712832 7858745600 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858745600 :
    ThetaLowerSegment 7858745600 7858778368 (785721884906501 / 100000)
      (785725168207709 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858745600 33 20 (284811 / 12500)
        (2278491 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858745600 7858778368 88649 _ _ (284811 / 12500) (222763 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858745600 7858778368 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858778368 :
    ThetaLowerSegment 7858778368 7858811136 (785725168207709 / 100000)
      (785728437837989 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858778368 33 20 (284811 / 12500)
        (2278491 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858778368 7858811136 88649 _ _ (284811 / 12500) (222763 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858778368 7858811136 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858811136 :
    ThetaLowerSegment 7858811136 7858843904 (785728437837989 / 100000)
      (785731732533083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858811136 33 20 (2278489 / 100000)
        (569623 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858811136 7858843904 88649 _ _ (2278489 / 100000) (356421 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858811136 7858843904 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858843904 :
    ThetaLowerSegment 7858843904 7858876672 (785731732533083 / 100000)
      (196433767629867 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858843904 33 20 (2278489 / 100000)
        (569623 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858843904 7858876672 88650 _ _ (2278489 / 100000) (356421 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858843904 7858876672 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858876672 :
    ThetaLowerSegment 7858876672 7858909440 (196433767629867 / 25000)
      (157147662561863 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858876672 33 20 (2278489 / 100000)
        (569623 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858876672 7858909440 88650 _ _ (2278489 / 100000) (356421 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858876672 7858909440 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858909440 :
    ThetaLowerSegment 7858909440 7858942208 (157147662561863 / 20000)
      (157148317855587 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858909440 33 20 (227849 / 10000)
        (2278493 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858909440 7858942208 88650 _ _ (227849 / 10000) (1782107 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858909440 7858942208 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858942208 :
    ThetaLowerSegment 7858942208 7858974976 (157148317855587 / 20000)
      (157148957199881 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858942208 33 20 (227849 / 10000)
        (2278493 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858942208 7858974976 88650 _ _ (227849 / 10000) (1782107 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858942208 7858974976 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7858974976 :
    ThetaLowerSegment 7858974976 7859007744 (157148957199881 / 20000)
      (157149617962271 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7858974976 33 20 (2278491 / 100000)
        (1139247 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7858974976 7859007744 88650 _ _ (2278491 / 100000) (445527 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7858974976 7859007744 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859007744 :
    ThetaLowerSegment 7859007744 7859040512 (157149617962271 / 20000)
      (196437830747521 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859007744 33 20 (2278491 / 100000)
        (1139247 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859007744 7859040512 88651 _ _ (2278491 / 100000) (445527 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859007744 7859040512 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859040512 :
    ThetaLowerSegment 7859040512 7859073280 (196437830747521 / 25000) (39287727694587 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859040512 33 20 (569623 / 25000)
        (455699 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859040512 7859073280 88651 _ _ (569623 / 25000) (178211 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859040512 7859073280 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859073280 :
    ThetaLowerSegment 7859073280 7859106048 (39287727694587 / 5000) (98219728510593 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859073280 33 20 (569623 / 25000)
        (455699 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859073280 7859106048 88651 _ _ (569623 / 25000) (178211 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859073280 7859106048 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859106048 :
    ThetaLowerSegment 7859106048 7859138816 (98219728510593 / 12500) (196440282404913 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859106048 33 20 (569623 / 25000)
        (455699 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859106048 7859138816 88651 _ _ (569623 / 25000) (178211 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859106048 7859138816 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859138816 :
    ThetaLowerSegment 7859138816 7859171584 (196440282404913 / 25000)
      (785764340016289 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859138816 33 20 (2278493 / 100000)
        (71203 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859138816 7859171584 88651 _ _ (2278493 / 100000) (55691 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859138816 7859171584 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859171584 :
    ThetaLowerSegment 7859171584 7859204352 (785764340016289 / 100000)
      (392883802548379 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859171584 33 20 (2278493 / 100000)
        (71203 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859171584 7859204352 88651 _ _ (2278493 / 100000) (55691 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859171584 7859204352 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859204352 :
    ThetaLowerSegment 7859204352 7859237120 (392883802548379 / 50000) (98221346810239 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859204352 33 20 (1139247 / 50000)
        (2278497 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859204352 7859237120 88652 _ _ (1139247 / 50000) (1782113 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859204352 7859237120 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859237120 :
    ThetaLowerSegment 7859237120 7859269888 (98221346810239 / 12500) (78577411703261 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859237120 33 20 (1139247 / 50000)
        (2278497 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859237120 7859269888 88652 _ _ (1139247 / 50000) (1782113 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859237120 7859269888 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859269888 :
    ThetaLowerSegment 7859269888 7859302656 (78577411703261 / 10000) (392888680804033 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859269888 33 20 (1139247 / 50000)
        (2278497 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859269888 7859302656 88652 _ _ (1139247 / 50000) (1782113 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859269888 7859302656 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859302656 :
    ThetaLowerSegment 7859302656 7859335424 (392888680804033 / 50000)
      (785780722388191 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859302656 33 20 (455699 / 20000)
        (1139249 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859302656 7859335424 88652 _ _ (455699 / 20000) (356423 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859302656 7859335424 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859335424 :
    ThetaLowerSegment 7859335424 7859368192 (785780722388191 / 100000)
      (392892030191683 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859335424 33 20 (455699 / 20000)
        (1139249 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859335424 7859368192 88652 _ _ (455699 / 20000) (356423 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859335424 7859368192 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859368192 :
    ThetaLowerSegment 7859368192 7859400960 (392892030191683 / 50000)
      (392893621721139 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859368192 33 20 (71203 / 3125)
        (2278499 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859368192 7859400960 88653 _ _ (71203 / 3125) (1782117 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859368192 7859400960 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859400960 :
    ThetaLowerSegment 7859400960 7859433728 (392893621721139 / 50000)
      (392895263377507 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859400960 33 20 (71203 / 3125)
        (2278499 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859400960 7859433728 88653 _ _ (71203 / 3125) (1782117 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859400960 7859433728 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859433728 :
    ThetaLowerSegment 7859433728 7859466496 (392895263377507 / 50000)
      (785793896652077 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859433728 33 20 (2278497 / 100000) (4557 / 200) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859433728 7859466496 88653 _ _ (2278497 / 100000) (891059 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859433728 7859466496 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859466496 :
    ThetaLowerSegment 7859466496 7859499264 (785793896652077 / 100000)
      (196449280181333 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859466496 33 20 (2278497 / 100000) (4557 / 200) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859466496 7859499264 88653 _ _ (2278497 / 100000) (891059 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859466496 7859499264 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859499264 :
    ThetaLowerSegment 7859499264 7859532032 (196449280181333 / 25000)
      (392900212272991 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859499264 33 20 (2278497 / 100000) (4557 / 200) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859499264 7859532032 88653 _ _ (2278497 / 100000) (891059 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859499264 7859532032 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859532032 :
    ThetaLowerSegment 7859532032 7859564800 (392900212272991 / 50000)
      (392901809500089 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859532032 33 20 (1139249 / 50000)
        (2278501 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859532032 7859564800 88654 _ _ (1139249 / 50000) (44553 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859532032 7859564800 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859564800 :
    ThetaLowerSegment 7859564800 7859597568 (392901809500089 / 50000)
      (392903472803629 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859564800 33 20 (1139249 / 50000)
        (2278501 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859564800 7859597568 88654 _ _ (1139249 / 50000) (44553 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859564800 7859597568 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859597568 :
    ThetaLowerSegment 7859597568 7859630336 (392903472803629 / 50000) (98226267507857 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859597568 33 20 (2278499 / 100000)
        (1139251 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859597568 7859630336 88654 _ _ (2278499 / 100000) (891061 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859597568 7859630336 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859630336 :
    ThetaLowerSegment 7859630336 7859663104 (98226267507857 / 12500) (157162721131967 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859630336 33 20 (2278499 / 100000)
        (1139251 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859630336 7859663104 88654 _ _ (2278499 / 100000) (891061 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859630336 7859663104 12 1521 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859663104 :
    ThetaLowerSegment 7859663104 7859695872 (157162721131967 / 20000)
      (392908421703457 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859663104 33 20 (2278499 / 100000)
        (1139251 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859663104 7859695872 88654 _ _ (2278499 / 100000) (891061 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859663104 7859695872 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859695872 :
    ThetaLowerSegment 7859695872 7859728640 (392908421703457 / 50000)
      (392910030324457 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859695872 33 20 (4557 / 200) (2278503 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859695872 7859728640 88654 _ _ (4557 / 200) (1782123 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859695872 7859728640 12 1412 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859728640 :
    ThetaLowerSegment 7859728640 7859761408 (392910030324457 / 50000)
      (392911671983707 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859728640 33 20 (4557 / 200) (2278503 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859728640 7859761408 88655 _ _ (4557 / 200) (1782123 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859728640 7859761408 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859761408 :
    ThetaLowerSegment 7859761408 7859794176 (392911671983707 / 50000)
      (785826613616349 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859761408 33 20 (2278501 / 100000)
        (284813 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859761408 7859794176 88655 _ _ (2278501 / 100000) (14257 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859761408 7859794176 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859794176 :
    ThetaLowerSegment 7859794176 7859826944 (785826613616349 / 100000)
      (392914953025147 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859794176 33 20 (2278501 / 100000)
        (284813 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859794176 7859826944 88655 _ _ (2278501 / 100000) (14257 / 800) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859794176 7859826944 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859826944 :
    ThetaLowerSegment 7859826944 7859859712 (392914953025147 / 50000)
      (196458301899923 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859826944 33 20 (1139251 / 50000)
        (455701 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859826944 7859859712 88655 _ _ (1139251 / 50000) (1782127 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859826944 7859859712 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859859712 :
    ThetaLowerSegment 7859859712 7859892480 (196458301899923 / 25000)
      (392918293309079 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859859712 33 20 (1139251 / 50000)
        (455701 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859859712 7859892480 88655 _ _ (1139251 / 50000) (1782127 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859859712 7859892480 12 1483 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859892480 :
    ThetaLowerSegment 7859892480 7859925248 (392918293309079 / 50000)
      (392919936109021 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859892480 33 20 (1139251 / 50000)
        (455701 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859892480 7859925248 88656 _ _ (1139251 / 50000) (1782127 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859892480 7859925248 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859925248 :
    ThetaLowerSegment 7859925248 7859958016 (392919936109021 / 50000)
      (785843260352003 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859925248 33 20 (2278503 / 100000)
        (1139253 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859925248 7859958016 88656 _ _ (2278503 / 100000) (111383 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859925248 7859958016 12 1487 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859958016 :
    ThetaLowerSegment 7859958016 7859990784 (785843260352003 / 100000)
      (785846450256203 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859958016 33 20 (2278503 / 100000)
        (1139253 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859958016 7859990784 88656 _ _ (2278503 / 100000) (111383 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859958016 7859990784 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7859990784 :
    ThetaLowerSegment 7859990784 7860023552 (785846450256203 / 100000)
      (785849688010387 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7859990784 33 20 (284813 / 12500)
        (2278507 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7859990784 7860023552 88656 _ _ (284813 / 12500) (178213 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7859990784 7860023552 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860023552 :
    ThetaLowerSegment 7860023552 7860056320 (785849688010387 / 100000)
      (157170594722631 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860023552 33 20 (284813 / 12500)
        (2278507 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860023552 7860056320 88656 _ _ (284813 / 12500) (178213 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860023552 7860056320 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860056320 :
    ThetaLowerSegment 7860056320 7860089088 (157170594722631 / 20000)
      (785856222759859 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860056320 33 20 (284813 / 12500)
        (2278507 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860056320 7860089088 88656 _ _ (284813 / 12500) (178213 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860056320 7860089088 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860089088 :
    ThetaLowerSegment 7860089088 7860121856 (785856222759859 / 100000)
      (392929741650257 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860089088 33 20 (455701 / 20000)
        (569627 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860089088 7860121856 88657 _ _ (455701 / 20000) (445533 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860089088 7860121856 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860121856 :
    ThetaLowerSegment 7860121856 7860154624 (392929741650257 / 50000)
      (196465683112161 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860121856 33 20 (455701 / 20000)
        (569627 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860121856 7860154624 88657 _ _ (455701 / 20000) (445533 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860121856 7860154624 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860154624 :
    ThetaLowerSegment 7860154624 7860187392 (196465683112161 / 25000)
      (392933069407557 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860154624 33 20 (1139253 / 50000)
        (2278509 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860154624 7860187392 88657 _ _ (1139253 / 50000) (1782133 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860154624 7860187392 12 1495 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860187392 :
    ThetaLowerSegment 7860187392 7860220160 (392933069407557 / 50000) (98233671501891 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860187392 33 20 (1139253 / 50000)
        (2278509 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860187392 7860220160 88657 _ _ (1139253 / 50000) (1782133 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860187392 7860220160 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860220160 :
    ThetaLowerSegment 7860220160 7860252928 (98233671501891 / 12500) (19646817238033 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860220160 33 20 (2278507 / 100000)
        (227851 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860220160 7860252928 88657 _ _ (2278507 / 100000) (356427 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860220160 7860252928 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860252928 :
    ThetaLowerSegment 7860252928 7860285696 (19646817238033 / 2500) (196468985807329 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860252928 33 20 (2278507 / 100000)
        (227851 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860252928 7860285696 88658 _ _ (2278507 / 100000) (356427 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860252928 7860285696 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860285696 :
    ThetaLowerSegment 7860285696 7860318464 (196468985807329 / 25000)
      (392939596190149 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860285696 33 20 (2278507 / 100000)
        (227851 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860285696 7860318464 88658 _ _ (2278507 / 100000) (356427 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860285696 7860318464 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860318464 :
    ThetaLowerSegment 7860318464 7860351232 (392939596190149 / 50000)
      (392941250386957 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860318464 33 20 (569627 / 25000)
        (2278511 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860318464 7860351232 88658 _ _ (569627 / 25000) (1782137 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860318464 7860351232 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860351232 :
    ThetaLowerSegment 7860351232 7860384000 (392941250386957 / 50000)
      (392942897748241 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860351232 33 20 (569627 / 25000)
        (2278511 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860351232 7860384000 88658 _ _ (569627 / 25000) (1782137 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860351232 7860384000 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860384000 :
    ThetaLowerSegment 7860384000 7860416768 (392942897748241 / 50000)
      (196472288504687 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860384000 33 20 (2278509 / 100000)
        (142407 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860384000 7860416768 88658 _ _ (2278509 / 100000) (891069 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860384000 7860416768 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860416768 :
    ThetaLowerSegment 7860416768 7860449536 (196472288504687 / 25000) (98236557801727 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860416768 33 20 (2278509 / 100000)
        (142407 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860416768 7860449536 88658 _ _ (2278509 / 100000) (891069 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860416768 7860449536 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860449536 :
    ThetaLowerSegment 7860449536 7860482304 (98236557801727 / 12500) (392947851226807 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860449536 33 20 (2278509 / 100000)
        (142407 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860449536 7860482304 88659 _ _ (2278509 / 100000) (891069 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860449536 7860482304 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860482304 :
    ThetaLowerSegment 7860482304 7860515072 (392947851226807 / 50000)
      (392949475804437 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860482304 33 20 (227851 / 10000)
        (2278513 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860482304 7860515072 88659 _ _ (227851 / 10000) (89107 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860482304 7860515072 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860515072 :
    ThetaLowerSegment 7860515072 7860547840 (392949475804437 / 50000)
      (392951075318457 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860515072 33 20 (227851 / 10000)
        (2278513 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860515072 7860547840 88659 _ _ (227851 / 10000) (89107 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860515072 7860547840 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860547840 :
    ThetaLowerSegment 7860547840 7860580608 (392951075318457 / 50000)
      (785905356501891 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860547840 33 20 (2278511 / 100000)
        (1139257 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860547840 7860580608 88659 _ _ (2278511 / 100000) (1782141 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860547840 7860580608 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860580608 :
    ThetaLowerSegment 7860580608 7860613376 (785905356501891 / 100000)
      (196477163376827 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860580608 33 20 (2278511 / 100000)
        (1139257 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860580608 7860613376 88659 _ _ (2278511 / 100000) (1782141 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860580608 7860613376 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860613376 :
    ThetaLowerSegment 7860613376 7860646144 (196477163376827 / 25000)
      (196477970539703 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860613376 33 20 (142407 / 6250)
        (455703 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860613376 7860646144 88660 _ _ (142407 / 6250) (1782143 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860613376 7860646144 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860646144 :
    ThetaLowerSegment 7860646144 7860678912 (196477970539703 / 25000)
      (196478779411463 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860646144 33 20 (142407 / 6250)
        (455703 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860646144 7860678912 88660 _ _ (142407 / 6250) (1782143 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860646144 7860678912 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860678912 :
    ThetaLowerSegment 7860678912 7860711680 (196478779411463 / 25000)
      (196479578599547 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860678912 33 20 (142407 / 6250)
        (455703 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860678912 7860711680 88660 _ _ (142407 / 6250) (1782143 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860678912 7860711680 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860711680 :
    ThetaLowerSegment 7860711680 7860744448 (196479578599547 / 25000)
      (785921620520551 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860711680 33 20 (2278513 / 100000)
        (569629 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860711680 7860744448 88660 _ _ (2278513 / 100000) (356429 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860711680 7860744448 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860744448 :
    ThetaLowerSegment 7860744448 7860777216 (785921620520551 / 100000)
      (98240608425197 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860744448 33 20 (2278513 / 100000)
        (569629 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860744448 7860777216 88660 _ _ (2278513 / 100000) (356429 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860744448 7860777216 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860777216 :
    ThetaLowerSegment 7860777216 7860809984 (98240608425197 / 12500) (392964123218919 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860777216 33 20 (1139257 / 50000)
        (2278517 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860777216 7860809984 88661 _ _ (1139257 / 50000) (891073 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860777216 7860809984 12 1483 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860809984 :
    ThetaLowerSegment 7860809984 7860842752 (392964123218919 / 50000) (78593152294097 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860809984 33 20 (1139257 / 50000)
        (2278517 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860809984 7860842752 88661 _ _ (1139257 / 50000) (891073 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860809984 7860842752 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860842752 :
    ThetaLowerSegment 7860842752 7860875520 (78593152294097 / 10000) (196483694734369 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860842752 33 20 (1139257 / 50000)
        (2278517 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860842752 7860875520 88661 _ _ (1139257 / 50000) (891073 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860842752 7860875520 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860875520 :
    ThetaLowerSegment 7860875520 7860908288 (196483694734369 / 25000)
      (392969050506173 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860875520 33 20 (455703 / 20000)
        (1139259 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860875520 7860908288 88661 _ _ (455703 / 20000) (445537 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860875520 7860908288 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860908288 :
    ThetaLowerSegment 7860908288 7860941056 (392969050506173 / 50000)
      (785941402580581 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860908288 33 20 (455703 / 20000)
        (1139259 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860908288 7860941056 88661 _ _ (455703 / 20000) (445537 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860908288 7860941056 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860941056 :
    ThetaLowerSegment 7860941056 7860973824 (785941402580581 / 100000)
      (785944663136977 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860941056 33 20 (569629 / 25000)
        (2278519 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860941056 7860973824 88661 _ _ (569629 / 25000) (35643 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860941056 7860973824 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7860973824 :
    ThetaLowerSegment 7860973824 7861006592 (785944663136977 / 100000)
      (785947953314081 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7860973824 33 20 (569629 / 25000)
        (2278519 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7860973824 7861006592 88662 _ _ (569629 / 25000) (35643 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7860973824 7861006592 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861006592 :
    ThetaLowerSegment 7861006592 7861039360 (785947953314081 / 100000) (39297562516409 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861006592 33 20 (2278517 / 100000)
        (56963 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861006592 7861039360 88662 _ _ (2278517 / 100000) (1782151 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861006592 7861039360 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861039360 :
    ThetaLowerSegment 7861039360 7861072128 (39297562516409 / 5000) (196488641962233 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861039360 33 20 (2278517 / 100000)
        (56963 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861039360 7861072128 88662 _ _ (2278517 / 100000) (1782151 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861039360 7861072128 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861072128 :
    ThetaLowerSegment 7861072128 7861104896 (196488641962233 / 25000)
      (785957819292691 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861072128 33 20 (2278517 / 100000)
        (56963 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861072128 7861104896 88662 _ _ (2278517 / 100000) (1782151 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861072128 7861104896 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861104896 :
    ThetaLowerSegment 7861104896 7861137664 (785957819292691 / 100000)
      (157192205489207 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861104896 33 20 (1139259 / 50000)
        (2278521 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861104896 7861137664 88662 _ _ (1139259 / 50000) (1782153 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861104896 7861137664 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861137664 :
    ThetaLowerSegment 7861137664 7861170432 (157192205489207 / 20000)
      (785964260663077 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861137664 33 20 (1139259 / 50000)
        (2278521 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861137664 7861170432 88663 _ _ (1139259 / 50000) (1782153 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861137664 7861170432 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861170432 :
    ThetaLowerSegment 7861170432 7861203200 (785964260663077 / 100000) (49122968652411 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861170432 33 20 (2278519 / 100000)
        (1139261 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861170432 7861203200 88663 _ _ (2278519 / 100000) (356431 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861170432 7861203200 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861203200 :
    ThetaLowerSegment 7861203200 7861235968 (49122968652411 / 6250) (785970754442227 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861203200 33 20 (2278519 / 100000)
        (1139261 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861203200 7861235968 88663 _ _ (2278519 / 100000) (356431 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861203200 7861235968 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861235968 :
    ThetaLowerSegment 7861235968 7861268736 (785970754442227 / 100000)
      (785974122093309 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861235968 33 20 (2278519 / 100000)
        (1139261 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861235968 7861268736 88663 _ _ (2278519 / 100000) (356431 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861235968 7861268736 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861268736 :
    ThetaLowerSegment 7861268736 7861301504 (785974122093309 / 100000)
      (785977510252549 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861268736 33 20 (56963 / 2500)
        (2278523 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861268736 7861301504 88663 _ _ (56963 / 2500) (445539 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861268736 7861301504 12 1487 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861301504 :
    ThetaLowerSegment 7861301504 7861334272 (785977510252549 / 100000)
      (785980804992469 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861301504 33 20 (56963 / 2500)
        (2278523 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861301504 7861334272 88663 _ _ (56963 / 2500) (445539 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861301504 7861334272 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861334272 :
    ThetaLowerSegment 7861334272 7861367040 (785980804992469 / 100000)
      (785984072391583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861334272 33 20 (2278521 / 100000)
        (569631 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861334272 7861367040 88664 _ _ (2278521 / 100000) (891079 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861334272 7861367040 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861367040 :
    ThetaLowerSegment 7861367040 7861399808 (785984072391583 / 100000) (15719746476821 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861367040 33 20 (2278521 / 100000)
        (569631 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861367040 7861399808 88664 _ _ (2278521 / 100000) (891079 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861367040 7861399808 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861399808 :
    ThetaLowerSegment 7861399808 7861432576 (15719746476821 / 2000) (196497663190423 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861399808 33 20 (1139261 / 50000)
        (91141 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861399808 7861432576 88664 _ _ (1139261 / 50000) (22277 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861399808 7861432576 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861432576 :
    ThetaLowerSegment 7861432576 7861465344 (196497663190423 / 25000)
      (392996952106293 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861432576 33 20 (1139261 / 50000)
        (91141 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861432576 7861465344 88664 _ _ (1139261 / 50000) (22277 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861432576 7861465344 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861465344 :
    ThetaLowerSegment 7861465344 7861498112 (392996952106293 / 50000) (98249651293501 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861465344 33 20 (1139261 / 50000)
        (91141 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861465344 7861498112 88664 _ _ (1139261 / 50000) (22277 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861465344 7861498112 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861498112 :
    ThetaLowerSegment 7861498112 7861530880 (98249651293501 / 12500) (196500120576759 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861498112 33 20 (2278523 / 100000)
        (1139263 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861498112 7861530880 88665 _ _ (2278523 / 100000) (1782161 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861498112 7861530880 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861530880 :
    ThetaLowerSegment 7861530880 7861563648 (196500120576759 / 25000)
      (786003592490931 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861530880 33 20 (2278523 / 100000)
        (1139263 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861530880 7861563648 88665 _ _ (2278523 / 100000) (1782161 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861530880 7861563648 12 1365 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861563648 :
    ThetaLowerSegment 7861563648 7861596416 (786003592490931 / 100000) (31440271843827 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861563648 33 20 (569631 / 25000)
        (2278527 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861563648 7861596416 88665 _ _ (569631 / 25000) (1782163 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861563648 7861596416 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861596416 :
    ThetaLowerSegment 7861596416 7861629184 (31440271843827 / 4000) (786010243502487 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861596416 33 20 (569631 / 25000)
        (2278527 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861596416 7861629184 88665 _ _ (569631 / 25000) (1782163 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861596416 7861629184 12 1513 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861629184 :
    ThetaLowerSegment 7861629184 7861661952 (786010243502487 / 100000)
      (786013583818671 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861629184 33 20 (569631 / 25000)
        (2278527 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861629184 7861661952 88665 _ _ (569631 / 25000) (1782163 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861629184 7861661952 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861661952 :
    ThetaLowerSegment 7861661952 7861694720 (786013583818671 / 100000)
      (786016915022221 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861661952 33 20 (91141 / 4000) (71204 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861661952 7861694720 88666 _ _ (91141 / 4000) (356433 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861661952 7861694720 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861694720 :
    ThetaLowerSegment 7861694720 7861727488 (786016915022221 / 100000)
      (786020104957221 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861694720 33 20 (91141 / 4000) (71204 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861694720 7861727488 88666 _ _ (91141 / 4000) (356433 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861694720 7861727488 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861727488 :
    ThetaLowerSegment 7861727488 7861760256 (786020104957221 / 100000)
      (786023461226019 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861727488 33 20 (1139263 / 50000)
        (2278529 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861727488 7861760256 88666 _ _ (1139263 / 50000) (891083 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861727488 7861760256 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861760256 :
    ThetaLowerSegment 7861760256 7861793024 (786023461226019 / 100000)
      (786026635212737 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861760256 33 20 (1139263 / 50000)
        (2278529 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861760256 7861793024 88666 _ _ (1139263 / 50000) (891083 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861760256 7861793024 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861793024 :
    ThetaLowerSegment 7861793024 7861825792 (786026635212737 / 100000)
      (786029929962779 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861793024 33 20 (2278527 / 100000)
        (227853 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861793024 7861825792 88666 _ _ (2278527 / 100000) (222771 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861793024 7861825792 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861825792 :
    ThetaLowerSegment 7861825792 7861858560 (786029929962779 / 100000) (31441333727849 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861825792 33 20 (2278527 / 100000)
        (227853 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861825792 7861858560 88666 _ _ (2278527 / 100000) (222771 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861825792 7861858560 12 1498 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861858560 :
    ThetaLowerSegment 7861858560 7861891328 (31441333727849 / 4000) (393018269984803 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861858560 33 20 (2278527 / 100000)
        (227853 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861858560 7861891328 88667 _ _ (2278527 / 100000) (222771 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861858560 7861891328 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861891328 :
    ThetaLowerSegment 7861891328 7861924096 (393018269984803 / 50000) (78603981649287 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861891328 33 20 (71204 / 3125)
        (2278531 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861891328 7861924096 88667 _ _ (71204 / 3125) (178217 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861891328 7861924096 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861924096 :
    ThetaLowerSegment 7861924096 7861956864 (78603981649287 / 10000) (393021545368803 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861924096 33 20 (71204 / 3125)
        (2278531 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861924096 7861956864 88667 _ _ (71204 / 3125) (178217 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861924096 7861956864 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861956864 :
    ThetaLowerSegment 7861956864 7861989632 (393021545368803 / 50000)
      (786046369540837 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861956864 33 20 (2278529 / 100000)
        (569633 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861956864 7861989632 88667 _ _ (2278529 / 100000) (1782171 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861956864 7861989632 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7861989632 :
    ThetaLowerSegment 7861989632 7862022400 (786046369540837 / 100000)
      (98256207182273 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7861989632 33 20 (2278529 / 100000)
        (569633 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7861989632 7862022400 88667 _ _ (2278529 / 100000) (1782171 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7861989632 7862022400 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862022400 :
    ThetaLowerSegment 7862022400 7862055168 (98256207182273 / 12500) (393026448763211 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862022400 33 20 (2278529 / 100000)
        (569633 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862022400 7862055168 88668 _ _ (2278529 / 100000) (1782171 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862022400 7862055168 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862055168 :
    ThetaLowerSegment 7862055168 7862087936 (393026448763211 / 50000)
      (196514066868073 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862055168 33 20 (227853 / 10000)
        (2278533 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862055168 7862087936 88668 _ _ (227853 / 10000) (1782173 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862055168 7862087936 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862087936 :
    ThetaLowerSegment 7862087936 7862120704 (196514066868073 / 25000) (49128727196227 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862087936 33 20 (227853 / 10000)
        (2278533 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862087936 7862120704 88668 _ _ (227853 / 10000) (1782173 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862087936 7862120704 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862120704 :
    ThetaLowerSegment 7862120704 7862153472 (49128727196227 / 6250) (98257862249503 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862120704 33 20 (2278531 / 100000)
        (1139267 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862120704 7862153472 88668 _ _ (2278531 / 100000) (71287 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862120704 7862153472 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862153472 :
    ThetaLowerSegment 7862153472 7862186240 (98257862249503 / 12500)
      (786066240601001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862153472 33 20 (2278531 / 100000)
        (1139267 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862153472 7862186240 88668 _ _ (2278531 / 100000) (71287 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862153472 7862186240 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862186240 :
    ThetaLowerSegment 7862186240 7862219008 (786066240601001 / 100000)
      (786069489787633 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862186240 33 20 (569633 / 25000)
        (455707 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862186240 7862219008 88668 _ _ (569633 / 25000) (55693 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862186240 7862219008 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862219008 :
    ThetaLowerSegment 7862219008 7862251776 (786069489787633 / 100000)
      (786072752645457 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862219008 33 20 (569633 / 25000)
        (455707 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862219008 7862251776 88669 _ _ (569633 / 25000) (55693 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862219008 7862251776 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862251776 :
    ThetaLowerSegment 7862251776 7862284544 (786072752645457 / 100000)
      (157215206290601 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862251776 33 20 (569633 / 25000)
        (455707 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862251776 7862284544 88669 _ _ (569633 / 25000) (55693 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862251776 7862284544 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862284544 :
    ThetaLowerSegment 7862284544 7862317312 (157215206290601 / 20000)
      (196519816172833 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862284544 33 20 (2278533 / 100000)
        (284817 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862284544 7862317312 88669 _ _ (2278533 / 100000) (891089 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862284544 7862317312 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862317312 :
    ThetaLowerSegment 7862317312 7862350080 (196519816172833 / 25000) (9826031708309 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862317312 33 20 (2278533 / 100000)
        (284817 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862317312 7862350080 88669 _ _ (2278533 / 100000) (891089 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862317312 7862350080 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862350080 :
    ThetaLowerSegment 7862350080 7862382848 (9826031708309 / 1250) (78608589750237 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862350080 33 20 (1139267 / 50000)
        (2278537 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862350080 7862382848 88669 _ _ (1139267 / 50000) (1782179 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862350080 7862382848 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862382848 :
    ThetaLowerSegment 7862382848 7862415616 (78608589750237 / 10000) (393044596131267 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862382848 33 20 (1139267 / 50000)
        (2278537 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862382848 7862415616 88670 _ _ (1139267 / 50000) (1782179 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862382848 7862415616 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862415616 :
    ThetaLowerSegment 7862415616 7862448384 (393044596131267 / 50000)
      (196523114350439 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862415616 33 20 (1139267 / 50000)
        (2278537 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862415616 7862448384 88670 _ _ (1139267 / 50000) (1782179 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862415616 7862448384 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862448384 :
    ThetaLowerSegment 7862448384 7862481152 (196523114350439 / 25000)
      (786095681528781 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862448384 33 20 (455707 / 20000)
        (1139269 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862448384 7862481152 88670 _ _ (455707 / 20000) (1782181 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862448384 7862481152 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862481152 :
    ThetaLowerSegment 7862481152 7862513920 (786095681528781 / 100000)
      (786098985404531 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862481152 33 20 (455707 / 20000)
        (1139269 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862481152 7862513920 88670 _ _ (455707 / 20000) (1782181 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862481152 7862513920 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862513920 :
    ThetaLowerSegment 7862513920 7862546688 (786098985404531 / 100000)
      (786102234596867 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862513920 33 20 (284817 / 12500)
        (2278539 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862513920 7862546688 88670 _ _ (284817 / 12500) (1782183 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862513920 7862546688 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862546688 :
    ThetaLowerSegment 7862546688 7862579456 (786102234596867 / 100000)
      (786105536195531 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862546688 33 20 (284817 / 12500)
        (2278539 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862546688 7862579456 88671 _ _ (284817 / 12500) (1782183 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862546688 7862579456 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862579456 :
    ThetaLowerSegment 7862579456 7862612224 (786105536195531 / 100000)
      (98263608142261 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862579456 33 20 (2278537 / 100000)
        (113927 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862579456 7862612224 88671 _ _ (2278537 / 100000) (222773 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862579456 7862612224 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862612224 :
    ThetaLowerSegment 7862612224 7862644992 (98263608142261 / 12500) (157222425144907 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862612224 33 20 (2278537 / 100000)
        (113927 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862612224 7862644992 88671 _ _ (2278537 / 100000) (222773 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862612224 7862644992 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862644992 :
    ThetaLowerSegment 7862644992 7862677760 (157222425144907 / 20000)
      (786115507073443 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862644992 33 20 (2278537 / 100000)
        (113927 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862644992 7862677760 88671 _ _ (2278537 / 100000) (222773 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862644992 7862677760 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862677760 :
    ThetaLowerSegment 7862677760 7862710528 (786115507073443 / 100000)
      (786118760825707 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862677760 33 20 (1139269 / 50000)
        (2278541 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862677760 7862710528 88671 _ _ (1139269 / 50000) (891093 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862677760 7862710528 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862710528 :
    ThetaLowerSegment 7862710528 7862743296 (786118760825707 / 100000)
      (786121969007211 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862710528 33 20 (1139269 / 50000)
        (2278541 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862710528 7862743296 88671 _ _ (1139269 / 50000) (891093 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862710528 7862743296 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862743296 :
    ThetaLowerSegment 7862743296 7862776064 (786121969007211 / 100000)
      (786125236432137 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862743296 33 20 (2278539 / 100000)
        (1139271 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862743296 7862776064 88672 _ _ (2278539 / 100000) (445547 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862743296 7862776064 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862776064 :
    ThetaLowerSegment 7862776064 7862808832 (786125236432137 / 100000)
      (786128435500893 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862776064 33 20 (2278539 / 100000)
        (1139271 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862776064 7862808832 88672 _ _ (2278539 / 100000) (445547 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862776064 7862808832 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862808832 :
    ThetaLowerSegment 7862808832 7862841600 (786128435500893 / 100000)
      (393065870830491 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862808832 33 20 (2278539 / 100000)
        (1139271 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862808832 7862841600 88672 _ _ (2278539 / 100000) (445547 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862808832 7862841600 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862841600 :
    ThetaLowerSegment 7862841600 7862874368 (393065870830491 / 50000)
      (393067529607611 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862841600 33 20 (113927 / 5000)
        (2278543 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862841600 7862874368 88672 _ _ (113927 / 5000) (1782189 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862841600 7862874368 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862874368 :
    ThetaLowerSegment 7862874368 7862907136 (393067529607611 / 50000)
      (393069139396121 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862874368 33 20 (113927 / 5000)
        (2278543 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862874368 7862907136 88672 _ _ (113927 / 5000) (1782189 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862874368 7862907136 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862907136 :
    ThetaLowerSegment 7862907136 7862939904 (393069139396121 / 50000)
      (786141666982709 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862907136 33 20 (2278541 / 100000)
        (142409 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862907136 7862939904 88673 _ _ (2278541 / 100000) (1782191 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862907136 7862939904 12 1487 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862939904 :
    ThetaLowerSegment 7862939904 7862972672 (786141666982709 / 100000) (49134055694889 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862939904 33 20 (2278541 / 100000)
        (142409 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862939904 7862972672 88673 _ _ (2278541 / 100000) (1782191 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862939904 7862972672 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7862972672 :
    ThetaLowerSegment 7862972672 7863005440 (49134055694889 / 6250) (196537028244153 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7862972672 33 20 (1139271 / 50000)
        (455709 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7862972672 7863005440 88673 _ _ (1139271 / 50000) (1782193 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7862972672 7863005440 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863005440 :
    ThetaLowerSegment 7863005440 7863038208 (196537028244153 / 25000)
      (393075727798863 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863005440 33 20 (1139271 / 50000)
        (455709 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863005440 7863038208 88673 _ _ (1139271 / 50000) (1782193 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863005440 7863038208 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863038208 :
    ThetaLowerSegment 7863038208 7863070976 (393075727798863 / 50000)
      (196538666515851 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863038208 33 20 (1139271 / 50000)
        (455709 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863038208 7863070976 88673 _ _ (1139271 / 50000) (1782193 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863038208 7863070976 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863070976 :
    ThetaLowerSegment 7863070976 7863103744 (196538666515851 / 25000)
      (786157922101351 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863070976 33 20 (2278543 / 100000)
        (1139273 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863070976 7863103744 88673 _ _ (2278543 / 100000) (891097 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863070976 7863103744 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863103744 :
    ThetaLowerSegment 7863103744 7863136512 (786157922101351 / 100000) (31446441565927 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863103744 33 20 (2278543 / 100000)
        (1139273 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863103744 7863136512 88674 _ _ (2278543 / 100000) (891097 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863103744 7863136512 12 1368 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863136512 :
    ThetaLowerSegment 7863136512 7863169280 (31446441565927 / 4000) (786164279237743 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863136512 33 20 (142409 / 6250)
        (2278547 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863136512 7863169280 88674 _ _ (142409 / 6250) (445549 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863136512 7863169280 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863169280 :
    ThetaLowerSegment 7863169280 7863202048 (786164279237743 / 100000)
      (157233504321171 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863169280 33 20 (142409 / 6250)
        (2278547 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863169280 7863202048 88674 _ _ (142409 / 6250) (445549 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863169280 7863202048 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863202048 :
    ThetaLowerSegment 7863202048 7863234816 (157233504321171 / 20000)
      (786170818659023 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863202048 33 20 (142409 / 6250)
        (2278547 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863202048 7863234816 88674 _ _ (142409 / 6250) (445549 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863202048 7863234816 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863234816 :
    ThetaLowerSegment 7863234816 7863267584 (786170818659023 / 100000)
      (393087012285919 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863234816 33 20 (455709 / 20000)
        (569637 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863234816 7863267584 88674 _ _ (455709 / 20000) (891099 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863234816 7863267584 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863267584 :
    ThetaLowerSegment 7863267584 7863300352 (393087012285919 / 50000) (98272161500671 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863267584 33 20 (455709 / 20000)
        (569637 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863267584 7863300352 88675 _ _ (455709 / 20000) (891099 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863267584 7863300352 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863300352 :
    ThetaLowerSegment 7863300352 7863333120 (98272161500671 / 12500) (78618065741781 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863300352 33 20 (1139273 / 50000)
        (2278549 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863300352 7863333120 88675 _ _ (1139273 / 50000) (1782199 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863300352 7863333120 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863333120 :
    ThetaLowerSegment 7863333120 7863365888 (78618065741781 / 10000) (393091962426387 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863333120 33 20 (1139273 / 50000)
        (2278549 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863333120 7863365888 88675 _ _ (1139273 / 50000) (1782199 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863333120 7863365888 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863365888 :
    ThetaLowerSegment 7863365888 7863398656 (393091962426387 / 50000) (49136702366257 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863365888 33 20 (2278547 / 100000)
        (45571 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863365888 7863398656 88675 _ _ (2278547 / 100000) (1782201 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863365888 7863398656 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863398656 :
    ThetaLowerSegment 7863398656 7863431424 (49136702366257 / 6250) (786190557703091 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863398656 33 20 (2278547 / 100000)
        (45571 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863398656 7863431424 88675 _ _ (2278547 / 100000) (1782201 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863398656 7863431424 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863431424 :
    ThetaLowerSegment 7863431424 7863464192 (786190557703091 / 100000)
      (786193907167181 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863431424 33 20 (2278547 / 100000)
        (45571 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863431424 7863464192 88675 _ _ (2278547 / 100000) (1782201 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863431424 7863464192 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863464192 :
    ThetaLowerSegment 7863464192 7863496960 (786193907167181 / 100000)
      (786197245240001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863464192 33 20 (569637 / 25000)
        (2278551 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863464192 7863496960 88676 _ _ (569637 / 25000) (1782203 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863464192 7863496960 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863496960 :
    ThetaLowerSegment 7863496960 7863529728 (786197245240001 / 100000)
      (786200526349121 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863496960 33 20 (569637 / 25000)
        (2278551 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863496960 7863529728 88676 _ _ (569637 / 25000) (1782203 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863496960 7863529728 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863529728 :
    ThetaLowerSegment 7863529728 7863562496 (786200526349121 / 100000)
      (393101841069743 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863529728 33 20 (2278549 / 100000)
        (284819 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863529728 7863562496 88676 _ _ (2278549 / 100000) (445551 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863529728 7863562496 12 1385 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863562496 :
    ThetaLowerSegment 7863562496 7863595264 (393101841069743 / 50000) (4913793890577 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863562496 33 20 (2278549 / 100000)
        (284819 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863562496 7863595264 88676 _ _ (2278549 / 100000) (445551 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863562496 7863595264 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863595264 :
    ThetaLowerSegment 7863595264 7863628032 (4913793890577 / 625) (393105126737401 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863595264 33 20 (2278549 / 100000)
        (284819 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863595264 7863628032 88676 _ _ (2278549 / 100000) (445551 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863595264 7863628032 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863628032 :
    ThetaLowerSegment 7863628032 7863660800 (393105126737401 / 50000)
      (393106758179201 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863628032 33 20 (45571 / 2000)
        (2278553 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863628032 7863660800 88677 _ _ (45571 / 2000) (891103 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863628032 7863660800 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863660800 :
    ThetaLowerSegment 7863660800 7863693568 (393106758179201 / 50000)
      (393108369114051 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863660800 33 20 (45571 / 2000)
        (2278553 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863660800 7863693568 88677 _ _ (45571 / 2000) (891103 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863660800 7863693568 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863693568 :
    ThetaLowerSegment 7863693568 7863726336 (393108369114051 / 50000)
      (786220017062991 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863693568 33 20 (2278551 / 100000)
        (1139277 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863693568 7863726336 88677 _ _ (2278551 / 100000) (55694 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863693568 7863726336 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863726336 :
    ThetaLowerSegment 7863726336 7863759104 (786220017062991 / 100000)
      (786223384761369 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863726336 33 20 (2278551 / 100000)
        (1139277 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863726336 7863759104 88677 _ _ (2278551 / 100000) (55694 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863726336 7863759104 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863759104 :
    ThetaLowerSegment 7863759104 7863791872 (786223384761369 / 100000)
      (786226590684033 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863759104 33 20 (284819 / 12500)
        (455711 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863759104 7863791872 88677 _ _ (284819 / 12500) (1782209 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863759104 7863791872 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863791872 :
    ThetaLowerSegment 7863791872 7863824640 (786226590684033 / 100000)
      (157245983929701 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863791872 33 20 (284819 / 12500)
        (455711 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863791872 7863824640 88678 _ _ (284819 / 12500) (1782209 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863791872 7863824640 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863824640 :
    ThetaLowerSegment 7863824640 7863857408 (157245983929701 / 20000)
      (786233152913793 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863824640 33 20 (284819 / 12500)
        (455711 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863824640 7863857408 88678 _ _ (284819 / 12500) (1782209 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863824640 7863857408 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863857408 :
    ThetaLowerSegment 7863857408 7863890176 (786233152913793 / 100000)
      (196559123887761 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863857408 33 20 (2278553 / 100000)
        (569639 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863857408 7863890176 88678 _ _ (2278553 / 100000) (1782211 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863857408 7863890176 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863890176 :
    ThetaLowerSegment 7863890176 7863922944 (196559123887761 / 25000)
      (786239856416719 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863890176 33 20 (2278553 / 100000)
        (569639 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863890176 7863922944 88678 _ _ (2278553 / 100000) (1782211 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863890176 7863922944 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863922944 :
    ThetaLowerSegment 7863922944 7863955712 (786239856416719 / 100000)
      (786243242347963 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863922944 33 20 (1139277 / 50000)
        (2278557 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863922944 7863955712 88678 _ _ (1139277 / 50000) (445553 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863922944 7863955712 12 1486 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863955712 :
    ThetaLowerSegment 7863955712 7863988480 (786243242347963 / 100000)
      (786246411816577 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863955712 33 20 (1139277 / 50000)
        (2278557 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863955712 7863988480 88678 _ _ (1139277 / 50000) (445553 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863955712 7863988480 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7863988480 :
    ThetaLowerSegment 7863988480 7864021248 (786246411816577 / 100000)
      (786249768126619 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7863988480 33 20 (1139277 / 50000)
        (2278557 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7863988480 7864021248 88679 _ _ (1139277 / 50000) (445553 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7863988480 7864021248 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864021248 :
    ThetaLowerSegment 7864021248 7864054016 (786249768126619 / 100000)
      (786252962660729 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864021248 33 20 (455711 / 20000)
        (1139279 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864021248 7864054016 88679 _ _ (455711 / 20000) (891107 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864021248 7864054016 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864054016 :
    ThetaLowerSegment 7864054016 7864086784 (786252962660729 / 100000)
      (393128129864907 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864054016 33 20 (455711 / 20000)
        (1139279 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864054016 7864086784 88679 _ _ (455711 / 20000) (891107 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864054016 7864086784 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864086784 :
    ThetaLowerSegment 7864086784 7864119552 (393128129864907 / 50000)
      (393129772703783 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864086784 33 20 (569639 / 25000)
        (2278559 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864086784 7864119552 88679 _ _ (569639 / 25000) (222777 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864086784 7864119552 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864119552 :
    ThetaLowerSegment 7864119552 7864152320 (393129772703783 / 50000) (78626290399911 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864119552 33 20 (569639 / 25000)
        (2278559 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864119552 7864152320 88679 _ _ (569639 / 25000) (222777 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864119552 7864152320 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864152320 :
    ThetaLowerSegment 7864152320 7864185088 (78626290399911 / 10000)
      (786266246642229 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864152320 33 20 (2278557 / 100000)
        (14241 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864152320 7864185088 88680 _ _ (2278557 / 100000) (1782217 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864152320 7864185088 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864185088 :
    ThetaLowerSegment 7864185088 7864217856 (786266246642229 / 100000)
      (196567388207109 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864185088 33 20 (2278557 / 100000)
        (14241 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864185088 7864217856 88680 _ _ (2278557 / 100000) (1782217 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864185088 7864217856 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864217856 :
    ThetaLowerSegment 7864217856 7864250624 (196567388207109 / 25000)
      (786272813443503 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864217856 33 20 (2278557 / 100000)
        (14241 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864217856 7864250624 88680 _ _ (2278557 / 100000) (1782217 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864217856 7864250624 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864250624 :
    ThetaLowerSegment 7864250624 7864283392 (786272813443503 / 100000)
      (786276062667211 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864250624 33 20 (1139279 / 50000)
        (2278561 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864250624 7864283392 88680 _ _ (1139279 / 50000) (1782219 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864250624 7864283392 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864283392 :
    ThetaLowerSegment 7864283392 7864316160 (786276062667211 / 100000)
      (786279387083333 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864283392 33 20 (1139279 / 50000)
        (2278561 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864283392 7864316160 88680 _ _ (1139279 / 50000) (1782219 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864283392 7864316160 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864316160 :
    ThetaLowerSegment 7864316160 7864348928 (786279387083333 / 100000)
      (393141369421811 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864316160 33 20 (2278559 / 100000)
        (1139281 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864316160 7864348928 88680 _ _ (2278559 / 100000) (1782221 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864316160 7864348928 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864348928 :
    ThetaLowerSegment 7864348928 7864381696 (393141369421811 / 50000) (7862860245257 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864348928 33 20 (2278559 / 100000)
        (1139281 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864348928 7864381696 88681 _ _ (2278559 / 100000) (1782221 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864348928 7864381696 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864381696 :
    ThetaLowerSegment 7864381696 7864414464 (7862860245257 / 1000) (393144668775243 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864381696 33 20 (2278559 / 100000)
        (1139281 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864381696 7864414464 88681 _ _ (2278559 / 100000) (1782221 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864381696 7864414464 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864414464 :
    ThetaLowerSegment 7864414464 7864447232 (393144668775243 / 50000)
      (393146253513723 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864414464 33 20 (14241 / 625)
        (2278563 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864414464 7864447232 88681 _ _ (14241 / 625) (891111 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864414464 7864447232 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864447232 :
    ThetaLowerSegment 7864447232 7864480000 (393146253513723 / 50000)
      (393147858759243 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864447232 33 20 (14241 / 625)
        (2278563 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864447232 7864480000 88681 _ _ (14241 / 625) (891111 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864447232 7864480000 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864480000 :
    ThetaLowerSegment 7864480000 7864512768 (393147858759243 / 50000)
      (786299078395961 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864480000 33 20 (2278561 / 100000)
        (569641 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864480000 7864512768 88681 _ _ (2278561 / 100000) (111389 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864480000 7864512768 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864512768 :
    ThetaLowerSegment 7864512768 7864545536 (786299078395961 / 100000)
      (196575582475627 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864512768 33 20 (2278561 / 100000)
        (569641 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864512768 7864545536 88682 _ _ (2278561 / 100000) (111389 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864512768 7864545536 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864545536 :
    ThetaLowerSegment 7864545536 7864578304 (196575582475627 / 25000)
      (393152868176349 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864545536 33 20 (1139281 / 50000)
        (455713 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864545536 7864578304 88682 _ _ (1139281 / 50000) (891113 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864545536 7864578304 12 1495 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864578304 :
    ThetaLowerSegment 7864578304 7864611072 (393152868176349 / 50000)
      (393154490512493 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864578304 33 20 (1139281 / 50000)
        (455713 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864578304 7864611072 88682 _ _ (1139281 / 50000) (891113 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864578304 7864611072 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864611072 :
    ThetaLowerSegment 7864611072 7864643840 (393154490512493 / 50000)
      (393156101455827 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864611072 33 20 (1139281 / 50000)
        (455713 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864611072 7864643840 88682 _ _ (1139281 / 50000) (891113 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864611072 7864643840 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864643840 :
    ThetaLowerSegment 7864643840 7864676608 (393156101455827 / 50000)
      (786315513663693 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864643840 33 20 (2278563 / 100000)
        (1139283 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864643840 7864676608 88682 _ _ (2278563 / 100000) (1782227 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864643840 7864676608 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864676608 :
    ThetaLowerSegment 7864676608 7864709376 (786315513663693 / 100000)
      (786318822137169 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864676608 33 20 (2278563 / 100000)
        (1139283 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864676608 7864709376 88683 _ _ (2278563 / 100000) (1782227 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864676608 7864709376 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864709376 :
    ThetaLowerSegment 7864709376 7864742144 (786318822137169 / 100000)
      (786322130612097 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864709376 33 20 (569641 / 25000)
        (2278567 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864709376 7864742144 88683 _ _ (569641 / 25000) (1782229 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864709376 7864742144 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864742144 :
    ThetaLowerSegment 7864742144 7864774912 (786322130612097 / 100000)
      (786325521115329 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864742144 33 20 (569641 / 25000)
        (2278567 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864742144 7864774912 88683 _ _ (569641 / 25000) (1782229 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864742144 7864774912 12 1488 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864774912 :
    ThetaLowerSegment 7864774912 7864807680 (786325521115329 / 100000)
      (157265744043837 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864774912 33 20 (569641 / 25000)
        (2278567 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864774912 7864807680 88683 _ _ (569641 / 25000) (1782229 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864774912 7864807680 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864807680 :
    ThetaLowerSegment 7864807680 7864840448 (157265744043837 / 20000) (39316600865137 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864807680 33 20 (455713 / 20000)
        (284821 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864807680 7864840448 88683 _ _ (455713 / 20000) (1782231 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864807680 7864840448 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864840448 :
    ThetaLowerSegment 7864840448 7864873216 (39316600865137 / 5000) (9829191572239 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864840448 33 20 (455713 / 20000)
        (284821 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864840448 7864873216 88683 _ _ (455713 / 20000) (1782231 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864840448 7864873216 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864873216 :
    ThetaLowerSegment 7864873216 7864905984 (9829191572239 / 1250) (78633873223529 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864873216 33 20 (1139283 / 50000)
        (2278569 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864873216 7864905984 88684 _ _ (1139283 / 50000) (222779 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864873216 7864905984 12 1495 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864905984 :
    ThetaLowerSegment 7864905984 7864938752 (78633873223529 / 10000) (24573184571179 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864905984 33 20 (1139283 / 50000)
        (2278569 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864905984 7864938752 88684 _ _ (1139283 / 50000) (222779 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864905984 7864938752 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864938752 :
    ThetaLowerSegment 7864938752 7864971520 (24573184571179 / 3125) (786345185135641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864938752 33 20 (2278567 / 100000)
        (227857 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864938752 7864971520 88684 _ _ (2278567 / 100000) (891117 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864938752 7864971520 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7864971520 :
    ThetaLowerSegment 7864971520 7865004288 (786345185135641 / 100000)
      (786348397915111 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7864971520 33 20 (2278567 / 100000)
        (227857 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7864971520 7865004288 88684 _ _ (2278567 / 100000) (891117 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7864971520 7865004288 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865004288 :
    ThetaLowerSegment 7865004288 7865037056 (786348397915111 / 100000)
      (196587930586091 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865004288 33 20 (2278567 / 100000)
        (227857 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865004288 7865037056 88684 _ _ (2278567 / 100000) (891117 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865004288 7865037056 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865037056 :
    ThetaLowerSegment 7865037056 7865069824 (196587930586091 / 25000)
      (196588753149139 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865037056 33 20 (284821 / 12500)
        (2278571 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865037056 7865069824 88685 _ _ (284821 / 12500) (445559 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865037056 7865069824 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865069824 :
    ThetaLowerSegment 7865069824 7865102592 (196588753149139 / 25000)
      (196589559192569 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865069824 33 20 (284821 / 12500)
        (2278571 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865069824 7865102592 88685 _ _ (284821 / 12500) (445559 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865069824 7865102592 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865102592 :
    ThetaLowerSegment 7865102592 7865135360 (196589559192569 / 25000)
      (786361524745343 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865102592 33 20 (2278569 / 100000)
        (569643 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865102592 7865135360 88685 _ _ (2278569 / 100000) (1782237 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865102592 7865135360 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865135360 :
    ThetaLowerSegment 7865135360 7865168128 (786361524745343 / 100000)
      (786364842341807 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865135360 33 20 (2278569 / 100000)
        (569643 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865135360 7865168128 88685 _ _ (2278569 / 100000) (1782237 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865135360 7865168128 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865168128 :
    ThetaLowerSegment 7865168128 7865200896 (786364842341807 / 100000)
      (786368141709719 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865168128 33 20 (2278569 / 100000)
        (569643 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865168128 7865200896 88685 _ _ (2278569 / 100000) (1782237 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865168128 7865200896 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865200896 :
    ThetaLowerSegment 7865200896 7865233664 (786368141709719 / 100000)
      (786371452471929 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865200896 33 20 (227857 / 10000)
        (2278573 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865200896 7865233664 88685 _ _ (227857 / 10000) (1782239 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865200896 7865233664 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865233664 :
    ThetaLowerSegment 7865233664 7865266432 (786371452471929 / 100000)
      (786374662977059 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865233664 33 20 (227857 / 10000)
        (2278573 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865233664 7865266432 88686 _ _ (227857 / 10000) (1782239 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865233664 7865266432 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865266432 :
    ThetaLowerSegment 7865266432 7865299200 (786374662977059 / 100000)
      (786377953233583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865266432 33 20 (2278571 / 100000)
        (1139287 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865266432 7865299200 88686 _ _ (2278571 / 100000) (1782241 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865266432 7865299200 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865299200 :
    ThetaLowerSegment 7865299200 7865331968 (786377953233583 / 100000)
      (786381207032971 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865299200 33 20 (2278571 / 100000)
        (1139287 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865299200 7865331968 88686 _ _ (2278571 / 100000) (1782241 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865299200 7865331968 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865331968 :
    ThetaLowerSegment 7865331968 7865364736 (786381207032971 / 100000)
      (786384483619507 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865331968 33 20 (569643 / 25000) (91143 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865331968 7865364736 88686 _ _ (569643 / 25000) (891121 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865331968 7865364736 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865364736 :
    ThetaLowerSegment 7865364736 7865397504 (786384483619507 / 100000) (31455513233671 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865364736 33 20 (569643 / 25000) (91143 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865364736 7865397504 88686 _ _ (569643 / 25000) (891121 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865364736 7865397504 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865397504 :
    ThetaLowerSegment 7865397504 7865430272 (31455513233671 / 4000) (786391241864059 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865397504 33 20 (569643 / 25000) (91143 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865397504 7865430272 88687 _ _ (569643 / 25000) (891121 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865397504 7865430272 12 1497 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865430272 :
    ThetaLowerSegment 7865430272 7865463040 (786391241864059 / 100000) (39319725808673 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865430272 33 20 (2278573 / 100000)
        (142411 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865430272 7865463040 88687 _ _ (2278573 / 100000) (445561 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865430272 7865463040 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865463040 :
    ThetaLowerSegment 7865463040 7865495808 (39319725808673 / 5000) (98299712132671 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865463040 33 20 (2278573 / 100000)
        (142411 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865463040 7865495808 88687 _ _ (2278573 / 100000) (445561 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865463040 7865495808 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865495808 :
    ThetaLowerSegment 7865495808 7865528576 (98299712132671 / 12500) (393200494800399 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865495808 33 20 (1139287 / 50000)
        (2278577 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865495808 7865528576 88687 _ _ (1139287 / 50000) (891123 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865495808 7865528576 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865528576 :
    ThetaLowerSegment 7865528576 7865561344 (393200494800399 / 50000)
      (196601054585039 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865528576 33 20 (1139287 / 50000)
        (2278577 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865528576 7865561344 88687 _ _ (1139287 / 50000) (891123 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865528576 7865561344 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865561344 :
    ThetaLowerSegment 7865561344 7865594112 (196601054585039 / 25000)
      (393203780504107 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865561344 33 20 (1139287 / 50000)
        (2278577 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865561344 7865594112 88688 _ _ (1139287 / 50000) (891123 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865561344 7865594112 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865594112 :
    ThetaLowerSegment 7865594112 7865626880 (393203780504107 / 50000) (24575338105327 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865594112 33 20 (91143 / 4000)
        (1139289 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865594112 7865626880 88688 _ _ (91143 / 4000) (1782247 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865594112 7865626880 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865626880 :
    ThetaLowerSegment 7865626880 7865659648 (24575338105327 / 3125) (393207079880707 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865626880 33 20 (91143 / 4000)
        (1139289 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865626880 7865659648 88688 _ _ (91143 / 4000) (1782247 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865626880 7865659648 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865659648 :
    ThetaLowerSegment 7865659648 7865692416 (393207079880707 / 50000)
      (393208632730251 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865659648 33 20 (142411 / 6250)
        (2278579 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865659648 7865692416 88688 _ _ (142411 / 6250) (1782249 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865659648 7865692416 12 1363 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865692416 :
    ThetaLowerSegment 7865692416 7865725184 (393208632730251 / 50000)
      (393210243683483 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865692416 33 20 (142411 / 6250)
        (2278579 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865692416 7865725184 88688 _ _ (142411 / 6250) (1782249 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865692416 7865725184 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865725184 :
    ThetaLowerSegment 7865725184 7865757952 (393210243683483 / 50000)
      (786423757124961 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865725184 33 20 (2278577 / 100000)
        (113929 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865725184 7865757952 88688 _ _ (2278577 / 100000) (7129 / 400) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865725184 7865757952 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865757952 :
    ThetaLowerSegment 7865757952 7865790720 (786423757124961 / 100000)
      (786427061061611 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865757952 33 20 (2278577 / 100000)
        (113929 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865757952 7865790720 88689 _ _ (2278577 / 100000) (7129 / 400) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865757952 7865790720 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865790720 :
    ThetaLowerSegment 7865790720 7865823488 (786427061061611 / 100000)
      (786430196383563 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865790720 33 20 (2278577 / 100000)
        (113929 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865790720 7865823488 88689 _ _ (2278577 / 100000) (7129 / 400) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865790720 7865823488 12 1376 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865823488 :
    ThetaLowerSegment 7865823488 7865856256 (786430196383563 / 100000)
      (786433527664599 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865823488 33 20 (1139289 / 50000)
        (2278581 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865823488 7865856256 88689 _ _ (1139289 / 50000) (445563 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865823488 7865856256 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865856256 :
    ThetaLowerSegment 7865856256 7865889024 (786433527664599 / 100000)
      (786436840717011 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865856256 33 20 (1139289 / 50000)
        (2278581 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865856256 7865889024 88689 _ _ (1139289 / 50000) (445563 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865856256 7865889024 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865889024 :
    ThetaLowerSegment 7865889024 7865921792 (786436840717011 / 100000) (31457607244553 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865889024 33 20 (2278579 / 100000)
        (1139291 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865889024 7865921792 88689 _ _ (2278579 / 100000) (891127 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865889024 7865921792 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865921792 :
    ThetaLowerSegment 7865921792 7865954560 (31457607244553 / 4000) (49152719382359 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865921792 33 20 (2278579 / 100000)
        (1139291 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865921792 7865954560 88690 _ _ (2278579 / 100000) (891127 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865921792 7865954560 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865954560 :
    ThetaLowerSegment 7865954560 7865987328 (49152719382359 / 6250) (393223393357173 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865954560 33 20 (2278579 / 100000)
        (1139291 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865954560 7865987328 88690 _ _ (2278579 / 100000) (891127 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865954560 7865987328 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7865987328 :
    ThetaLowerSegment 7865987328 7866020096 (393223393357173 / 50000)
      (393225043049093 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7865987328 33 20 (113929 / 5000)
        (2278583 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7865987328 7866020096 88690 _ _ (113929 / 5000) (356451 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7865987328 7866020096 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866020096 :
    ThetaLowerSegment 7866020096 7866052864 (393225043049093 / 50000)
      (393226674512373 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866020096 33 20 (113929 / 5000)
        (2278583 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866020096 7866052864 88690 _ _ (113929 / 5000) (356451 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866020096 7866052864 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866052864 :
    ThetaLowerSegment 7866052864 7866085632 (393226674512373 / 50000)
      (157291339252047 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866052864 33 20 (2278581 / 100000)
        (284823 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866052864 7866085632 88690 _ _ (2278581 / 100000) (1782257 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866052864 7866085632 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866085632 :
    ThetaLowerSegment 7866085632 7866118400 (157291339252047 / 20000)
      (196614988088121 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866085632 33 20 (2278581 / 100000)
        (284823 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866085632 7866118400 88690 _ _ (2278581 / 100000) (1782257 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866085632 7866118400 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866118400 :
    ThetaLowerSegment 7866118400 7866151168 (196614988088121 / 25000)
      (196615815213387 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866118400 33 20 (1139291 / 50000)
        (455717 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866118400 7866151168 88691 _ _ (1139291 / 50000) (1782259 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866118400 7866151168 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866151168 :
    ThetaLowerSegment 7866151168 7866183936 (196615815213387 / 25000) (24577079295452 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866151168 33 20 (1139291 / 50000)
        (455717 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866151168 7866183936 88691 _ _ (1139291 / 50000) (1782259 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866151168 7866183936 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866183936 :
    ThetaLowerSegment 7866183936 7866216704 (24577079295452 / 3125) (393234919559891 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866183936 33 20 (1139291 / 50000)
        (455717 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866183936 7866216704 88691 _ _ (1139291 / 50000) (1782259 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866183936 7866216704 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866216704 :
    ThetaLowerSegment 7866216704 7866249472 (393234919559891 / 50000) (24577282018088 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866216704 33 20 (2278583 / 100000)
        (1139293 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866216704 7866249472 88691 _ _ (2278583 / 100000) (89113 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866216704 7866249472 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866249472 :
    ThetaLowerSegment 7866249472 7866282240 (24577282018088 / 3125) (196619065041669 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866249472 33 20 (2278583 / 100000)
        (1139293 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866249472 7866282240 88691 _ _ (2278583 / 100000) (89113 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866249472 7866282240 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866282240 :
    ThetaLowerSegment 7866282240 7866315008 (196619065041669 / 25000)
      (196619893876599 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866282240 33 20 (284823 / 12500)
        (2278587 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866282240 7866315008 88692 _ _ (284823 / 12500) (891131 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866282240 7866315008 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866315008 :
    ThetaLowerSegment 7866315008 7866347776 (196619893876599 / 25000) (39324139529421 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866315008 33 20 (284823 / 12500)
        (2278587 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866315008 7866347776 88692 _ _ (284823 / 12500) (891131 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866315008 7866347776 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866347776 :
    ThetaLowerSegment 7866347776 7866380544 (39324139529421 / 5000) (196621527051681 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866347776 33 20 (284823 / 12500)
        (2278587 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866347776 7866380544 88692 _ _ (284823 / 12500) (891131 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866347776 7866380544 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866380544 :
    ThetaLowerSegment 7866380544 7866413312 (196621527051681 / 25000)
      (786489400762049 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866380544 33 20 (455717 / 20000)
        (569647 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866380544 7866413312 88692 _ _ (455717 / 20000) (222783 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866380544 7866413312 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866413312 :
    ThetaLowerSegment 7866413312 7866446080 (786489400762049 / 100000)
      (786492681924449 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866413312 33 20 (455717 / 20000)
        (569647 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866413312 7866446080 88692 _ _ (455717 / 20000) (222783 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866413312 7866446080 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866446080 :
    ThetaLowerSegment 7866446080 7866478848 (786492681924449 / 100000)
      (786496015495767 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866446080 33 20 (1139293 / 50000)
        (2278589 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866446080 7866478848 88692 _ _ (1139293 / 50000) (356453 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866446080 7866478848 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866478848 :
    ThetaLowerSegment 7866478848 7866511616 (786496015495767 / 100000)
      (786499255645059 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866478848 33 20 (1139293 / 50000)
        (2278589 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866478848 7866511616 88693 _ _ (1139293 / 50000) (356453 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866478848 7866511616 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866511616 :
    ThetaLowerSegment 7866511616 7866544384 (786499255645059 / 100000)
      (786502564153383 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866511616 33 20 (2278587 / 100000)
        (227859 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866511616 7866544384 88693 _ _ (2278587 / 100000) (1782267 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866511616 7866544384 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866544384 :
    ThetaLowerSegment 7866544384 7866577152 (786502564153383 / 100000)
      (98313236076477 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866544384 33 20 (2278587 / 100000)
        (227859 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866544384 7866577152 88693 _ _ (2278587 / 100000) (1782267 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866544384 7866577152 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866577152 :
    ThetaLowerSegment 7866577152 7866609920 (98313236076477 / 12500)
      (786509135598291 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866577152 33 20 (2278587 / 100000)
        (227859 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866577152 7866609920 88693 _ _ (2278587 / 100000) (1782267 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866577152 7866609920 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866609920 :
    ThetaLowerSegment 7866609920 7866642688 (786509135598291 / 100000)
      (786512393979131 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866609920 33 20 (569647 / 25000)
        (2278591 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866609920 7866642688 88693 _ _ (569647 / 25000) (1782269 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866609920 7866642688 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866642688 :
    ThetaLowerSegment 7866642688 7866675456 (786512393979131 / 100000)
      (786515661474323 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866642688 33 20 (569647 / 25000)
        (2278591 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866642688 7866675456 88694 _ _ (569647 / 25000) (1782269 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866642688 7866675456 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866675456 :
    ThetaLowerSegment 7866675456 7866708224 (786515661474323 / 100000)
      (786518974542729 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866675456 33 20 (2278589 / 100000)
        (71206 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866675456 7866708224 88694 _ _ (2278589 / 100000) (178227 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866675456 7866708224 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866708224 :
    ThetaLowerSegment 7866708224 7866740992 (786518974542729 / 100000)
      (196630545129363 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866708224 33 20 (2278589 / 100000)
        (71206 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866708224 7866740992 88694 _ _ (2278589 / 100000) (178227 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866708224 7866740992 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866740992 :
    ThetaLowerSegment 7866740992 7866773760 (196630545129363 / 25000)
      (393262678435259 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866740992 33 20 (2278589 / 100000)
        (71206 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866740992 7866773760 88694 _ _ (2278589 / 100000) (178227 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866740992 7866773760 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866773760 :
    ThetaLowerSegment 7866773760 7866806528 (393262678435259 / 50000)
      (196632157801087 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866773760 33 20 (227859 / 10000)
        (2278593 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866773760 7866806528 88694 _ _ (227859 / 10000) (55696 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866773760 7866806528 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866806528 :
    ThetaLowerSegment 7866806528 7866839296 (196632157801087 / 25000)
      (393265925426009 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866806528 33 20 (227859 / 10000)
        (2278593 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866806528 7866839296 88695 _ _ (227859 / 10000) (55696 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866806528 7866839296 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866839296 :
    ThetaLowerSegment 7866839296 7866872064 (393265925426009 / 50000)
      (786535015814917 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866839296 33 20 (2278591 / 100000)
        (1139297 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866839296 7866872064 88695 _ _ (2278591 / 100000) (891137 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866839296 7866872064 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866872064 :
    ThetaLowerSegment 7866872064 7866904832 (786535015814917 / 100000)
      (786538319771867 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866872064 33 20 (2278591 / 100000)
        (1139297 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866872064 7866904832 88695 _ _ (2278591 / 100000) (891137 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866872064 7866904832 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866904832 :
    ThetaLowerSegment 7866904832 7866937600 (786538319771867 / 100000)
      (786541532586587 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866904832 33 20 (71206 / 3125) (455719 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866904832 7866937600 88695 _ _ (71206 / 3125) (71291 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866904832 7866937600 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866937600 :
    ThetaLowerSegment 7866937600 7866970368 (786541532586587 / 100000)
      (786544779580187 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866937600 33 20 (71206 / 3125) (455719 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866937600 7866970368 88695 _ _ (71206 / 3125) (71291 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866937600 7866970368 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7866970368 :
    ThetaLowerSegment 7866970368 7867003136 (786544779580187 / 100000)
      (786548049359707 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7866970368 33 20 (71206 / 3125) (455719 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7866970368 7867003136 88695 _ _ (71206 / 3125) (71291 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7866970368 7867003136 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867003136 :
    ThetaLowerSegment 7867003136 7867035904 (786548049359707 / 100000) (24579729435206 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867003136 33 20 (2278593 / 100000)
        (569649 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867003136 7867035904 88696 _ _ (2278593 / 100000) (1782277 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867003136 7867035904 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867035904 :
    ThetaLowerSegment 7867035904 7867068672 (24579729435206 / 3125) (393277322943221 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867035904 33 20 (2278593 / 100000)
        (569649 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867035904 7867068672 88696 _ _ (2278593 / 100000) (1782277 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867035904 7867068672 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867068672 :
    ThetaLowerSegment 7867068672 7867101440 (393277322943221 / 50000)
      (393278997709811 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867068672 33 20 (1139297 / 50000)
        (2278597 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867068672 7867101440 88696 _ _ (1139297 / 50000) (1782279 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867068672 7867101440 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867101440 :
    ThetaLowerSegment 7867101440 7867134208 (393278997709811 / 50000)
      (393280633740303 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867101440 33 20 (1139297 / 50000)
        (2278597 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867101440 7867134208 88696 _ _ (1139297 / 50000) (1782279 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867101440 7867134208 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867134208 :
    ThetaLowerSegment 7867134208 7867166976 (393280633740303 / 50000)
      (393282262935013 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867134208 33 20 (1139297 / 50000)
        (2278597 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867134208 7867166976 88696 _ _ (1139297 / 50000) (1782279 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867134208 7867166976 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867166976 :
    ThetaLowerSegment 7867166976 7867199744 (393282262935013 / 50000)
      (786567836668561 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867166976 33 20 (455719 / 20000)
        (1139299 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867166976 7867199744 88697 _ _ (455719 / 20000) (44557 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867166976 7867199744 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867199744 :
    ThetaLowerSegment 7867199744 7867232512 (786567836668561 / 100000)
      (786571149745691 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867199744 33 20 (455719 / 20000)
        (1139299 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867199744 7867232512 88697 _ _ (455719 / 20000) (44557 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867199744 7867232512 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867232512 :
    ThetaLowerSegment 7867232512 7867265280 (786571149745691 / 100000)
      (786574446874103 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867232512 33 20 (569649 / 25000)
        (2278599 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867232512 7867265280 88697 _ _ (569649 / 25000) (891141 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867232512 7867265280 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867265280 :
    ThetaLowerSegment 7867265280 7867298048 (786574446874103 / 100000)
      (786577728052343 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867265280 33 20 (569649 / 25000)
        (2278599 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867265280 7867298048 88697 _ _ (569649 / 25000) (891141 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867265280 7867298048 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867298048 :
    ThetaLowerSegment 7867298048 7867330816 (786577728052343 / 100000)
      (786580949988501 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867298048 33 20 (2278597 / 100000)
        (11393 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867298048 7867330816 88697 _ _ (2278597 / 100000) (1782283 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867298048 7867330816 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867330816 :
    ThetaLowerSegment 7867330816 7867363584 (786580949988501 / 100000)
      (786584317754867 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867330816 33 20 (2278597 / 100000)
        (11393 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867330816 7867363584 88697 _ _ (2278597 / 100000) (1782283 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867330816 7867363584 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867363584 :
    ThetaLowerSegment 7867363584 7867396352 (786584317754867 / 100000)
      (393293743641647 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867363584 33 20 (2278597 / 100000)
        (11393 / 500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867363584 7867396352 88698 _ _ (2278597 / 100000) (1782283 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867363584 7867396352 12 1391 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867396352 :
    ThetaLowerSegment 7867396352 7867429120 (393293743641647 / 50000) (98323852609021 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867396352 33 20 (1139299 / 50000)
        (2278601 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867396352 7867429120 88698 _ _ (1139299 / 50000) (356457 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867396352 7867429120 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867429120 :
    ThetaLowerSegment 7867429120 7867461888 (98323852609021 / 12500) (393297017986973 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867429120 33 20 (1139299 / 50000)
        (2278601 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867429120 7867461888 88698 _ _ (1139299 / 50000) (356457 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867429120 7867461888 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867461888 :
    ThetaLowerSegment 7867461888 7867494656 (393297017986973 / 50000)
      (786597378678679 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867461888 33 20 (2278599 / 100000)
        (1139301 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867461888 7867494656 88698 _ _ (2278599 / 100000) (1782287 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867461888 7867494656 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867494656 :
    ThetaLowerSegment 7867494656 7867527424 (786597378678679 / 100000)
      (196650157559863 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867494656 33 20 (2278599 / 100000)
        (1139301 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867494656 7867527424 88698 _ _ (2278599 / 100000) (1782287 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867494656 7867527424 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867527424 :
    ThetaLowerSegment 7867527424 7867560192 (196650157559863 / 25000)
      (196650959626711 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867527424 33 20 (2278599 / 100000)
        (1139301 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867527424 7867560192 88699 _ _ (2278599 / 100000) (1782287 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867527424 7867560192 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867560192 :
    ThetaLowerSegment 7867560192 7867592960 (196650959626711 / 25000)
      (196651791315711 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867560192 33 20 (11393 / 500)
        (2278603 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867560192 7867592960 88699 _ _ (11393 / 500) (111393 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867560192 7867592960 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867592960 :
    ThetaLowerSegment 7867592960 7867625728 (196651791315711 / 25000)
      (196652623004711 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867592960 33 20 (11393 / 500)
        (2278603 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867592960 7867625728 88699 _ _ (11393 / 500) (111393 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867592960 7867625728 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867625728 :
    ThetaLowerSegment 7867625728 7867658496 (196652623004711 / 25000)
      (786613807383299 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867625728 33 20 (2278601 / 100000)
        (569651 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867625728 7867658496 88699 _ _ (2278601 / 100000) (178229 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867625728 7867658496 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867658496 :
    ThetaLowerSegment 7867658496 7867691264 (786613807383299 / 100000)
      (157323406776463 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867658496 33 20 (2278601 / 100000)
        (569651 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867658496 7867691264 88699 _ _ (2278601 / 100000) (178229 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867658496 7867691264 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867691264 :
    ThetaLowerSegment 7867691264 7867724032 (157323406776463 / 20000)
      (786620444949509 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867691264 33 20 (1139301 / 50000)
        (455721 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867691264 7867724032 88700 _ _ (1139301 / 50000) (445573 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867691264 7867724032 12 1497 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867724032 :
    ThetaLowerSegment 7867724032 7867756800 (786620444949509 / 100000)
      (786623758036817 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867724032 33 20 (1139301 / 50000)
        (455721 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867724032 7867756800 88700 _ _ (1139301 / 50000) (445573 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867724032 7867756800 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867756800 :
    ThetaLowerSegment 7867756800 7867789568 (786623758036817 / 100000)
      (786626977701443 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867756800 33 20 (1139301 / 50000)
        (455721 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867756800 7867789568 88700 _ _ (1139301 / 50000) (445573 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867756800 7867789568 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867789568 :
    ThetaLowerSegment 7867789568 7867822336 (786626977701443 / 100000) (3146521299877 / 400) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867789568 33 20 (2278603 / 100000)
        (1139303 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867789568 7867822336 88700 _ _ (2278603 / 100000) (1782293 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867789568 7867822336 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867822336 :
    ThetaLowerSegment 7867822336 7867855104 (3146521299877 / 400) (78663365172963 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867822336 33 20 (2278603 / 100000)
        (1139303 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867822336 7867855104 88700 _ _ (2278603 / 100000) (1782293 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867822336 7867855104 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867855104 :
    ThetaLowerSegment 7867855104 7867887872 (78663365172963 / 10000) (78663694431241 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867855104 33 20 (569651 / 25000)
        (2278607 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867855104 7867887872 88700 _ _ (569651 / 25000) (356459 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867855104 7867887872 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867887872 :
    ThetaLowerSegment 7867887872 7867920640 (78663694431241 / 10000) (393320162880373 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867887872 33 20 (569651 / 25000)
        (2278607 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867887872 7867920640 88701 _ _ (569651 / 25000) (356459 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867887872 7867920640 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867920640 :
    ThetaLowerSegment 7867920640 7867953408 (393320162880373 / 50000) (78664343833381 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867920640 33 20 (569651 / 25000)
        (2278607 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867920640 7867953408 88701 _ _ (569651 / 25000) (356459 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867920640 7867953408 12 1366 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867953408 :
    ThetaLowerSegment 7867953408 7867986176 (78664343833381 / 10000) (31465870877317 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867953408 33 20 (455721 / 20000)
        (142413 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867953408 7867986176 88701 _ _ (455721 / 20000) (1782297 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867953408 7867986176 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7867986176 :
    ThetaLowerSegment 7867986176 7868018944 (31465870877317 / 4000) (157330027030781 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7867986176 33 20 (455721 / 20000)
        (142413 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7867986176 7868018944 88701 _ _ (455721 / 20000) (1782297 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7867986176 7868018944 12 1476 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868018944 :
    ThetaLowerSegment 7868018944 7868051712 (157330027030781 / 20000)
      (157330687826521 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868018944 33 20 (1139303 / 50000)
        (2278609 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868018944 7868051712 88701 _ _ (1139303 / 50000) (891149 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868018944 7868051712 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868051712 :
    ThetaLowerSegment 7868051712 7868084480 (157330687826521 / 20000)
      (786656683867549 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868051712 33 20 (1139303 / 50000)
        (2278609 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868051712 7868084480 88702 _ _ (1139303 / 50000) (891149 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868051712 7868084480 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868084480 :
    ThetaLowerSegment 7868084480 7868117248 (786656683867549 / 100000)
      (393329990505939 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868084480 33 20 (2278607 / 100000)
        (227861 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868084480 7868117248 88702 _ _ (2278607 / 100000) (17823 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868084480 7868117248 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868117248 :
    ThetaLowerSegment 7868117248 7868150016 (393329990505939 / 50000)
      (786663319171133 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868117248 33 20 (2278607 / 100000)
        (227861 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868117248 7868150016 88702 _ _ (2278607 / 100000) (17823 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868117248 7868150016 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868150016 :
    ThetaLowerSegment 7868150016 7868182784 (786663319171133 / 100000)
      (786666595807999 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868150016 33 20 (2278607 / 100000)
        (227861 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868150016 7868182784 88702 _ _ (2278607 / 100000) (17823 / 1000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868150016 7868182784 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868182784 :
    ThetaLowerSegment 7868182784 7868215552 (786666595807999 / 100000)
      (786669838267183 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868182784 33 20 (142413 / 6250)
        (2278611 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868182784 7868215552 88702 _ _ (142413 / 6250) (891151 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868182784 7868215552 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868215552 :
    ThetaLowerSegment 7868215552 7868248320 (786669838267183 / 100000)
      (157334609765171 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868215552 33 20 (142413 / 6250)
        (2278611 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868215552 7868248320 88702 _ _ (142413 / 6250) (891151 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868215552 7868248320 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868248320 :
    ThetaLowerSegment 7868248320 7868281088 (157334609765171 / 20000) (98334534701851 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868248320 33 20 (2278609 / 100000)
        (569653 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868248320 7868281088 88703 _ _ (2278609 / 100000) (1782303 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868248320 7868281088 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868281088 :
    ThetaLowerSegment 7868281088 7868313856 (98334534701851 / 12500) (78667941753801 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868281088 33 20 (2278609 / 100000)
        (569653 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868281088 7868313856 88703 _ _ (2278609 / 100000) (1782303 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868281088 7868313856 12 1378 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868313856 :
    ThetaLowerSegment 7868313856 7868346624 (78667941753801 / 10000) (39334136076053 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868313856 33 20 (2278609 / 100000)
        (569653 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868313856 7868346624 88703 _ _ (2278609 / 100000) (1782303 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868313856 7868346624 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868346624 :
    ThetaLowerSegment 7868346624 7868379392 (39334136076053 / 5000) (9833575660611 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868346624 33 20 (227861 / 10000)
        (2278613 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868346624 7868379392 88703 _ _ (227861 / 10000) (356461 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868346624 7868379392 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868379392 :
    ThetaLowerSegment 7868379392 7868412160 (9833575660611 / 1250) (19667232211877 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868379392 33 20 (227861 / 10000)
        (2278613 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868379392 7868412160 88703 _ _ (227861 / 10000) (356461 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868379392 7868412160 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868412160 :
    ThetaLowerSegment 7868412160 7868444928 (19667232211877 / 2500) (157338529885261 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868412160 33 20 (2278611 / 100000)
        (1139307 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868412160 7868444928 88704 _ _ (2278611 / 100000) (1782307 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868412160 7868444928 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868444928 :
    ThetaLowerSegment 7868444928 7868477696 (157338529885261 / 20000)
      (196673992340633 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868444928 33 20 (2278611 / 100000)
        (1139307 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868444928 7868477696 88704 _ _ (2278611 / 100000) (1782307 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868444928 7868477696 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868477696 :
    ThetaLowerSegment 7868477696 7868510464 (196673992340633 / 25000)
      (196674794412057 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868477696 33 20 (569653 / 25000)
        (455723 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868477696 7868510464 88704 _ _ (569653 / 25000) (445577 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868477696 7868510464 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868510464 :
    ThetaLowerSegment 7868510464 7868543232 (196674794412057 / 25000)
      (196675620408907 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868510464 33 20 (569653 / 25000)
        (455723 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868510464 7868543232 88704 _ _ (569653 / 25000) (445577 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868510464 7868543232 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868543232 :
    ThetaLowerSegment 7868543232 7868576000 (196675620408907 / 25000) (98338216651869 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868543232 33 20 (569653 / 25000)
        (455723 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868543232 7868576000 88704 _ _ (569653 / 25000) (445577 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868543232 7868576000 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868576000 :
    ThetaLowerSegment 7868576000 7868608768 (98338216651869 / 12500) (393354573288613 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868576000 33 20 (2278613 / 100000)
        (284827 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868576000 7868608768 88704 _ _ (2278613 / 100000) (178231 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868576000 7868608768 12 1498 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868608768 :
    ThetaLowerSegment 7868608768 7868641536 (393354573288613 / 50000)
      (393356159203261 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868608768 33 20 (2278613 / 100000)
        (284827 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868608768 7868641536 88705 _ _ (2278613 / 100000) (178231 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868608768 7868641536 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868641536 :
    ThetaLowerSegment 7868641536 7868674304 (393356159203261 / 50000) (3933578419597 / 500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868641536 33 20 (1139307 / 50000)
        (2278617 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868641536 7868674304 88705 _ _ (1139307 / 50000) (222789 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868641536 7868674304 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868674304 :
    ThetaLowerSegment 7868674304 7868707072 (3933578419597 / 500) (39335947116871 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868674304 33 20 (1139307 / 50000)
        (2278617 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868674304 7868707072 88705 _ _ (1139307 / 50000) (222789 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868674304 7868707072 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868707072 :
    ThetaLowerSegment 7868707072 7868739840 (39335947116871 / 5000) (24585068203954 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868707072 33 20 (1139307 / 50000)
        (2278617 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868707072 7868739840 88705 _ _ (1139307 / 50000) (222789 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868707072 7868739840 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868739840 :
    ThetaLowerSegment 7868739840 7868772608 (24585068203954 / 3125) (786725538926423 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868739840 33 20 (455723 / 20000)
        (1139309 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868739840 7868772608 88705 _ _ (455723 / 20000) (1782313 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868739840 7868772608 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868772608 :
    ThetaLowerSegment 7868772608 7868805376 (786725538926423 / 100000)
      (196682206741967 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868772608 33 20 (455723 / 20000)
        (1139309 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868772608 7868805376 88706 _ _ (455723 / 20000) (1782313 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868772608 7868805376 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868805376 :
    ThetaLowerSegment 7868805376 7868838144 (196682206741967 / 25000) (39336607345569 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868805376 33 20 (284827 / 12500)
        (2278619 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868805376 7868838144 88706 _ _ (284827 / 12500) (356463 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868805376 7868838144 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868838144 :
    ThetaLowerSegment 7868838144 7868870912 (39336607345569 / 5000) (1573470879023 / 200) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868838144 33 20 (284827 / 12500)
        (2278619 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868838144 7868870912 88706 _ _ (284827 / 12500) (356463 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868838144 7868870912 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868870912 :
    ThetaLowerSegment 7868870912 7868903680 (1573470879023 / 200) (393369307951799 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868870912 33 20 (2278617 / 100000)
        (113931 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868870912 7868903680 88706 _ _ (2278617 / 100000) (445579 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868870912 7868903680 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868903680 :
    ThetaLowerSegment 7868903680 7868936448 (393369307951799 / 50000)
      (786741862932823 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868903680 33 20 (2278617 / 100000)
        (113931 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868903680 7868936448 88706 _ _ (2278617 / 100000) (445579 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868903680 7868936448 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868936448 :
    ThetaLowerSegment 7868936448 7868969216 (786741862932823 / 100000)
      (196686293440831 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868936448 33 20 (2278617 / 100000)
        (113931 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868936448 7868969216 88707 _ _ (2278617 / 100000) (445579 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868936448 7868969216 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7868969216 :
    ThetaLowerSegment 7868969216 7869001984 (196686293440831 / 25000)
      (393374157988773 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7868969216 33 20 (1139309 / 50000)
        (2278621 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7868969216 7869001984 88707 _ _ (1139309 / 50000) (891159 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7868969216 7869001984 12 1379 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869001984 :
    ThetaLowerSegment 7869001984 7869034752 (393374157988773 / 50000)
      (393375759857227 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869001984 33 20 (1139309 / 50000)
        (2278621 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869001984 7869034752 88707 _ _ (1139309 / 50000) (891159 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869001984 7869034752 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869034752 :
    ThetaLowerSegment 7869034752 7869067520 (393375759857227 / 50000)
      (786754862448527 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869034752 33 20 (2278619 / 100000)
        (1139311 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869034752 7869067520 88707 _ _ (2278619 / 100000) (22279 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869034752 7869067520 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869067520 :
    ThetaLowerSegment 7869067520 7869100288 (786754862448527 / 100000) (39337903423273 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869067520 33 20 (2278619 / 100000)
        (1139311 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869067520 7869100288 88707 _ _ (2278619 / 100000) (22279 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869067520 7869100288 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869100288 :
    ThetaLowerSegment 7869100288 7869133056 (39337903423273 / 5000) (78676141803539 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869100288 33 20 (2278619 / 100000)
        (1139311 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869100288 7869133056 88707 _ _ (2278619 / 100000) (22279 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869100288 7869133056 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869133056 :
    ThetaLowerSegment 7869133056 7869165824 (78676141803539 / 10000) (78676479267161 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869133056 33 20 (113931 / 5000)
        (2278623 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869133056 7869165824 88708 _ _ (113931 / 5000) (1782321 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869133056 7869165824 12 1481 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869165824 :
    ThetaLowerSegment 7869165824 7869198592 (78676479267161 / 10000) (78676806476993 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869165824 33 20 (113931 / 5000)
        (2278623 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869165824 7869198592 88708 _ _ (113931 / 5000) (1782321 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869165824 7869198592 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869198592 :
    ThetaLowerSegment 7869198592 7869231360 (78676806476993 / 10000) (157354285147181 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869198592 33 20 (2278621 / 100000)
        (71207 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869198592 7869231360 88708 _ _ (2278621 / 100000) (1782323 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869198592 7869231360 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869231360 :
    ThetaLowerSegment 7869231360 7869264128 (157354285147181 / 20000)
      (393387286255753 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869231360 33 20 (2278621 / 100000)
        (71207 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869231360 7869264128 88708 _ _ (2278621 / 100000) (1782323 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869231360 7869264128 12 1381 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869264128 :
    ThetaLowerSegment 7869264128 7869296896 (393387286255753 / 50000)
      (196694460583519 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869264128 33 20 (1139311 / 50000) (18229 / 800) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869264128 7869296896 88708 _ _ (1139311 / 50000) (71293 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869264128 7869296896 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869296896 :
    ThetaLowerSegment 7869296896 7869329664 (196694460583519 / 25000)
      (393390601650763 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869296896 33 20 (1139311 / 50000) (18229 / 800) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869296896 7869329664 88709 _ _ (1139311 / 50000) (71293 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869296896 7869329664 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869329664 :
    ThetaLowerSegment 7869329664 7869362432 (393390601650763 / 50000)
      (393392217193761 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869329664 33 20 (1139311 / 50000) (18229 / 800) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869329664 7869362432 88709 _ _ (1139311 / 50000) (71293 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869329664 7869362432 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869362432 :
    ThetaLowerSegment 7869362432 7869395200 (393392217193761 / 50000)
      (786787640410083 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869362432 33 20 (2278623 / 100000)
        (1139313 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869362432 7869395200 88709 _ _ (2278623 / 100000) (891163 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869362432 7869395200 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869395200 :
    ThetaLowerSegment 7869395200 7869427968 (786787640410083 / 100000)
      (157358181591093 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869395200 33 20 (2278623 / 100000)
        (1139313 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869395200 7869427968 88709 _ _ (2278623 / 100000) (891163 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869395200 7869427968 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869427968 :
    ThetaLowerSegment 7869427968 7869460736 (157358181591093 / 20000)
      (157358830998933 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869427968 33 20 (71207 / 3125)
        (2278627 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869427968 7869460736 88709 _ _ (71207 / 3125) (222791 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869427968 7869460736 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869460736 :
    ThetaLowerSegment 7869460736 7869493504 (157358830998933 / 20000)
      (786797454442217 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869460736 33 20 (71207 / 3125)
        (2278627 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869460736 7869493504 88709 _ _ (71207 / 3125) (222791 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869460736 7869493504 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869493504 :
    ThetaLowerSegment 7869493504 7869526272 (786797454442217 / 100000)
      (786800765282889 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869493504 33 20 (71207 / 3125)
        (2278627 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869493504 7869526272 88710 _ _ (71207 / 3125) (222791 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869493504 7869526272 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869526272 :
    ThetaLowerSegment 7869526272 7869559040 (786800765282889 / 100000)
      (393401997047257 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869526272 33 20 (18229 / 800) (569657 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869526272 7869559040 88710 _ _ (18229 / 800) (178233 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869526272 7869559040 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869559040 :
    ThetaLowerSegment 7869559040 7869591808 (393401997047257 / 50000)
      (786807300379389 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869559040 33 20 (18229 / 800) (569657 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869559040 7869591808 88710 _ _ (18229 / 800) (178233 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869559040 7869591808 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869591808 :
    ThetaLowerSegment 7869591808 7869624576 (786807300379389 / 100000)
      (786810604387089 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869591808 33 20 (1139313 / 50000)
        (2278629 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869591808 7869624576 88710 _ _ (1139313 / 50000) (1782331 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869591808 7869624576 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869624576 :
    ThetaLowerSegment 7869624576 7869657344 (786810604387089 / 100000)
      (786813878772651 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869624576 33 20 (1139313 / 50000)
        (2278629 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869624576 7869657344 88710 _ _ (1139313 / 50000) (1782331 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869624576 7869657344 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869657344 :
    ThetaLowerSegment 7869657344 7869690112 (786813878772651 / 100000) (24588034469683 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869657344 33 20 (2278627 / 100000)
        (227863 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869657344 7869690112 88711 _ _ (2278627 / 100000) (1782333 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869657344 7869690112 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869690112 :
    ThetaLowerSegment 7869690112 7869722880 (24588034469683 / 3125) (786820318172553 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869690112 33 20 (2278627 / 100000)
        (227863 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869690112 7869722880 88711 _ _ (2278627 / 100000) (1782333 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869690112 7869722880 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869722880 :
    ThetaLowerSegment 7869722880 7869755648 (786820318172553 / 100000)
      (196705895861261 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869722880 33 20 (2278627 / 100000)
        (227863 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869722880 7869755648 88711 _ _ (2278627 / 100000) (1782333 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869722880 7869755648 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869755648 :
    ThetaLowerSegment 7869755648 7869788416 (196705895861261 / 25000) (24588337455911 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869755648 33 20 (569657 / 25000)
        (2278631 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869755648 7869788416 88711 _ _ (569657 / 25000) (356467 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869755648 7869788416 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869788416 :
    ThetaLowerSegment 7869788416 7869821184 (24588337455911 / 3125) (39341500686663 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869788416 33 20 (569657 / 25000)
        (2278631 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869788416 7869821184 88711 _ _ (569657 / 25000) (356467 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869788416 7869821184 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869821184 :
    ThetaLowerSegment 7869821184 7869853952 (39341500686663 / 5000) (786833320023939 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869821184 33 20 (2278629 / 100000)
        (284829 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869821184 7869853952 88712 _ _ (2278629 / 100000) (55698 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869821184 7869853952 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869853952 :
    ThetaLowerSegment 7869853952 7869886720 (786833320023939 / 100000)
      (196709134931679 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869853952 33 20 (2278629 / 100000)
        (284829 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869853952 7869886720 88712 _ _ (2278629 / 100000) (55698 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869853952 7869886720 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869886720 :
    ThetaLowerSegment 7869886720 7869919488 (196709134931679 / 25000)
      (786839773101267 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869886720 33 20 (2278629 / 100000)
        (284829 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869886720 7869919488 88712 _ _ (2278629 / 100000) (55698 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869886720 7869919488 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869919488 :
    ThetaLowerSegment 7869919488 7869952256 (786839773101267 / 100000)
      (786843134080517 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869919488 33 20 (227863 / 10000)
        (2278633 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869919488 7869952256 88712 _ _ (227863 / 10000) (891169 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869919488 7869952256 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869952256 :
    ThetaLowerSegment 7869952256 7869985024 (786843134080517 / 100000)
      (786846269475397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869952256 33 20 (227863 / 10000)
        (2278633 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869952256 7869985024 88712 _ _ (227863 / 10000) (891169 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869952256 7869985024 12 1376 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7869985024 :
    ThetaLowerSegment 7869985024 7870017792 (786846269475397 / 100000) (786849489181 / 100) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7869985024 33 20 (2278631 / 100000)
        (1139317 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7869985024 7870017792 88712 _ _ (2278631 / 100000) (89117 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7869985024 7870017792 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870017792 :
    ThetaLowerSegment 7870017792 7870050560 (786849489181 / 100) (786852809146367 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870017792 33 20 (2278631 / 100000)
        (1139317 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870017792 7870050560 88713 _ _ (2278631 / 100000) (89117 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870017792 7870050560 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870050560 :
    ThetaLowerSegment 7870050560 7870083328 (786852809146367 / 100000)
      (786856012902959 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870050560 33 20 (284829 / 12500)
        (455727 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870050560 7870083328 88713 _ _ (284829 / 12500) (1782341 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870050560 7870083328 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870083328 :
    ThetaLowerSegment 7870083328 7870116096 (786856012902959 / 100000)
      (786859287297143 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870083328 33 20 (284829 / 12500)
        (455727 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870083328 7870116096 88713 _ _ (284829 / 12500) (1782341 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870083328 7870116096 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870116096 :
    ThetaLowerSegment 7870116096 7870148864 (786859287297143 / 100000)
      (786862481939207 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870116096 33 20 (284829 / 12500)
        (455727 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870116096 7870148864 88713 _ _ (284829 / 12500) (1782341 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870116096 7870148864 12 1402 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870148864 :
    ThetaLowerSegment 7870148864 7870181632 (786862481939207 / 100000)
      (393432839430653 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870148864 33 20 (2278633 / 100000)
        (569659 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870148864 7870181632 88713 _ _ (2278633 / 100000) (1782343 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870148864 7870181632 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870181632 :
    ThetaLowerSegment 7870181632 7870214400 (393432839430653 / 50000)
      (786868985157789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870181632 33 20 (2278633 / 100000)
        (569659 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870181632 7870214400 88714 _ _ (2278633 / 100000) (1782343 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870181632 7870214400 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870214400 :
    ThetaLowerSegment 7870214400 7870247168 (786868985157789 / 100000)
      (786872300570259 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870214400 33 20 (1139317 / 50000)
        (2278637 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870214400 7870247168 88714 _ _ (1139317 / 50000) (356469 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870214400 7870247168 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870247168 :
    ThetaLowerSegment 7870247168 7870279936 (786872300570259 / 100000)
      (157375118183551 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870247168 33 20 (1139317 / 50000)
        (2278637 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870247168 7870279936 88714 _ _ (1139317 / 50000) (356469 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870247168 7870279936 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870279936 :
    ThetaLowerSegment 7870279936 7870312704 (157375118183551 / 20000)
      (786878874429349 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870279936 33 20 (1139317 / 50000)
        (2278637 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870279936 7870312704 88714 _ _ (1139317 / 50000) (356469 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870279936 7870312704 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870312704 :
    ThetaLowerSegment 7870312704 7870345472 (786878874429349 / 100000)
      (393441113150717 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870312704 33 20 (455727 / 20000)
        (1139319 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870312704 7870345472 88714 _ _ (455727 / 20000) (891173 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870312704 7870345472 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870345472 :
    ThetaLowerSegment 7870345472 7870378240 (393441113150717 / 50000)
      (786885564501709 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870345472 33 20 (455727 / 20000)
        (1139319 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870345472 7870378240 88714 _ _ (455727 / 20000) (891173 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870345472 7870378240 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870378240 :
    ThetaLowerSegment 7870378240 7870411008 (786885564501709 / 100000)
      (786888861688001 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870378240 33 20 (569659 / 25000)
        (2278639 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870378240 7870411008 88715 _ _ (569659 / 25000) (445587 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870378240 7870411008 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870411008 :
    ThetaLowerSegment 7870411008 7870443776 (786888861688001 / 100000)
      (786892022156133 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870411008 33 20 (569659 / 25000)
        (2278639 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870411008 7870443776 88715 _ _ (569659 / 25000) (445587 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870411008 7870443776 12 1387 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870443776 :
    ThetaLowerSegment 7870443776 7870476544 (786892022156133 / 100000)
      (786895307950687 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870443776 33 20 (2278637 / 100000)
        (28483 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870443776 7870476544 88715 _ _ (2278637 / 100000) (35647 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870443776 7870476544 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870476544 :
    ThetaLowerSegment 7870476544 7870509312 (786895307950687 / 100000)
      (786898516271583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870476544 33 20 (2278637 / 100000)
        (28483 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870476544 7870509312 88715 _ _ (2278637 / 100000) (35647 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870476544 7870509312 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870509312 :
    ThetaLowerSegment 7870509312 7870542080 (786898516271583 / 100000)
      (157380366793411 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870509312 33 20 (2278637 / 100000)
        (28483 / 1250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870509312 7870542080 88715 _ _ (2278637 / 100000) (35647 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870509312 7870542080 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870542080 :
    ThetaLowerSegment 7870542080 7870574848 (157380366793411 / 20000)
      (786905133434879 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870542080 33 20 (1139319 / 50000)
        (2278641 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870542080 7870574848 88716 _ _ (1139319 / 50000) (1782351 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870542080 7870574848 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870574848 :
    ThetaLowerSegment 7870574848 7870607616 (786905133434879 / 100000)
      (786908369100839 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870574848 33 20 (1139319 / 50000)
        (2278641 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870574848 7870607616 88716 _ _ (1139319 / 50000) (1782351 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870574848 7870607616 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870607616 :
    ThetaLowerSegment 7870607616 7870640384 (786908369100839 / 100000)
      (393455830867097 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870607616 33 20 (2278639 / 100000)
        (1139321 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870607616 7870640384 88716 _ _ (2278639 / 100000) (1782353 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870607616 7870640384 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870640384 :
    ThetaLowerSegment 7870640384 7870673152 (393455830867097 / 50000) (98364379834649 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870640384 33 20 (2278639 / 100000)
        (1139321 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870640384 7870673152 88716 _ _ (2278639 / 100000) (1782353 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870640384 7870673152 12 1482 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870673152 :
    ThetaLowerSegment 7870673152 7870705920 (98364379834649 / 12500)
      (786918395112439 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870673152 33 20 (2278639 / 100000)
        (1139321 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870673152 7870705920 88716 _ _ (2278639 / 100000) (1782353 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870673152 7870705920 12 1473 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870705920 :
    ThetaLowerSegment 7870705920 7870738688 (786918395112439 / 100000)
      (786921667239479 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870705920 33 20 (28483 / 1250)
        (2278643 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870705920 7870738688 88716 _ _ (28483 / 1250) (891177 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870705920 7870738688 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870738688 :
    ThetaLowerSegment 7870738688 7870771456 (786921667239479 / 100000)
      (786925014561639 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870738688 33 20 (28483 / 1250)
        (2278643 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870738688 7870771456 88717 _ _ (28483 / 1250) (891177 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870738688 7870771456 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870771456 :
    ThetaLowerSegment 7870771456 7870804224 (786925014561639 / 100000) (24591509884764 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870771456 33 20 (2278641 / 100000)
        (569661 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870771456 7870804224 88717 _ _ (2278641 / 100000) (445589 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870771456 7870804224 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870804224 :
    ThetaLowerSegment 7870804224 7870836992 (24591509884764 / 3125) (393465814728231 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870804224 33 20 (2278641 / 100000)
        (569661 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870804224 7870836992 88717 _ _ (2278641 / 100000) (445589 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870804224 7870836992 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870836992 :
    ThetaLowerSegment 7870836992 7870869760 (393465814728231 / 50000)
      (196733729384217 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870836992 33 20 (1139321 / 50000)
        (455729 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870836992 7870869760 88717 _ _ (1139321 / 50000) (891179 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870836992 7870869760 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870869760 :
    ThetaLowerSegment 7870869760 7870902528 (196733729384217 / 25000)
      (196734529187559 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870869760 33 20 (1139321 / 50000)
        (455729 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870869760 7870902528 88717 _ _ (1139321 / 50000) (891179 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870869760 7870902528 12 1404 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870902528 :
    ThetaLowerSegment 7870902528 7870935296 (196734529187559 / 25000) (15738829190361 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870902528 33 20 (1139321 / 50000)
        (455729 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870902528 7870935296 88718 _ _ (1139321 / 50000) (891179 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870902528 7870935296 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870935296 :
    ThetaLowerSegment 7870935296 7870968064 (15738829190361 / 2000) (786944692912467 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870935296 33 20 (2278643 / 100000)
        (1139323 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870935296 7870968064 88718 _ _ (2278643 / 100000) (1782359 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870935296 7870968064 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7870968064 :
    ThetaLowerSegment 7870968064 7871000832 (786944692912467 / 100000)
      (196736995248579 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7870968064 33 20 (2278643 / 100000)
        (1139323 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7870968064 7871000832 88718 _ _ (2278643 / 100000) (1782359 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7870968064 7871000832 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871000832 :
    ThetaLowerSegment 7871000832 7871033600 (196736995248579 / 25000) (39347558099067 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871000832 33 20 (569661 / 25000)
        (2278647 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871000832 7871033600 88718 _ _ (569661 / 25000) (1782361 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871000832 7871033600 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871033600 :
    ThetaLowerSegment 7871033600 7871066368 (39347558099067 / 5000) (196738630175649 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871033600 33 20 (569661 / 25000)
        (2278647 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871033600 7871066368 88718 _ _ (569661 / 25000) (1782361 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871033600 7871066368 12 1474 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871066368 :
    ThetaLowerSegment 7871066368 7871099136 (196738630175649 / 25000)
      (196739483527827 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871066368 33 20 (569661 / 25000)
        (2278647 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871066368 7871099136 88719 _ _ (569661 / 25000) (1782361 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871066368 7871099136 12 1498 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871099136 :
    ThetaLowerSegment 7871099136 7871131904 (196739483527827 / 25000)
      (393480532484769 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871099136 33 20 (455729 / 20000)
        (284831 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871099136 7871131904 88719 _ _ (455729 / 20000) (1782363 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871099136 7871131904 12 1374 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871131904 :
    ThetaLowerSegment 7871131904 7871164672 (393480532484769 / 50000)
      (393482200452909 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871131904 33 20 (455729 / 20000)
        (284831 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871131904 7871164672 88719 _ _ (455729 / 20000) (1782363 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871131904 7871164672 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871164672 :
    ThetaLowerSegment 7871164672 7871197440 (393482200452909 / 50000)
      (196741908576123 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871164672 33 20 (1139323 / 50000)
        (2278649 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871164672 7871197440 88719 _ _ (1139323 / 50000) (445591 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871164672 7871197440 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871197440 :
    ThetaLowerSegment 7871197440 7871230208 (196741908576123 / 25000) (9837137526791 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871197440 33 20 (1139323 / 50000)
        (2278649 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871197440 7871230208 88719 _ _ (1139323 / 50000) (445591 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871197440 7871230208 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871230208 :
    ThetaLowerSegment 7871230208 7871262976 (9837137526791 / 1250) (786974217314197 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871230208 33 20 (2278647 / 100000)
        (45573 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871230208 7871262976 88719 _ _ (2278647 / 100000) (891183 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871230208 7871262976 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871262976 :
    ThetaLowerSegment 7871262976 7871295744 (786974217314197 / 100000)
      (196744388883013 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871262976 33 20 (2278647 / 100000)
        (45573 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871262976 7871295744 88720 _ _ (2278647 / 100000) (891183 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871262976 7871295744 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871295744 :
    ThetaLowerSegment 7871295744 7871328512 (196744388883013 / 25000)
      (196745218310521 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871295744 33 20 (2278647 / 100000)
        (45573 / 2000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871295744 7871328512 88720 _ _ (2278647 / 100000) (891183 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871295744 7871328512 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871328512 :
    ThetaLowerSegment 7871328512 7871361280 (196745218310521 / 25000) (39349208522287 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871328512 33 20 (284831 / 12500)
        (2278651 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871328512 7871361280 88720 _ _ (284831 / 12500) (55699 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871328512 7871361280 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871361280 :
    ThetaLowerSegment 7871361280 7871394048 (39349208522287 / 5000) (196746861215729 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871361280 33 20 (284831 / 12500)
        (2278651 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871361280 7871394048 88720 _ _ (284831 / 12500) (55699 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871361280 7871394048 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871394048 :
    ThetaLowerSegment 7871394048 7871426816 (196746861215729 / 25000)
      (786990623578271 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871394048 33 20 (2278649 / 100000)
        (569663 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871394048 7871426816 88720 _ _ (2278649 / 100000) (1782369 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871394048 7871426816 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871426816 :
    ThetaLowerSegment 7871426816 7871459584 (786990623578271 / 100000)
      (786993904832831 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871426816 33 20 (2278649 / 100000)
        (569663 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871426816 7871459584 88721 _ _ (2278649 / 100000) (1782369 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871426816 7871459584 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871459584 :
    ThetaLowerSegment 7871459584 7871492352 (786993904832831 / 100000)
      (393498573675179 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871459584 33 20 (2278649 / 100000)
        (569663 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871459584 7871492352 88721 _ _ (2278649 / 100000) (1782369 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871459584 7871492352 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871492352 :
    ThetaLowerSegment 7871492352 7871525120 (393498573675179 / 50000)
      (196750090631377 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871492352 33 20 (45573 / 2000)
        (2278653 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871492352 7871525120 88721 _ _ (45573 / 2000) (1782371 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871492352 7871525120 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871525120 :
    ThetaLowerSegment 7871525120 7871557888 (196750090631377 / 25000)
      (393501813915479 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871525120 33 20 (45573 / 2000)
        (2278653 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871525120 7871557888 88721 _ _ (45573 / 2000) (1782371 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871525120 7871557888 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871557888 :
    ThetaLowerSegment 7871557888 7871590656 (393501813915479 / 50000)
      (393503477330709 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871557888 33 20 (2278651 / 100000)
        (1139327 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871557888 7871590656 88721 _ _ (2278651 / 100000) (1782373 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871557888 7871590656 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871590656 :
    ThetaLowerSegment 7871590656 7871623424 (393503477330709 / 50000)
      (787010242754811 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871590656 33 20 (2278651 / 100000)
        (1139327 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871590656 7871623424 88721 _ _ (2278651 / 100000) (1782373 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871590656 7871623424 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871623424 :
    ThetaLowerSegment 7871623424 7871656192 (787010242754811 / 100000)
      (787013487555259 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871623424 33 20 (569663 / 25000)
        (455731 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871623424 7871656192 88722 _ _ (569663 / 25000) (891187 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871623424 7871656192 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871656192 :
    ThetaLowerSegment 7871656192 7871688960 (787013487555259 / 100000)
      (787016805272571 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871656192 33 20 (569663 / 25000)
        (455731 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871656192 7871688960 88722 _ _ (569663 / 25000) (891187 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871656192 7871688960 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871688960 :
    ThetaLowerSegment 7871688960 7871721728 (787016805272571 / 100000)
      (157404018217751 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871688960 33 20 (569663 / 25000)
        (455731 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871688960 7871721728 88722 _ _ (569663 / 25000) (891187 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871688960 7871721728 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871721728 :
    ThetaLowerSegment 7871721728 7871754496 (157404018217751 / 20000)
      (393511671363293 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871721728 33 20 (2278653 / 100000)
        (71208 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871721728 7871754496 88722 _ _ (2278653 / 100000) (222797 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871721728 7871754496 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871754496 :
    ThetaLowerSegment 7871754496 7871787264 (393511671363293 / 50000) (39351328692827 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871754496 33 20 (2278653 / 100000)
        (71208 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871754496 7871787264 88722 _ _ (2278653 / 100000) (222797 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871754496 7871787264 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871787264 :
    ThetaLowerSegment 7871787264 7871820032 (39351328692827 / 5000) (393514928698477 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871787264 33 20 (1139327 / 50000)
        (2278657 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871787264 7871820032 88723 _ _ (1139327 / 50000) (891189 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871787264 7871820032 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871820032 :
    ThetaLowerSegment 7871820032 7871852800 (393514928698477 / 50000)
      (393516612623783 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871820032 33 20 (1139327 / 50000)
        (2278657 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871820032 7871852800 88723 _ _ (1139327 / 50000) (891189 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871820032 7871852800 12 1478 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871852800 :
    ThetaLowerSegment 7871852800 7871885568 (393516612623783 / 50000)
      (393518285155819 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871852800 33 20 (1139327 / 50000)
        (2278657 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871852800 7871885568 88723 _ _ (1139327 / 50000) (891189 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871852800 7871885568 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871885568 :
    ThetaLowerSegment 7871885568 7871918336 (393518285155819 / 50000)
      (787039776379223 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871885568 33 20 (455731 / 20000)
        (1139329 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871885568 7871918336 88723 _ _ (455731 / 20000) (1782379 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871885568 7871918336 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871918336 :
    ThetaLowerSegment 7871918336 7871951104 (787039776379223 / 100000)
      (787043048527803 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871918336 33 20 (455731 / 20000)
        (1139329 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871918336 7871951104 88723 _ _ (455731 / 20000) (1782379 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871918336 7871951104 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871951104 :
    ThetaLowerSegment 7871951104 7871983872 (787043048527803 / 100000)
      (787046395873467 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871951104 33 20 (71208 / 3125)
        (2278659 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871951104 7871983872 88724 _ _ (71208 / 3125) (1782381 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871951104 7871983872 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7871983872 :
    ThetaLowerSegment 7871983872 7872016640 (787046395873467 / 100000)
      (787049709039291 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7871983872 33 20 (71208 / 3125)
        (2278659 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7871983872 7872016640 88724 _ _ (71208 / 3125) (1782381 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7871983872 7872016640 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872016640 :
    ThetaLowerSegment 7872016640 7872049408 (787049709039291 / 100000)
      (393526484898729 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872016640 33 20 (2278657 / 100000)
        (113933 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872016640 7872049408 88724 _ _ (2278657 / 100000) (1782383 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872016640 7872049408 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872049408 :
    ThetaLowerSegment 7872049408 7872082176 (393526484898729 / 50000)
      (787056221440997 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872049408 33 20 (2278657 / 100000)
        (113933 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872049408 7872082176 88724 _ _ (2278657 / 100000) (1782383 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872049408 7872082176 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872082176 :
    ThetaLowerSegment 7872082176 7872114944 (787056221440997 / 100000)
      (787059425232739 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872082176 33 20 (2278657 / 100000)
        (113933 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872082176 7872114944 88724 _ _ (2278657 / 100000) (1782383 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872082176 7872114944 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872114944 :
    ThetaLowerSegment 7872114944 7872147712 (787059425232739 / 100000)
      (787062635861861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872114944 33 20 (1139329 / 50000)
        (2278661 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872114944 7872147712 88724 _ _ (1139329 / 50000) (111399 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872114944 7872147712 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872147712 :
    ThetaLowerSegment 7872147712 7872180480 (787062635861861 / 100000)
      (787065823704403 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872147712 33 20 (1139329 / 50000)
        (2278661 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872147712 7872180480 88725 _ _ (1139329 / 50000) (111399 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872147712 7872180480 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872180480 :
    ThetaLowerSegment 7872180480 7872213248 (787065823704403 / 100000) (24595910598539 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872180480 33 20 (2278659 / 100000)
        (1139331 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872180480 7872213248 88725 _ _ (2278659 / 100000) (891193 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872180480 7872213248 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872213248 :
    ThetaLowerSegment 7872213248 7872246016 (24595910598539 / 3125) (787072468274047 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872213248 33 20 (2278659 / 100000)
        (1139331 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872213248 7872246016 88725 _ _ (2278659 / 100000) (891193 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872213248 7872246016 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872246016 :
    ThetaLowerSegment 7872246016 7872278784 (787072468274047 / 100000)
      (787075781444233 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872246016 33 20 (2278659 / 100000)
        (1139331 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872246016 7872278784 88725 _ _ (2278659 / 100000) (891193 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872246016 7872278784 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872278784 :
    ThetaLowerSegment 7872278784 7872311552 (787075781444233 / 100000)
      (787079121959793 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872278784 33 20 (113933 / 5000)
        (2278663 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872278784 7872311552 88725 _ _ (113933 / 5000) (1782387 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872278784 7872311552 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872311552 :
    ThetaLowerSegment 7872311552 7872344320 (787079121959793 / 100000)
      (787082375886273 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872311552 33 20 (113933 / 5000)
        (2278663 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872311552 7872344320 88726 _ _ (113933 / 5000) (1782387 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872311552 7872344320 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872344320 :
    ThetaLowerSegment 7872344320 7872377088 (787082375886273 / 100000)
      (787085597912927 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872344320 33 20 (2278661 / 100000)
        (284833 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872344320 7872377088 88726 _ _ (2278661 / 100000) (1782389 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872344320 7872377088 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872377088 :
    ThetaLowerSegment 7872377088 7872409856 (787085597912927 / 100000)
      (787088879184767 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872377088 33 20 (2278661 / 100000)
        (284833 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872377088 7872409856 88726 _ _ (2278661 / 100000) (1782389 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872377088 7872409856 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872409856 :
    ThetaLowerSegment 7872409856 7872442624 (787088879184767 / 100000)
      (787092151343399 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872409856 33 20 (1139331 / 50000)
        (455733 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872409856 7872442624 88726 _ _ (1139331 / 50000) (1782391 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872409856 7872442624 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872442624 :
    ThetaLowerSegment 7872442624 7872475392 (787092151343399 / 100000)
      (787095332355551 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872442624 33 20 (1139331 / 50000)
        (455733 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872442624 7872475392 88726 _ _ (1139331 / 50000) (1782391 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872442624 7872475392 12 1396 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872475392 :
    ThetaLowerSegment 7872475392 7872508160 (787095332355551 / 100000)
      (787098634136789 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872475392 33 20 (1139331 / 50000)
        (455733 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872475392 7872508160 88726 _ _ (1139331 / 50000) (1782391 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872475392 7872508160 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872508160 :
    ThetaLowerSegment 7872508160 7872540928 (787098634136789 / 100000)
      (393550952009097 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872508160 33 20 (2278663 / 100000)
        (1139333 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872508160 7872540928 88727 _ _ (2278663 / 100000) (222799 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872508160 7872540928 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872540928 :
    ThetaLowerSegment 7872540928 7872573696 (393550952009097 / 50000)
      (787105214915533 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872540928 33 20 (2278663 / 100000)
        (1139333 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872540928 7872573696 88727 _ _ (2278663 / 100000) (222799 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872540928 7872573696 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872573696 :
    ThetaLowerSegment 7872573696 7872606464 (787105214915533 / 100000)
      (787108489355701 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872573696 33 20 (284833 / 12500)
        (2278667 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872573696 7872606464 88727 _ _ (284833 / 12500) (891197 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872573696 7872606464 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872606464 :
    ThetaLowerSegment 7872606464 7872639232 (787108489355701 / 100000)
      (787111745566557 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872606464 33 20 (284833 / 12500)
        (2278667 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872606464 7872639232 88727 _ _ (284833 / 12500) (891197 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872606464 7872639232 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872639232 :
    ThetaLowerSegment 7872639232 7872672000 (787111745566557 / 100000)
      (787114994941421 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872639232 33 20 (284833 / 12500)
        (2278667 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872639232 7872672000 88727 _ _ (284833 / 12500) (891197 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872639232 7872672000 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872672000 :
    ThetaLowerSegment 7872672000 7872704768 (787114994941421 / 100000) (49194893830271 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872672000 33 20 (455733 / 20000)
        (569667 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872672000 7872704768 88728 _ _ (455733 / 20000) (445599 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872672000 7872704768 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872704768 :
    ThetaLowerSegment 7872704768 7872737536 (49194893830271 / 6250) (787121530152641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872704768 33 20 (455733 / 20000)
        (569667 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872704768 7872737536 88728 _ _ (455733 / 20000) (445599 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872704768 7872737536 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872737536 :
    ThetaLowerSegment 7872737536 7872770304 (787121530152641 / 100000)
      (787124768137027 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872737536 33 20 (1139333 / 50000)
        (2278669 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872737536 7872770304 88728 _ _ (1139333 / 50000) (1782397 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872737536 7872770304 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872770304 :
    ThetaLowerSegment 7872770304 7872803072 (787124768137027 / 100000)
      (787127894466779 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872770304 33 20 (1139333 / 50000)
        (2278669 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872770304 7872803072 88728 _ _ (1139333 / 50000) (1782397 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872770304 7872803072 12 1372 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872803072 :
    ThetaLowerSegment 7872803072 7872835840 (787127894466779 / 100000)
      (393565630028969 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872803072 33 20 (2278667 / 100000)
        (227867 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872803072 7872835840 88728 _ _ (2278667 / 100000) (1782399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872803072 7872835840 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872835840 :
    ThetaLowerSegment 7872835840 7872868608 (393565630028969 / 50000) (24597955128909 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872835840 33 20 (2278667 / 100000)
        (227867 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872835840 7872868608 88729 _ _ (2278667 / 100000) (1782399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872835840 7872868608 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872868608 :
    ThetaLowerSegment 7872868608 7872901376 (24597955128909 / 3125) (787137829454899 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872868608 33 20 (2278667 / 100000)
        (227867 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872868608 7872901376 88729 _ _ (2278667 / 100000) (1782399 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872868608 7872901376 12 1433 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872901376 :
    ThetaLowerSegment 7872901376 7872934144 (787137829454899 / 100000)
      (787141147195507 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872901376 33 20 (569667 / 25000)
        (2278671 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872901376 7872934144 88729 _ _ (569667 / 25000) (1782401 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872901376 7872934144 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872934144 :
    ThetaLowerSegment 7872934144 7872966912 (787141147195507 / 100000)
      (787144369232059 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872934144 33 20 (569667 / 25000)
        (2278671 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872934144 7872966912 88729 _ _ (569667 / 25000) (1782401 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872934144 7872966912 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872966912 :
    ThetaLowerSegment 7872966912 7872999680 (787144369232059 / 100000)
      (787147655072757 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872966912 33 20 (2278669 / 100000)
        (142417 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872966912 7872999680 88729 _ _ (2278669 / 100000) (891201 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872966912 7872999680 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7872999680 :
    ThetaLowerSegment 7872999680 7873032448 (787147655072757 / 100000)
      (787150845209357 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7872999680 33 20 (2278669 / 100000)
        (142417 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7872999680 7873032448 88729 _ _ (2278669 / 100000) (891201 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7872999680 7873032448 12 1400 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873032448 :
    ThetaLowerSegment 7873032448 7873065216 (787150845209357 / 100000) (49197130484709 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873032448 33 20 (2278669 / 100000)
        (142417 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873032448 7873065216 88730 _ _ (2278669 / 100000) (891201 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873032448 7873065216 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873065216 :
    ThetaLowerSegment 7873065216 7873097984 (49197130484709 / 6250) (196789334284691 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873065216 33 20 (227867 / 10000)
        (2278673 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873065216 7873097984 88730 _ _ (227867 / 10000) (445601 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873065216 7873097984 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873097984 :
    ThetaLowerSegment 7873097984 7873130752 (196789334284691 / 25000)
      (393580278449737 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873097984 33 20 (227867 / 10000)
        (2278673 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873097984 7873130752 88730 _ _ (227867 / 10000) (445601 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873097984 7873130752 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873130752 :
    ThetaLowerSegment 7873130752 7873163520 (393580278449737 / 50000)
      (196790926505699 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873130752 33 20 (2278671 / 100000)
        (1139337 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873130752 7873163520 88730 _ _ (2278671 / 100000) (891203 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873130752 7873163520 12 1382 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873163520 :
    ThetaLowerSegment 7873163520 7873196288 (196790926505699 / 25000)
      (787166944014287 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873163520 33 20 (2278671 / 100000)
        (1139337 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873163520 7873196288 88730 _ _ (2278671 / 100000) (891203 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873163520 7873196288 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873196288 :
    ThetaLowerSegment 7873196288 7873229056 (787166944014287 / 100000)
      (393585122904283 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873196288 33 20 (2278671 / 100000)
        (1139337 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873196288 7873229056 88731 _ _ (2278671 / 100000) (891203 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873196288 7873229056 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873229056 :
    ThetaLowerSegment 7873229056 7873261824 (393585122904283 / 50000)
      (393586797728203 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873229056 33 20 (142417 / 6250) (91147 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873229056 7873261824 88731 _ _ (142417 / 6250) (1782407 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873229056 7873261824 12 1470 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873261824 :
    ThetaLowerSegment 7873261824 7873294592 (393586797728203 / 50000)
      (393588421282003 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873261824 33 20 (142417 / 6250) (91147 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873261824 7873294592 88731 _ _ (142417 / 6250) (1782407 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873261824 7873294592 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873294592 :
    ThetaLowerSegment 7873294592 7873327360 (393588421282003 / 50000)
      (787180167147913 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873294592 33 20 (2278673 / 100000)
        (569669 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873294592 7873327360 88731 _ _ (2278673 / 100000) (1782409 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873294592 7873327360 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873327360 :
    ThetaLowerSegment 7873327360 7873360128 (787180167147913 / 100000)
      (157436686952999 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873327360 33 20 (2278673 / 100000)
        (569669 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873327360 7873360128 88731 _ _ (2278673 / 100000) (1782409 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873327360 7873360128 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873360128 :
    ThetaLowerSegment 7873360128 7873392896 (157436686952999 / 20000)
      (787186665924727 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873360128 33 20 (1139337 / 50000)
        (2278677 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873360128 7873392896 88731 _ _ (1139337 / 50000) (1782411 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873360128 7873392896 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873392896 :
    ThetaLowerSegment 7873392896 7873425664 (787186665924727 / 100000)
      (787189981395397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873392896 33 20 (1139337 / 50000)
        (2278677 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873392896 7873425664 88732 _ _ (1139337 / 50000) (1782411 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873392896 7873425664 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873425664 :
    ThetaLowerSegment 7873425664 7873458432 (787189981395397 / 100000)
      (787193205719107 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873425664 33 20 (1139337 / 50000)
        (2278677 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873425664 7873458432 88732 _ _ (1139337 / 50000) (1782411 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873425664 7873458432 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873458432 :
    ThetaLowerSegment 7873458432 7873491200 (787193205719107 / 100000)
      (787196473339057 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873458432 33 20 (91147 / 4000)
        (1139339 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873458432 7873491200 88732 _ _ (91147 / 4000) (445603 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873458432 7873491200 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873491200 :
    ThetaLowerSegment 7873491200 7873523968 (787196473339057 / 100000)
      (787199845778057 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873491200 33 20 (91147 / 4000)
        (1139339 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873491200 7873523968 88732 _ _ (91147 / 4000) (445603 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873491200 7873523968 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873523968 :
    ThetaLowerSegment 7873523968 7873556736 (787199845778057 / 100000)
      (787203199989129 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873523968 33 20 (569669 / 25000)
        (2278679 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873523968 7873556736 88732 _ _ (569669 / 25000) (891207 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873523968 7873556736 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873556736 :
    ThetaLowerSegment 7873556736 7873589504 (787203199989129 / 100000)
      (787206419758317 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873556736 33 20 (569669 / 25000)
        (2278679 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873556736 7873589504 88733 _ _ (569669 / 25000) (891207 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873556736 7873589504 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873589504 :
    ThetaLowerSegment 7873589504 7873622272 (787206419758317 / 100000) (31488382846689 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873589504 33 20 (569669 / 25000)
        (2278679 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873589504 7873622272 88733 _ _ (569669 / 25000) (891207 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873589504 7873622272 12 1383 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873622272 :
    ThetaLowerSegment 7873622272 7873655040 (31488382846689 / 4000) (196803230775273 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873622272 33 20 (2278677 / 100000)
        (56967 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873622272 7873655040 88733 _ _ (2278677 / 100000) (111401 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873622272 7873655040 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873655040 :
    ThetaLowerSegment 7873655040 7873687808 (196803230775273 / 25000)
      (196804060213701 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873655040 33 20 (2278677 / 100000)
        (56967 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873655040 7873687808 88733 _ _ (2278677 / 100000) (111401 / 6250)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873655040 7873687808 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873687808 :
    ThetaLowerSegment 7873687808 7873720576 (196804060213701 / 25000)
      (393609778165647 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873687808 33 20 (1139339 / 50000)
        (2278681 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873687808 7873720576 88733 _ _ (1139339 / 50000) (1782417 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873687808 7873720576 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873720576 :
    ThetaLowerSegment 7873720576 7873753344 (393609778165647 / 50000)
      (393611496288859 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873720576 33 20 (1139339 / 50000)
        (2278681 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873720576 7873753344 88733 _ _ (1139339 / 50000) (1782417 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873720576 7873753344 12 1508 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873753344 :
    ThetaLowerSegment 7873753344 7873786112 (393611496288859 / 50000) (98403274550049 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873753344 33 20 (2278679 / 100000)
        (1139341 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873753344 7873786112 88734 _ _ (2278679 / 100000) (1782419 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873753344 7873786112 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873786112 :
    ThetaLowerSegment 7873786112 7873818880 (98403274550049 / 12500)
      (787229498206263 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873786112 33 20 (2278679 / 100000)
        (1139341 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873786112 7873818880 88734 _ _ (2278679 / 100000) (1782419 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873786112 7873818880 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873818880 :
    ThetaLowerSegment 7873818880 7873851648 (787229498206263 / 100000)
      (787232838749677 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873818880 33 20 (2278679 / 100000)
        (1139341 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873818880 7873851648 88734 _ _ (2278679 / 100000) (1782419 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873818880 7873851648 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873851648 :
    ThetaLowerSegment 7873851648 7873884416 (787232838749677 / 100000)
      (787236053967157 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873851648 33 20 (56967 / 2500)
        (2278683 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873851648 7873884416 88734 _ _ (56967 / 2500) (1782421 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873851648 7873884416 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873884416 :
    ThetaLowerSegment 7873884416 7873917184 (787236053967157 / 100000)
      (787239317036917 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873884416 33 20 (56967 / 2500)
        (2278683 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873884416 7873917184 88734 _ _ (56967 / 2500) (1782421 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873884416 7873917184 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873917184 :
    ThetaLowerSegment 7873917184 7873949952 (787239317036917 / 100000) (19681062850659 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873917184 33 20 (2278681 / 100000)
        (569671 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873917184 7873949952 88735 _ _ (2278681 / 100000) (891211 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873917184 7873949952 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873949952 :
    ThetaLowerSegment 7873949952 7873982720 (19681062850659 / 2500) (196811455667793 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873949952 33 20 (2278681 / 100000)
        (569671 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873949952 7873982720 88735 _ _ (2278681 / 100000) (891211 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873949952 7873982720 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7873982720 :
    ThetaLowerSegment 7873982720 7874015488 (196811455667793 / 25000) (49203070707249 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7873982720 33 20 (2278681 / 100000)
        (569671 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7873982720 7874015488 88735 _ _ (2278681 / 100000) (891211 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7873982720 7874015488 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874015488 :
    ThetaLowerSegment 7874015488 7874048256 (49203070707249 / 6250) (196813099736493 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874015488 33 20 (1139341 / 50000)
        (455737 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874015488 7874048256 88735 _ _ (1139341 / 50000) (222803 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874015488 7874048256 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874048256 :
    ThetaLowerSegment 7874048256 7874081024 (196813099736493 / 25000)
      (393627834427321 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874048256 33 20 (1139341 / 50000)
        (455737 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874048256 7874081024 88735 _ _ (1139341 / 50000) (222803 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874048256 7874081024 12 1435 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874081024 :
    ThetaLowerSegment 7874081024 7874113792 (393627834427321 / 50000)
      (157451804159467 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874081024 33 20 (2278683 / 100000)
        (1139343 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874081024 7874113792 88736 _ _ (2278683 / 100000) (71297 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874081024 7874113792 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874113792 :
    ThetaLowerSegment 7874113792 7874146560 (157451804159467 / 20000) (7872623362811 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874113792 33 20 (2278683 / 100000)
        (1139343 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874113792 7874146560 88736 _ _ (2278683 / 100000) (71297 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874113792 7874146560 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874146560 :
    ThetaLowerSegment 7874146560 7874179328 (7872623362811 / 1000) (196816405535857 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874146560 33 20 (569671 / 25000)
        (2278687 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874146560 7874179328 88736 _ _ (569671 / 25000) (1782427 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874146560 7874179328 12 1442 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874179328 :
    ThetaLowerSegment 7874179328 7874212096 (196816405535857 / 25000) (98408618342923 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874179328 33 20 (569671 / 25000)
        (2278687 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874179328 7874212096 88736 _ _ (569671 / 25000) (1782427 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874179328 7874212096 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874212096 :
    ThetaLowerSegment 7874212096 7874244864 (98408618342923 / 12500) (7872721346223 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874212096 33 20 (569671 / 25000)
        (2278687 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874212096 7874244864 88736 _ _ (569671 / 25000) (1782427 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874212096 7874244864 12 1399 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874244864 :
    ThetaLowerSegment 7874244864 7874277632 (7872721346223 / 1000) (7872755070761 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874244864 33 20 (455737 / 20000) (71209 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874244864 7874277632 88736 _ _ (455737 / 20000) (1782429 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874244864 7874277632 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874277632 :
    ThetaLowerSegment 7874277632 7874310400 (7872755070761 / 1000) (15745576223387 / 2000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874277632 33 20 (455737 / 20000) (71209 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874277632 7874310400 88737 _ _ (455737 / 20000) (1782429 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874277632 7874310400 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874310400 :
    ThetaLowerSegment 7874310400 7874343168 (15745576223387 / 2000) (393641059910711 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874310400 33 20 (1139343 / 50000)
        (2278689 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874310400 7874343168 88737 _ _ (1139343 / 50000) (178243 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874310400 7874343168 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874343168 :
    ThetaLowerSegment 7874343168 7874375936 (393641059910711 / 50000)
      (393642693728573 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874343168 33 20 (1139343 / 50000)
        (2278689 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874343168 7874375936 88737 _ _ (1139343 / 50000) (178243 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874343168 7874375936 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874375936 :
    ThetaLowerSegment 7874375936 7874408704 (393642693728573 / 50000) (49205544788587 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874375936 33 20 (1139343 / 50000)
        (2278689 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874375936 7874408704 88737 _ _ (1139343 / 50000) (178243 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874375936 7874408704 12 1461 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874408704 :
    ThetaLowerSegment 7874408704 7874441472 (49205544788587 / 6250) (787291895385757 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874408704 33 20 (2278687 / 100000)
        (227869 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874408704 7874441472 88737 _ _ (2278687 / 100000) (55701 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874408704 7874441472 12 1395 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874441472 :
    ThetaLowerSegment 7874441472 7874474240 (787291895385757 / 100000)
      (787295222268777 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874441472 33 20 (2278687 / 100000)
        (227869 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874441472 7874474240 88738 _ _ (2278687 / 100000) (55701 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874441472 7874474240 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874474240 :
    ThetaLowerSegment 7874474240 7874507008 (787295222268777 / 100000)
      (787298375972969 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874474240 33 20 (71209 / 3125)
        (2278691 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874474240 7874507008 88738 _ _ (71209 / 3125) (891217 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874474240 7874507008 12 1384 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874507008 :
    ThetaLowerSegment 7874507008 7874539776 (787298375972969 / 100000)
      (157460325532149 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874507008 33 20 (71209 / 3125)
        (2278691 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874507008 7874539776 88738 _ _ (71209 / 3125) (891217 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874507008 7874539776 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874539776 :
    ThetaLowerSegment 7874539776 7874572544 (157460325532149 / 20000)
      (157460986351959 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874539776 33 20 (2278689 / 100000)
        (569673 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874539776 7874572544 88738 _ _ (2278689 / 100000) (356487 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874539776 7874572544 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874572544 :
    ThetaLowerSegment 7874572544 7874605312 (157460986351959 / 20000)
      (157461665401281 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874572544 33 20 (2278689 / 100000)
        (569673 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874572544 7874605312 88738 _ _ (2278689 / 100000) (356487 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874572544 7874605312 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874605312 :
    ThetaLowerSegment 7874605312 7874638080 (157461665401281 / 20000)
      (787311576416919 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874605312 33 20 (2278689 / 100000)
        (569673 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874605312 7874638080 88738 _ _ (2278689 / 100000) (356487 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874605312 7874638080 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874638080 :
    ThetaLowerSegment 7874638080 7874670848 (787311576416919 / 100000)
      (787314866845279 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874638080 33 20 (227869 / 10000)
        (2278693 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874638080 7874670848 88739 _ _ (227869 / 10000) (1782437 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874638080 7874670848 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874670848 :
    ThetaLowerSegment 7874670848 7874703616 (787314866845279 / 100000)
      (787318120814599 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874670848 33 20 (227869 / 10000)
        (2278693 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874670848 7874703616 88739 _ _ (227869 / 10000) (1782437 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874670848 7874703616 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874703616 :
    ThetaLowerSegment 7874703616 7874736384 (787318120814599 / 100000)
      (787321374785347 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874703616 33 20 (2278691 / 100000)
        (1139347 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874703616 7874736384 88739 _ _ (2278691 / 100000) (1782439 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874703616 7874736384 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874736384 :
    ThetaLowerSegment 7874736384 7874769152 (787321374785347 / 100000)
      (787324701674207 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874736384 33 20 (2278691 / 100000)
        (1139347 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874736384 7874769152 88739 _ _ (2278691 / 100000) (1782439 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874736384 7874769152 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874769152 :
    ThetaLowerSegment 7874769152 7874801920 (787324701674207 / 100000)
      (393663951617531 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874769152 33 20 (2278691 / 100000)
        (1139347 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874769152 7874801920 88739 _ _ (2278691 / 100000) (1782439 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874769152 7874801920 12 1405 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874801920 :
    ThetaLowerSegment 7874801920 7874834688 (393663951617531 / 50000)
      (393665554677353 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874801920 33 20 (569673 / 25000)
        (455739 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874801920 7874834688 88740 _ _ (569673 / 25000) (44561 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874801920 7874834688 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874834688 :
    ThetaLowerSegment 7874834688 7874867456 (393665554677353 / 50000)
      (393667158876521 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874834688 33 20 (569673 / 25000)
        (455739 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874834688 7874867456 88740 _ _ (569673 / 25000) (44561 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874834688 7874867456 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874867456 :
    ThetaLowerSegment 7874867456 7874900224 (393667158876521 / 50000)
      (196834396349701 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874867456 33 20 (2278693 / 100000)
        (284837 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874867456 7874900224 88740 _ _ (2278693 / 100000) (891221 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874867456 7874900224 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874900224 :
    ThetaLowerSegment 7874900224 7874932992 (196834396349701 / 25000)
      (157468167418743 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874900224 33 20 (2278693 / 100000)
        (284837 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874900224 7874932992 88740 _ _ (2278693 / 100000) (891221 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874900224 7874932992 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874932992 :
    ThetaLowerSegment 7874932992 7874965760 (157468167418743 / 20000)
      (787344056888337 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874932992 33 20 (1139347 / 50000)
        (2278697 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874932992 7874965760 88740 _ _ (1139347 / 50000) (445611 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874932992 7874965760 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874965760 :
    ThetaLowerSegment 7874965760 7874998528 (787344056888337 / 100000)
      (787347313142063 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874965760 33 20 (1139347 / 50000)
        (2278697 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874965760 7874998528 88741 _ _ (1139347 / 50000) (445611 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874965760 7874998528 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7874998528 :
    ThetaLowerSegment 7874998528 7875031296 (787347313142063 / 100000)
      (787350701560041 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7874998528 33 20 (1139347 / 50000)
        (2278697 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7874998528 7875031296 88741 _ _ (1139347 / 50000) (445611 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7874998528 7875031296 12 1487 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875031296 :
    ThetaLowerSegment 7875031296 7875064064 (787350701560041 / 100000)
      (393677026760193 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875031296 33 20 (455739 / 20000)
        (1139349 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875031296 7875064064 88741 _ _ (455739 / 20000) (356489 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875031296 7875064064 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875064064 :
    ThetaLowerSegment 7875064064 7875096832 (393677026760193 / 50000)
      (787357369021611 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875064064 33 20 (455739 / 20000)
        (1139349 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875064064 7875096832 88741 _ _ (455739 / 20000) (356489 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875064064 7875096832 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875096832 :
    ThetaLowerSegment 7875096832 7875129600 (787357369021611 / 100000)
      (787360575146883 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875096832 33 20 (284837 / 12500)
        (2278699 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875096832 7875129600 88741 _ _ (284837 / 12500) (1782447 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875096832 7875129600 12 1407 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875129600 :
    ThetaLowerSegment 7875129600 7875162368 (787360575146883 / 100000)
      (787363797223027 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875129600 33 20 (284837 / 12500)
        (2278699 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875129600 7875162368 88741 _ _ (284837 / 12500) (1782447 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875129600 7875162368 12 1414 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875162368 :
    ThetaLowerSegment 7875162368 7875195136 (787363797223027 / 100000)
      (787367035250043 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875162368 33 20 (284837 / 12500)
        (2278699 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875162368 7875195136 88742 _ _ (284837 / 12500) (1782447 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875162368 7875195136 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875195136 :
    ThetaLowerSegment 7875195136 7875227904 (787367035250043 / 100000)
      (787370289229359 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875195136 33 20 (2278697 / 100000)
        (22787 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875195136 7875227904 88742 _ _ (2278697 / 100000) (1782449 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875195136 7875227904 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875227904 :
    ThetaLowerSegment 7875227904 7875260672 (787370289229359 / 100000)
      (196843368142267 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875227904 33 20 (2278697 / 100000)
        (22787 / 1000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875227904 7875260672 88742 _ _ (2278697 / 100000) (1782449 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875227904 7875260672 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875260672 :
    ThetaLowerSegment 7875260672 7875293440 (196843368142267 / 25000)
      (393688389479933 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875260672 33 20 (1139349 / 50000)
        (2278701 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875260672 7875293440 88742 _ _ (1139349 / 50000) (35649 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875260672 7875293440 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875293440 :
    ThetaLowerSegment 7875293440 7875326208 (393688389479933 / 50000) (39369004495403 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875293440 33 20 (1139349 / 50000)
        (2278701 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875293440 7875326208 88742 _ _ (1139349 / 50000) (35649 / 2000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875293440 7875326208 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875326208 :
    ThetaLowerSegment 7875326208 7875358976 (39369004495403 / 5000) (78738348516957 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875326208 33 20 (2278699 / 100000)
        (1139351 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875326208 7875358976 88743 _ _ (2278699 / 100000) (445613 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875326208 7875358976 12 1490 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875358976 :
    ThetaLowerSegment 7875358976 7875391744 (78738348516957 / 10000) (393693419707249 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875358976 33 20 (2278699 / 100000)
        (1139351 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875358976 7875391744 88743 _ _ (2278699 / 100000) (445613 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875358976 7875391744 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875391744 :
    ThetaLowerSegment 7875391744 7875424512 (393693419707249 / 50000)
      (787390050101389 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875391744 33 20 (2278699 / 100000)
        (1139351 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875391744 7875424512 88743 _ _ (2278699 / 100000) (445613 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875391744 7875424512 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875424512 :
    ThetaLowerSegment 7875424512 7875457280 (787390050101389 / 100000)
      (787393317757189 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875424512 33 20 (22787 / 1000)
        (2278703 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875424512 7875457280 88743 _ _ (22787 / 1000) (891227 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875424512 7875457280 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875457280 :
    ThetaLowerSegment 7875457280 7875490048 (787393317757189 / 100000)
      (787396628708289 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875457280 33 20 (22787 / 1000)
        (2278703 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875457280 7875490048 88743 _ _ (22787 / 1000) (891227 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875457280 7875490048 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875490048 :
    ThetaLowerSegment 7875490048 7875522816 (787396628708289 / 100000)
      (787399759643463 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875490048 33 20 (2278701 / 100000)
        (142419 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875490048 7875522816 88743 _ _ (2278701 / 100000) (356491 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875490048 7875522816 12 1374 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875522816 :
    ThetaLowerSegment 7875522816 7875555584 (787399759643463 / 100000)
      (787403004513687 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875522816 33 20 (2278701 / 100000)
        (142419 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875522816 7875555584 88744 _ _ (2278701 / 100000) (356491 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875522816 7875555584 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875555584 :
    ThetaLowerSegment 7875555584 7875588352 (787403004513687 / 100000)
      (157481251699743 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875555584 33 20 (2278701 / 100000)
        (142419 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875555584 7875588352 88744 _ _ (2278701 / 100000) (356491 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875555584 7875588352 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875588352 :
    ThetaLowerSegment 7875588352 7875621120 (157481251699743 / 20000)
      (787409571731423 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875588352 33 20 (1139351 / 50000)
        (455741 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875588352 7875621120 88744 _ _ (1139351 / 50000) (1782457 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875588352 7875621120 12 1454 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875621120 :
    ThetaLowerSegment 7875621120 7875653888 (787409571731423 / 100000)
      (787412848504899 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875621120 33 20 (1139351 / 50000)
        (455741 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875621120 7875653888 88744 _ _ (1139351 / 50000) (1782457 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875621120 7875653888 12 1438 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875653888 :
    ThetaLowerSegment 7875653888 7875686656 (787412848504899 / 100000)
      (787416061476129 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875653888 33 20 (2278703 / 100000)
        (1139353 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875653888 7875686656 88744 _ _ (2278703 / 100000) (891229 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875653888 7875686656 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875686656 :
    ThetaLowerSegment 7875686656 7875719424 (787416061476129 / 100000)
      (78741931318531 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875686656 33 20 (2278703 / 100000)
        (1139353 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875686656 7875719424 88745 _ _ (2278703 / 100000) (891229 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875686656 7875719424 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875719424 :
    ThetaLowerSegment 7875719424 7875752192 (78741931318531 / 10000) (393711309792407 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875719424 33 20 (142419 / 6250)
        (2278707 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875719424 7875752192 88745 _ _ (142419 / 6250) (89123 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875719424 7875752192 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875752192 :
    ThetaLowerSegment 7875752192 7875784960 (393711309792407 / 50000)
      (393712953877343 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875752192 33 20 (142419 / 6250)
        (2278707 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875752192 7875784960 88745 _ _ (142419 / 6250) (89123 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875752192 7875784960 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875784960 :
    ThetaLowerSegment 7875784960 7875817728 (393712953877343 / 50000)
      (393714626446079 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875784960 33 20 (142419 / 6250)
        (2278707 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875784960 7875817728 88745 _ _ (142419 / 6250) (89123 / 5000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875784960 7875817728 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875817728 :
    ThetaLowerSegment 7875817728 7875850496 (393714626446079 / 50000)
      (393716257998859 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875817728 33 20 (455741 / 20000)
        (569677 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875817728 7875850496 88745 _ _ (455741 / 20000) (891231 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875817728 7875850496 12 1432 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875850496 :
    ThetaLowerSegment 7875850496 7875883264 (393716257998859 / 50000)
      (787435790496803 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875850496 33 20 (455741 / 20000)
        (569677 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875850496 7875883264 88745 _ _ (455741 / 20000) (891231 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875850496 7875883264 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875883264 :
    ThetaLowerSegment 7875883264 7875916032 (787435790496803 / 100000) (31497562599893 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875883264 33 20 (1139353 / 50000)
        (2278709 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875883264 7875916032 88746 _ _ (1139353 / 50000) (1782463 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875883264 7875916032 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875916032 :
    ThetaLowerSegment 7875916032 7875948800 (31497562599893 / 4000) (787442337219141 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875916032 33 20 (1139353 / 50000)
        (2278709 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875916032 7875948800 88746 _ _ (1139353 / 50000) (1782463 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875916032 7875948800 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875948800 :
    ThetaLowerSegment 7875948800 7875981568 (787442337219141 / 100000)
      (787445641342841 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875948800 33 20 (1139353 / 50000)
        (2278709 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875948800 7875981568 88746 _ _ (1139353 / 50000) (1782463 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875948800 7875981568 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7875981568 :
    ThetaLowerSegment 7875981568 7876014336 (787445641342841 / 100000)
      (787448986484717 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7875981568 33 20 (2278707 / 100000)
        (227871 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7875981568 7876014336 88746 _ _ (2278707 / 100000) (356493 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7875981568 7876014336 12 1468 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876014336 :
    ThetaLowerSegment 7876014336 7876047104 (787448986484717 / 100000)
      (393726105427561 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876014336 33 20 (2278707 / 100000)
        (227871 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876014336 7876047104 88746 _ _ (2278707 / 100000) (356493 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876014336 7876047104 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876047104 :
    ThetaLowerSegment 7876047104 7876079872 (393726105427561 / 50000)
      (393727725588949 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876047104 33 20 (569677 / 25000)
        (2278711 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876047104 7876079872 88747 _ _ (569677 / 25000) (1782467 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876047104 7876079872 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876079872 :
    ThetaLowerSegment 7876079872 7876112640 (393727725588949 / 50000)
      (393729374234187 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876079872 33 20 (569677 / 25000)
        (2278711 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876079872 7876112640 88747 _ _ (569677 / 25000) (1782467 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876079872 7876112640 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876112640 :
    ThetaLowerSegment 7876112640 7876145408 (393729374234187 / 50000)
      (787462082219641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876112640 33 20 (2278709 / 100000)
        (284839 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876112640 7876145408 88747 _ _ (2278709 / 100000) (445617 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876112640 7876145408 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876145408 :
    ThetaLowerSegment 7876145408 7876178176 (787462082219641 / 100000)
      (787465349888347 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876145408 33 20 (2278709 / 100000)
        (284839 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876145408 7876178176 88747 _ _ (2278709 / 100000) (445617 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876145408 7876178176 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876178176 :
    ThetaLowerSegment 7876178176 7876210944 (787465349888347 / 100000)
      (393734337262389 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876178176 33 20 (2278709 / 100000)
        (284839 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876178176 7876210944 88747 _ _ (2278709 / 100000) (445617 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876178176 7876210944 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876210944 :
    ThetaLowerSegment 7876210944 7876243712 (393734337262389 / 50000)
      (393735957425199 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876210944 33 20 (227871 / 10000)
        (2278713 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876210944 7876243712 88748 _ _ (227871 / 10000) (178247 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876210944 7876243712 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876243712 :
    ThetaLowerSegment 7876243712 7876276480 (393735957425199 / 50000)
      (196868783666907 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876243712 33 20 (227871 / 10000)
        (2278713 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876243712 7876276480 88748 _ _ (227871 / 10000) (178247 / 10000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876243712 7876276480 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876276480 :
    ThetaLowerSegment 7876276480 7876309248 (196868783666907 / 25000) (196869610839 / 25) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876276480 33 20 (2278711 / 100000)
        (1139357 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876276480 7876309248 88748 _ _ (2278711 / 100000) (222809 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876276480 7876309248 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876309248 :
    ThetaLowerSegment 7876309248 7876342016 (196869610839 / 25) (787481763437927 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876309248 33 20 (2278711 / 100000)
        (1139357 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876309248 7876342016 88748 _ _ (2278711 / 100000) (222809 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876309248 7876342016 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876342016 :
    ThetaLowerSegment 7876342016 7876374784 (787481763437927 / 100000) (7874850516179 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876342016 33 20 (2278711 / 100000)
        (1139357 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876342016 7876374784 88748 _ _ (2278711 / 100000) (222809 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876342016 7876374784 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876374784 :
    ThetaLowerSegment 7876374784 7876407552 (7874850516179 / 1000) (39374421205583 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876374784 33 20 (284839 / 12500)
        (455743 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876374784 7876407552 88748 _ _ (284839 / 12500) (1782473 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876374784 7876407552 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876407552 :
    ThetaLowerSegment 7876407552 7876440320 (39374421205583 / 5000) (196872944593931 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876407552 33 20 (284839 / 12500)
        (455743 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876407552 7876440320 88749 _ _ (284839 / 12500) (1782473 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876407552 7876440320 12 1472 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876440320 :
    ThetaLowerSegment 7876440320 7876473088 (196872944593931 / 25000)
      (393747513910231 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876440320 33 20 (2278713 / 100000)
        (569679 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876440320 7876473088 88749 _ _ (2278713 / 100000) (71299 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876440320 7876473088 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876473088 :
    ThetaLowerSegment 7876473088 7876505856 (393747513910231 / 50000)
      (787498279543913 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876473088 33 20 (2278713 / 100000)
        (569679 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876473088 7876505856 88749 _ _ (2278713 / 100000) (71299 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876473088 7876505856 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876505856 :
    ThetaLowerSegment 7876505856 7876538624 (787498279543913 / 100000)
      (787501588236641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876505856 33 20 (1139357 / 50000)
        (2278717 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876505856 7876538624 88749 _ _ (1139357 / 50000) (1782477 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876505856 7876538624 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876538624 :
    ThetaLowerSegment 7876538624 7876571392 (787501588236641 / 100000)
      (787504798944667 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876538624 33 20 (1139357 / 50000)
        (2278717 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876538624 7876571392 88749 _ _ (1139357 / 50000) (1782477 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876538624 7876571392 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876571392 :
    ThetaLowerSegment 7876571392 7876604160 (787504798944667 / 100000)
      (787508059784401 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876571392 33 20 (1139357 / 50000)
        (2278717 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876571392 7876604160 88750 _ _ (1139357 / 50000) (1782477 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876571392 7876604160 12 1431 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876604160 :
    ThetaLowerSegment 7876604160 7876636928 (787508059784401 / 100000) (49219451557471 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876604160 33 20 (455743 / 20000)
        (1139359 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876604160 7876636928 88750 _ _ (455743 / 20000) (891239 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876604160 7876636928 12 1389 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876636928 :
    ThetaLowerSegment 7876636928 7876669696 (49219451557471 / 6250) (787514462973551 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876636928 33 20 (455743 / 20000)
        (1139359 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876636928 7876669696 88750 _ _ (455743 / 20000) (891239 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876636928 7876669696 12 1421 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876669696 :
    ThetaLowerSegment 7876669696 7876702464 (787514462973551 / 100000)
      (787517751160739 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876669696 33 20 (569679 / 25000)
        (2278719 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876669696 7876702464 88750 _ _ (569679 / 25000) (22281 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876669696 7876702464 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876702464 :
    ThetaLowerSegment 7876702464 7876735232 (787517751160739 / 100000)
      (787520993773607 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876702464 33 20 (569679 / 25000)
        (2278719 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876702464 7876735232 88750 _ _ (569679 / 25000) (22281 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876702464 7876735232 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876735232 :
    ThetaLowerSegment 7876735232 7876768000 (787520993773607 / 100000)
      (787524318420251 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876735232 33 20 (569679 / 25000)
        (2278719 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876735232 7876768000 88750 _ _ (569679 / 25000) (22281 / 1250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876735232 7876768000 12 1459 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876768000 :
    ThetaLowerSegment 7876768000 7876800768 (787524318420251 / 100000)
      (787527636232203 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876768000 33 20 (2278717 / 100000)
        (14242 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876768000 7876800768 88751 _ _ (2278717 / 100000) (891241 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876768000 7876800768 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876800768 :
    ThetaLowerSegment 7876800768 7876833536 (787527636232203 / 100000) (49220683630821 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876800768 33 20 (2278717 / 100000)
        (14242 / 625) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876800768 7876833536 88751 _ _ (2278717 / 100000) (891241 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876800768 7876833536 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876833536 :
    ThetaLowerSegment 7876833536 7876866304 (49220683630821 / 6250) (393767117699041 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876833536 33 20 (1139359 / 50000)
        (2278721 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876833536 7876866304 88751 _ _ (1139359 / 50000) (1782483 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876833536 7876866304 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876866304 :
    ThetaLowerSegment 7876866304 7876899072 (393767117699041 / 50000) (24610546330351 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876866304 33 20 (1139359 / 50000)
        (2278721 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876866304 7876899072 88751 _ _ (1139359 / 50000) (1782483 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876866304 7876899072 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876899072 :
    ThetaLowerSegment 7876899072 7876931840 (24610546330351 / 3125) (787540729745807 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876899072 33 20 (2278719 / 100000)
        (1139361 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876899072 7876931840 88751 _ _ (2278719 / 100000) (356497 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876899072 7876931840 12 1425 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876931840 :
    ThetaLowerSegment 7876931840 7876964608 (787540729745807 / 100000)
      (787543938182159 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876931840 33 20 (2278719 / 100000)
        (1139361 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876931840 7876964608 88752 _ _ (2278719 / 100000) (356497 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876931840 7876964608 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876964608 :
    ThetaLowerSegment 7876964608 7876997376 (787543938182159 / 100000)
      (787547196750329 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876964608 33 20 (2278719 / 100000)
        (1139361 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876964608 7876997376 88752 _ _ (2278719 / 100000) (356497 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876964608 7876997376 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7876997376 :
    ThetaLowerSegment 7876997376 7877030144 (787547196750329 / 100000)
      (787550519124089 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7876997376 33 20 (14242 / 625)
        (2278723 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7876997376 7877030144 88752 _ _ (14242 / 625) (1782487 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7876997376 7877030144 12 1458 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877030144 :
    ThetaLowerSegment 7877030144 7877062912 (787550519124089 / 100000)
      (787553855170169 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877030144 33 20 (14242 / 625)
        (2278723 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877030144 7877062912 88752 _ _ (14242 / 625) (1782487 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877030144 7877062912 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877062912 :
    ThetaLowerSegment 7877062912 7877095680 (787553855170169 / 100000)
      (196889276726259 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877062912 33 20 (2278721 / 100000)
        (569681 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877062912 7877095680 88752 _ _ (2278721 / 100000) (222811 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877062912 7877095680 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877095680 :
    ThetaLowerSegment 7877095680 7877128448 (196889276726259 / 25000) (24611261278707 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877095680 33 20 (2278721 / 100000)
        (569681 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877095680 7877128448 88753 _ _ (2278721 / 100000) (222811 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877095680 7877128448 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877128448 :
    ThetaLowerSegment 7877128448 7877161216 (24611261278707 / 3125) (24611361542431 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877128448 33 20 (2278721 / 100000)
        (569681 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877128448 7877161216 88753 _ _ (2278721 / 100000) (222811 / 12500)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877128448 7877161216 12 1408 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877161216 :
    ThetaLowerSegment 7877161216 7877193984 (24611361542431 / 3125) (78756680286431 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877161216 33 20 (1139361 / 50000)
        (91149 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877161216 7877193984 88753 _ _ (1139361 / 50000) (178249 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877161216 7877193984 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877193984 :
    ThetaLowerSegment 7877193984 7877226752 (78756680286431 / 10000) (78757001586233 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877193984 33 20 (1139361 / 50000)
        (91149 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877193984 7877226752 88753 _ _ (1139361 / 50000) (178249 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877193984 7877226752 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877226752 :
    ThetaLowerSegment 7877226752 7877259520 (78757001586233 / 10000)
      (787573313174511 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877226752 33 20 (2278723 / 100000)
        (1139363 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877226752 7877259520 88753 _ _ (2278723 / 100000) (445623 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877226752 7877259520 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877259520 :
    ThetaLowerSegment 7877259520 7877292288 (787573313174511 / 100000)
      (787576548961171 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877259520 33 20 (2278723 / 100000)
        (1139363 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877259520 7877292288 88753 _ _ (2278723 / 100000) (445623 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877259520 7877292288 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877292288 :
    ThetaLowerSegment 7877292288 7877325056 (787576548961171 / 100000)
      (787579732338599 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877292288 33 20 (569681 / 25000)
        (2278727 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877292288 7877325056 88754 _ _ (569681 / 25000) (1782493 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877292288 7877325056 12 1397 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877325056 :
    ThetaLowerSegment 7877325056 7877357824 (787579732338599 / 100000)
      (787583004586263 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877325056 33 20 (569681 / 25000)
        (2278727 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877325056 7877357824 88754 _ _ (569681 / 25000) (1782493 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877325056 7877357824 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877357824 :
    ThetaLowerSegment 7877357824 7877390592 (787583004586263 / 100000)
      (787586263161583 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877357824 33 20 (569681 / 25000)
        (2278727 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877357824 7877390592 88754 _ _ (569681 / 25000) (1782493 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877357824 7877390592 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877390592 :
    ThetaLowerSegment 7877390592 7877423360 (787586263161583 / 100000)
      (393794771123429 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877390592 33 20 (91149 / 4000) (284841 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877390592 7877423360 88754 _ _ (91149 / 4000) (356499 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877390592 7877423360 12 1439 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877423360 :
    ThetaLowerSegment 7877423360 7877456128 (393794771123429 / 50000)
      (196898197927177 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877423360 33 20 (91149 / 4000) (284841 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877423360 7877456128 88754 _ _ (91149 / 4000) (356499 / 20000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877423360 7877456128 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877456128 :
    ThetaLowerSegment 7877456128 7877488896 (196898197927177 / 25000)
      (196899009153633 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877456128 33 20 (1139363 / 50000)
        (2278729 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877456128 7877488896 88755 _ _ (1139363 / 50000) (55703 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877456128 7877488896 12 1424 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877488896 :
    ThetaLowerSegment 7877488896 7877521664 (196899009153633 / 25000)
      (196899815822637 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877488896 33 20 (1139363 / 50000)
        (2278729 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877488896 7877521664 88755 _ _ (1139363 / 50000) (55703 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877488896 7877521664 12 1416 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877521664 :
    ThetaLowerSegment 7877521664 7877554432 (196899815822637 / 25000)
      (393801275746083 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877521664 33 20 (1139363 / 50000)
        (2278729 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877521664 7877554432 88755 _ _ (1139363 / 50000) (55703 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877521664 7877554432 12 1443 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877554432 :
    ThetaLowerSegment 7877554432 7877587200 (393801275746083 / 50000)
      (787605771333417 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877554432 33 20 (2278727 / 100000)
        (227873 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877554432 7877587200 88755 _ _ (2278727 / 100000) (891249 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877554432 7877587200 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877587200 :
    ThetaLowerSegment 7877587200 7877619968 (787605771333417 / 100000)
      (787608934206493 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877587200 33 20 (2278727 / 100000)
        (227873 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877587200 7877619968 88755 _ _ (2278727 / 100000) (891249 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877587200 7877619968 12 1388 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877619968 :
    ThetaLowerSegment 7877619968 7877652736 (787608934206493 / 100000)
      (787612154049157 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877619968 33 20 (284841 / 12500)
        (2278731 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877619968 7877652736 88755 _ _ (284841 / 12500) (713 / 40) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877619968 7877652736 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877652736 :
    ThetaLowerSegment 7877652736 7877685504 (787612154049157 / 100000)
      (787615435417477 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877652736 33 20 (284841 / 12500)
        (2278731 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877652736 7877685504 88756 _ _ (284841 / 12500) (713 / 40) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877652736 7877685504 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877685504 :
    ThetaLowerSegment 7877685504 7877718272 (787615435417477 / 100000)
      (787618632472861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877685504 33 20 (284841 / 12500)
        (2278731 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877685504 7877718272 88756 _ _ (284841 / 12500) (713 / 40) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877685504 7877718272 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877718272 :
    ThetaLowerSegment 7877718272 7877751040 (787618632472861 / 100000)
      (157524390060457 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877718272 33 20 (2278729 / 100000)
        (569683 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877718272 7877751040 88756 _ _ (2278729 / 100000) (1782501 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877718272 7877751040 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877751040 :
    ThetaLowerSegment 7877751040 7877783808 (157524390060457 / 20000) (39381263292649 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877751040 33 20 (2278729 / 100000)
        (569683 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877751040 7877783808 88756 _ _ (2278729 / 100000) (1782501 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877751040 7877783808 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877783808 :
    ThetaLowerSegment 7877783808 7877816576 (39381263292649 / 5000) (78762856317529 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877783808 33 20 (227873 / 10000)
        (2278733 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877783808 7877816576 88756 _ _ (227873 / 10000) (1782503 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877783808 7877816576 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877816576 :
    ThetaLowerSegment 7877816576 7877849344 (78762856317529 / 10000) (78763184454649 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877816576 33 20 (227873 / 10000)
        (2278733 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877816576 7877849344 88757 _ _ (227873 / 10000) (1782503 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877816576 7877849344 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877849344 :
    ThetaLowerSegment 7877849344 7877882112 (78763184454649 / 10000) (24613596688028 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877849344 33 20 (2278731 / 100000)
        (1139367 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877849344 7877882112 88757 _ _ (2278731 / 100000) (356501 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877849344 7877882112 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877882112 :
    ThetaLowerSegment 7877882112 7877914880 (24613596688028 / 3125) (196909582453729 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877882112 33 20 (2278731 / 100000)
        (1139367 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877882112 7877914880 88757 _ _ (2278731 / 100000) (356501 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877882112 7877914880 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877914880 :
    ThetaLowerSegment 7877914880 7877947648 (196909582453729 / 25000)
      (196910375452117 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877914880 33 20 (2278731 / 100000)
        (1139367 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877914880 7877947648 88757 _ _ (2278731 / 100000) (356501 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877914880 7877947648 12 1392 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877947648 :
    ThetaLowerSegment 7877947648 7877980416 (196910375452117 / 25000) (98455594194879 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877947648 33 20 (569683 / 25000)
        (455747 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877947648 7877980416 88757 _ _ (569683 / 25000) (891253 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877947648 7877980416 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7877980416 :
    ThetaLowerSegment 7877980416 7878013184 (98455594194879 / 12500) (196912029811549 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7877980416 33 20 (569683 / 25000)
        (455747 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7877980416 7878013184 88757 _ _ (569683 / 25000) (891253 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7877980416 7878013184 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878013184 :
    ThetaLowerSegment 7878013184 7878045952 (196912029811549 / 25000) (78765130491493 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878013184 33 20 (2278733 / 100000)
        (142421 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878013184 7878045952 88758 _ _ (2278733 / 100000) (445627 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878013184 7878045952 12 1398 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878045952 :
    ThetaLowerSegment 7878045952 7878078720 (78765130491493 / 10000) (393827288587759 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878045952 33 20 (2278733 / 100000)
        (142421 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878045952 7878078720 88758 _ _ (2278733 / 100000) (445627 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878045952 7878078720 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878078720 :
    ThetaLowerSegment 7878078720 7878111488 (393827288587759 / 50000) (98457228331097 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878078720 33 20 (2278733 / 100000)
        (142421 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878078720 7878111488 88758 _ _ (2278733 / 100000) (445627 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878078720 7878111488 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878111488 :
    ThetaLowerSegment 7878111488 7878144256 (98457228331097 / 12500) (78766113309181 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878111488 33 20 (1139367 / 50000)
        (2278737 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878111488 7878144256 88758 _ _ (1139367 / 50000) (178251 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878111488 7878144256 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878144256 :
    ThetaLowerSegment 7878144256 7878177024 (78766113309181 / 10000) (24614513593043 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878144256 33 20 (1139367 / 50000)
        (2278737 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878144256 7878177024 88758 _ _ (1139367 / 50000) (178251 / 10000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878144256 7878177024 12 1449 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878177024 :
    ThetaLowerSegment 7878177024 7878209792 (24614513593043 / 3125) (787667741421861 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878177024 33 20 (455747 / 20000)
        (1139369 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878177024 7878209792 88759 _ _ (455747 / 20000) (1782511 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878177024 7878209792 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878209792 :
    ThetaLowerSegment 7878209792 7878242560 (787667741421861 / 100000)
      (196917765384689 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878209792 33 20 (455747 / 20000)
        (1139369 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878209792 7878242560 88759 _ _ (455747 / 20000) (1782511 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878209792 7878242560 12 1457 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878242560 :
    ThetaLowerSegment 7878242560 7878275328 (196917765384689 / 25000)
      (196918570348181 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878242560 33 20 (142421 / 6250)
        (2278739 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878242560 7878275328 88759 _ _ (142421 / 6250) (1782513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878242560 7878275328 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878275328 :
    ThetaLowerSegment 7878275328 7878308096 (196918570348181 / 25000)
      (196919384996301 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878275328 33 20 (142421 / 6250)
        (2278739 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878275328 7878308096 88759 _ _ (142421 / 6250) (1782513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878275328 7878308096 12 1430 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878308096 :
    ThetaLowerSegment 7878308096 7878340864 (196919384996301 / 25000) (39384044600293 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878308096 33 20 (142421 / 6250)
        (2278739 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878308096 7878340864 88759 _ _ (142421 / 6250) (1782513 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878308096 7878340864 12 1471 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878340864 :
    ThetaLowerSegment 7878340864 7878373632 (39384044600293 / 5000) (787684143763559 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878340864 33 20 (2278737 / 100000)
        (113937 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878340864 7878373632 88760 _ _ (2278737 / 100000) (356503 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878340864 7878373632 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878373632 :
    ThetaLowerSegment 7878373632 7878406400 (787684143763559 / 100000)
      (393843743335369 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878373632 33 20 (2278737 / 100000)
        (113937 / 5000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878373632 7878406400 88760 _ _ (2278737 / 100000) (356503 / 20000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878373632 7878406400 12 1467 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878406400 :
    ThetaLowerSegment 7878406400 7878439168 (393843743335369 / 50000)
      (393845368075563 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878406400 33 20 (1139369 / 50000)
        (2278741 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878406400 7878439168 88760 _ _ (1139369 / 50000) (445629 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878406400 7878439168 12 1426 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878439168 :
    ThetaLowerSegment 7878439168 7878471936 (393845368075563 / 50000) (9846174450099 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878439168 33 20 (1139369 / 50000)
        (2278741 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878439168 7878471936 88760 _ _ (1139369 / 50000) (445629 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878439168 7878471936 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878471936 :
    ThetaLowerSegment 7878471936 7878504704 (9846174450099 / 1250) (393848626670903 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878471936 33 20 (1139369 / 50000)
        (2278741 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878471936 7878504704 88760 _ _ (1139369 / 50000) (445629 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878471936 7878504704 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878504704 :
    ThetaLowerSegment 7878504704 7878537472 (393848626670903 / 50000)
      (787700623596787 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878504704 33 20 (2278739 / 100000)
        (1139371 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878504704 7878537472 88760 _ _ (2278739 / 100000) (891259 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878504704 7878537472 12 1479 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878537472 :
    ThetaLowerSegment 7878537472 7878570240 (787700623596787 / 100000)
      (157540754562817 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878537472 33 20 (2278739 / 100000)
        (1139371 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878537472 7878570240 88761 _ _ (2278739 / 100000) (891259 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878537472 7878570240 12 1382 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878570240 :
    ThetaLowerSegment 7878570240 7878603008 (157540754562817 / 20000) (31508283170633 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878570240 33 20 (113937 / 5000)
        (2278743 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878570240 7878603008 88761 _ _ (113937 / 5000) (44563 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878570240 7878603008 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878603008 :
    ThetaLowerSegment 7878603008 7878635776 (31508283170633 / 4000) (157542070307293 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878603008 33 20 (113937 / 5000)
        (2278743 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878603008 7878635776 88761 _ _ (113937 / 5000) (44563 / 2500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878603008 7878635776 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878635776 :
    ThetaLowerSegment 7878635776 7878668544 (157542070307293 / 20000)
      (157542731142183 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878635776 33 20 (2278741 / 100000)
        (284843 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878635776 7878668544 88761 _ _ (2278741 / 100000) (1782521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878635776 7878668544 12 1450 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878668544 :
    ThetaLowerSegment 7878668544 7878701312 (157542731142183 / 20000)
      (393858494754499 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878668544 33 20 (2278741 / 100000)
        (284843 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878668544 7878701312 88761 _ _ (2278741 / 100000) (1782521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878668544 7878701312 12 1463 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878701312 :
    ThetaLowerSegment 7878701312 7878734080 (393858494754499 / 50000)
      (393860181022839 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878701312 33 20 (2278741 / 100000)
        (284843 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878701312 7878734080 88762 _ _ (2278741 / 100000) (1782521 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878701312 7878734080 12 1480 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878734080 :
    ThetaLowerSegment 7878734080 7878766848 (393860181022839 / 50000)
      (196930879525837 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878734080 33 20 (1139371 / 50000)
        (455749 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878734080 7878766848 88762 _ _ (1139371 / 50000) (1782523 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878734080 7878766848 12 1385 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878766848 :
    ThetaLowerSegment 7878766848 7878799616 (196930879525837 / 25000)
      (393863368982897 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878766848 33 20 (1139371 / 50000)
        (455749 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878766848 7878799616 88762 _ _ (1139371 / 50000) (1782523 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878766848 7878799616 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878799616 :
    ThetaLowerSegment 7878799616 7878832384 (393863368982897 / 50000)
      (393864986890427 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878799616 33 20 (2278743 / 100000)
        (1139373 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878799616 7878832384 88762 _ _ (2278743 / 100000) (71301 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878799616 7878832384 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878832384 :
    ThetaLowerSegment 7878832384 7878865152 (393864986890427 / 50000)
      (196933310374579 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878832384 33 20 (2278743 / 100000)
        (1139373 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878832384 7878865152 88762 _ _ (2278743 / 100000) (71301 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878832384 7878865152 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878865152 :
    ThetaLowerSegment 7878865152 7878897920 (196933310374579 / 25000) (78773647275589 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878865152 33 20 (2278743 / 100000)
        (1139373 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878865152 7878897920 88762 _ _ (2278743 / 100000) (71301 / 4000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878865152 7878897920 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878897920 :
    ThetaLowerSegment 7878897920 7878930688 (78773647275589 / 10000) (393869881631113 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878897920 33 20 (284843 / 12500)
        (2278747 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878897920 7878930688 88763 _ _ (284843 / 12500) (891263 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878897920 7878930688 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878930688 :
    ThetaLowerSegment 7878930688 7878963456 (393869881631113 / 50000) (78774295578257 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878930688 33 20 (284843 / 12500)
        (2278747 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878930688 7878963456 88763 _ _ (284843 / 12500) (891263 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878930688 7878963456 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878963456 :
    ThetaLowerSegment 7878963456 7878996224 (78774295578257 / 10000) (78774622806039 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878963456 33 20 (455749 / 20000)
        (569687 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878963456 7878996224 88763 _ _ (455749 / 20000) (55704 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878963456 7878996224 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7878996224 :
    ThetaLowerSegment 7878996224 7879028992 (78774622806039 / 10000) (157549908726873 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7878996224 33 20 (455749 / 20000)
        (569687 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7878996224 7879028992 88763 _ _ (455749 / 20000) (55704 / 3125) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7878996224 7879028992 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879028992 :
    ThetaLowerSegment 7879028992 7879061760 (157549908726873 / 20000)
      (787752799962399 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879028992 33 20 (1139373 / 50000)
        (2278749 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879028992 7879061760 88763 _ _ (1139373 / 50000) (1782529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879028992 7879061760 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879061760 :
    ThetaLowerSegment 7879061760 7879094528 (787752799962399 / 100000)
      (787755974255577 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879061760 33 20 (1139373 / 50000)
        (2278749 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879061760 7879094528 88764 _ _ (1139373 / 50000) (1782529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879061760 7879094528 12 1393 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879094528 :
    ThetaLowerSegment 7879094528 7879127296 (787755974255577 / 100000)
      (787759271601039 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879094528 33 20 (1139373 / 50000)
        (2278749 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879094528 7879127296 88764 _ _ (1139373 / 50000) (1782529 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879094528 7879127296 12 1447 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879127296 :
    ThetaLowerSegment 7879127296 7879160064 (787759271601039 / 100000) (39388125712901 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879127296 33 20 (2278747 / 100000) (1823 / 80) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879127296 7879160064 88764 _ _ (2278747 / 100000) (1782531 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879127296 7879160064 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879160064 :
    ThetaLowerSegment 7879160064 7879192832 (39388125712901 / 5000) (49235362798043 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879160064 33 20 (2278747 / 100000) (1823 / 80) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879160064 7879192832 88764 _ _ (2278747 / 100000) (1782531 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879160064 7879192832 12 1444 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879192832 :
    ThetaLowerSegment 7879192832 7879225600 (49235362798043 / 6250) (98471143176657 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879192832 33 20 (569687 / 25000)
        (2278751 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879192832 7879225600 88764 _ _ (569687 / 25000) (1782533 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879192832 7879225600 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879225600 :
    ThetaLowerSegment 7879225600 7879258368 (98471143176657 / 12500) (196943115247899 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879225600 33 20 (569687 / 25000)
        (2278751 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879225600 7879258368 88765 _ _ (569687 / 25000) (1782533 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879225600 7879258368 12 1455 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879258368 :
    ThetaLowerSegment 7879258368 7879291136 (196943115247899 / 25000)
      (196943925342813 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879258368 33 20 (569687 / 25000)
        (2278751 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879258368 7879291136 88765 _ _ (569687 / 25000) (1782533 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879258368 7879291136 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879291136 :
    ThetaLowerSegment 7879291136 7879323904 (196943925342813 / 25000) (78777894175233 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879291136 33 20 (2278749 / 100000)
        (71211 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879291136 7879323904 88765 _ _ (2278749 / 100000) (891267 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879291136 7879323904 12 1422 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879323904 :
    ThetaLowerSegment 7879323904 7879356672 (78777894175233 / 10000) (393891038655477 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879323904 33 20 (2278749 / 100000)
        (71211 / 3125) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879323904 7879356672 88765 _ _ (2278749 / 100000) (891267 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879323904 7879356672 12 1376 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879356672 :
    ThetaLowerSegment 7879356672 7879389440 (393891038655477 / 50000)
      (196946327714301 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879356672 33 20 (1823 / 80) (2278753 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879356672 7879389440 88765 _ _ (1823 / 80) (222817 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879356672 7879389440 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879389440 :
    ThetaLowerSegment 7879389440 7879422208 (196946327714301 / 25000) (24618391941397 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879389440 33 20 (1823 / 80) (2278753 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879389440 7879422208 88765 _ _ (1823 / 80) (222817 / 12500) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879389440 7879422208 12 1418 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879422208 :
    ThetaLowerSegment 7879422208 7879454976 (24618391941397 / 3125) (787791907839931 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879422208 33 20 (2278751 / 100000)
        (1139377 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879422208 7879454976 88766 _ _ (2278751 / 100000) (891269 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879422208 7879454976 12 1477 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879454976 :
    ThetaLowerSegment 7879454976 7879487744 (787791907839931 / 100000)
      (196948783068149 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879454976 33 20 (2278751 / 100000)
        (1139377 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879454976 7879487744 88766 _ _ (2278751 / 100000) (891269 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879454976 7879487744 12 1415 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879487744 :
    ThetaLowerSegment 7879487744 7879520512 (196948783068149 / 25000)
      (393899277478299 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879487744 33 20 (2278751 / 100000)
        (1139377 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879487744 7879520512 88766 _ _ (2278751 / 100000) (891269 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879487744 7879520512 12 1502 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879520512 :
    ThetaLowerSegment 7879520512 7879553280 (393899277478299 / 50000)
      (393900927294747 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879520512 33 20 (71211 / 3125) (455751 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879520512 7879553280 88766 _ _ (71211 / 3125) (1782539 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879520512 7879553280 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879553280 :
    ThetaLowerSegment 7879553280 7879586048 (393900927294747 / 50000)
      (393902567996187 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879553280 33 20 (71211 / 3125) (455751 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879553280 7879586048 88766 _ _ (71211 / 3125) (1782539 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879553280 7879586048 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879586048 :
    ThetaLowerSegment 7879586048 7879618816 (393902567996187 / 50000)
      (787808392330411 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879586048 33 20 (2278753 / 100000)
        (569689 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879586048 7879618816 88767 _ _ (2278753 / 100000) (1782541 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879586048 7879618816 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879618816 :
    ThetaLowerSegment 7879618816 7879651584 (787808392330411 / 100000)
      (157562338392951 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879618816 33 20 (2278753 / 100000)
        (569689 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879618816 7879651584 88767 _ _ (2278753 / 100000) (1782541 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879618816 7879651584 12 1448 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879651584 :
    ThetaLowerSegment 7879651584 7879684352 (157562338392951 / 20000)
      (787815023501641 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879651584 33 20 (2278753 / 100000)
        (569689 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879651584 7879684352 88767 _ _ (2278753 / 100000) (1782541 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879651584 7879684352 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879684352 :
    ThetaLowerSegment 7879684352 7879717120 (787815023501641 / 100000)
      (157563645485953 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879684352 33 20 (1139377 / 50000)
        (2278757 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879684352 7879717120 88767 _ _ (1139377 / 50000) (1782543 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879684352 7879717120 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879717120 :
    ThetaLowerSegment 7879717120 7879749888 (157563645485953 / 20000)
      (787821501999263 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879717120 33 20 (1139377 / 50000)
        (2278757 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879717120 7879749888 88767 _ _ (1139377 / 50000) (1782543 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879717120 7879749888 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879749888 :
    ThetaLowerSegment 7879749888 7879782656 (787821501999263 / 100000) (24619525264774 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879749888 33 20 (455751 / 20000)
        (1139379 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879749888 7879782656 88767 _ _ (455751 / 20000) (111409 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879749888 7879782656 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879782656 :
    ThetaLowerSegment 7879782656 7879815424 (24619525264774 / 3125) (196957029306257 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879782656 33 20 (455751 / 20000)
        (1139379 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879782656 7879815424 88768 _ _ (455751 / 20000) (111409 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879782656 7879815424 12 1452 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879815424 :
    ThetaLowerSegment 7879815424 7879848192 (196957029306257 / 25000)
      (196957864470331 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879815424 33 20 (569689 / 25000)
        (2278759 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879815424 7879848192 88768 _ _ (569689 / 25000) (891273 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879815424 7879848192 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879848192 :
    ThetaLowerSegment 7879848192 7879880960 (196957864470331 / 25000) (24619836528556 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879848192 33 20 (569689 / 25000)
        (2278759 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879848192 7879880960 88768 _ _ (569689 / 25000) (891273 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879848192 7879880960 12 1453 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879880960 :
    ThetaLowerSegment 7879880960 7879913728 (24619836528556 / 3125) (49239875296707 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879880960 33 20 (569689 / 25000)
        (2278759 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879880960 7879913728 88768 _ _ (569689 / 25000) (891273 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879880960 7879913728 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879913728 :
    ThetaLowerSegment 7879913728 7879946496 (49239875296707 / 6250) (787841256533551 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879913728 33 20 (2278757 / 100000)
        (56969 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879913728 7879946496 88768 _ _ (2278757 / 100000) (445637 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879913728 7879946496 12 1427 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879946496 :
    ThetaLowerSegment 7879946496 7879979264 (787841256533551 / 100000)
      (787844574403743 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879946496 33 20 (2278757 / 100000)
        (56969 / 2500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879946496 7879979264 88769 _ _ (2278757 / 100000) (445637 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879946496 7879979264 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7879979264 :
    ThetaLowerSegment 7879979264 7880012032 (787844574403743 / 100000)
      (787847905947939 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7879979264 33 20 (1139379 / 50000)
        (2278761 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7879979264 7880012032 88769 _ _ (1139379 / 50000) (1782549 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7879979264 7880012032 12 1462 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880012032 :
    ThetaLowerSegment 7880012032 7880044800 (787847905947939 / 100000) (31514045397921 / 4000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880012032 33 20 (1139379 / 50000)
        (2278761 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880012032 7880044800 88769 _ _ (1139379 / 50000) (1782549 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880012032 7880044800 12 1417 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880044800 :
    ThetaLowerSegment 7880044800 7880077568 (31514045397921 / 4000) (787854368505627 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880044800 33 20 (1139379 / 50000)
        (2278761 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880044800 7880077568 88769 _ _ (1139379 / 50000) (1782549 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880044800 7880077568 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880077568 :
    ThetaLowerSegment 7880077568 7880110336 (787854368505627 / 100000)
      (787857636246033 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880077568 33 20 (2278759 / 100000)
        (1139381 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880077568 7880110336 88769 _ _ (2278759 / 100000) (1782551 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880077568 7880110336 12 1434 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880110336 :
    ThetaLowerSegment 7880110336 7880143104 (787857636246033 / 100000)
      (787860931331547 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880110336 33 20 (2278759 / 100000)
        (1139381 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880110336 7880143104 88769 _ _ (2278759 / 100000) (1782551 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880110336 7880143104 12 1446 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880143104 :
    ThetaLowerSegment 7880143104 7880175872 (787860931331547 / 100000)
      (787864224139747 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880143104 33 20 (56969 / 2500)
        (2278763 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880143104 7880175872 88770 _ _ (56969 / 2500) (1782553 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880143104 7880175872 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880175872 :
    ThetaLowerSegment 7880175872 7880208640 (787864224139747 / 100000)
      (787867551129347 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880175872 33 20 (56969 / 2500)
        (2278763 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880175872 7880208640 88770 _ _ (56969 / 2500) (1782553 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880175872 7880208640 12 1460 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880208640 :
    ThetaLowerSegment 7880208640 7880241408 (787867551129347 / 100000)
      (787870869005363 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880208640 33 20 (2278761 / 100000)
        (569691 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880208640 7880241408 88770 _ _ (2278761 / 100000) (891277 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880208640 7880241408 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880241408 :
    ThetaLowerSegment 7880241408 7880274176 (787870869005363 / 100000)
      (196968519944903 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880241408 33 20 (2278761 / 100000)
        (569691 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880241408 7880274176 88770 _ _ (2278761 / 100000) (891277 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880241408 7880274176 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880274176 :
    ThetaLowerSegment 7880274176 7880306944 (196968519944903 / 25000)
      (787877272323773 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880274176 33 20 (2278761 / 100000)
        (569691 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880274176 7880306944 88770 _ _ (2278761 / 100000) (891277 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880274176 7880306944 12 1401 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880306944 :
    ThetaLowerSegment 7880306944 7880339712 (787877272323773 / 100000)
      (157576111203963 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880306944 33 20 (1139381 / 50000)
        (455753 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880306944 7880339712 88771 _ _ (1139381 / 50000) (445639 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880306944 7880339712 12 1441 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880339712 :
    ThetaLowerSegment 7880339712 7880372480 (157576111203963 / 20000)
      (787883862503477 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880339712 33 20 (1139381 / 50000)
        (455753 / 20000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880339712 7880372480 88771 _ _ (1139381 / 50000) (445639 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880339712 7880372480 12 1451 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880372480 :
    ThetaLowerSegment 7880372480 7880405248 (787883862503477 / 100000)
      (157577436076481 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880372480 33 20 (2278763 / 100000)
        (1139383 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880372480 7880405248 88771 _ _ (2278763 / 100000) (891279 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880372480 7880405248 12 1456 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880405248 :
    ThetaLowerSegment 7880405248 7880438016 (157577436076481 / 20000)
      (393945211531077 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880405248 33 20 (2278763 / 100000)
        (1139383 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880405248 7880438016 88771 _ _ (2278763 / 100000) (891279 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880405248 7880438016 12 1423 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880438016 :
    ThetaLowerSegment 7880438016 7880470784 (393945211531077 / 50000)
      (787893620166643 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880438016 33 20 (2278763 / 100000)
        (1139383 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880438016 7880470784 88771 _ _ (2278763 / 100000) (891279 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880438016 7880470784 12 1403 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880470784 :
    ThetaLowerSegment 7880470784 7880503552 (787893620166643 / 100000)
      (157579374848327 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880470784 33 20 (569691 / 25000)
        (2278767 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880470784 7880503552 88772 _ _ (569691 / 25000) (1782559 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880470784 7880503552 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880503552 :
    ThetaLowerSegment 7880503552 7880536320 (157579374848327 / 20000)
      (157580033411123 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880503552 33 20 (569691 / 25000)
        (2278767 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880503552 7880536320 88772 _ _ (569691 / 25000) (1782559 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880503552 7880536320 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880536320 :
    ThetaLowerSegment 7880536320 7880569088 (157580033411123 / 20000) (78790352823399 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880536320 33 20 (455753 / 20000)
        (142423 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880536320 7880569088 88772 _ _ (455753 / 20000) (1782561 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880536320 7880569088 12 1475 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880569088 :
    ThetaLowerSegment 7880569088 7880601856 (78790352823399 / 10000) (4924417133079 / 625) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880569088 33 20 (455753 / 20000)
        (142423 / 6250) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880569088 7880601856 88772 _ _ (455753 / 20000) (1782561 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880569088 7880601856 12 1410 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880601856 :
    ThetaLowerSegment 7880601856 7880634624 (4924417133079 / 625) (196977486309409 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880601856 33 20 (1139383 / 50000)
        (2278769 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880601856 7880634624 88772 _ _ (1139383 / 50000) (1782563 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880601856 7880634624 12 1406 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880634624 :
    ThetaLowerSegment 7880634624 7880667392 (196977486309409 / 25000)
      (196978295271339 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880634624 33 20 (1139383 / 50000)
        (2278769 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880634624 7880667392 88772 _ _ (1139383 / 50000) (1782563 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880634624 7880667392 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880667392 :
    ThetaLowerSegment 7880667392 7880700160 (196978295271339 / 25000) (78791643744197 / 10000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880667392 33 20 (1139383 / 50000)
        (2278769 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880667392 7880700160 88773 _ _ (1139383 / 50000) (1782563 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880667392 7880700160 12 1429 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880700160 :
    ThetaLowerSegment 7880700160 7880732928 (78791643744197 / 10000) (157583946052057 / 20000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880700160 33 20 (2278767 / 100000)
        (227877 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880700160 7880732928 88773 _ _ (2278767 / 100000) (445641 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880700160 7880732928 12 1445 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880732928 :
    ThetaLowerSegment 7880732928 7880765696 (157583946052057 / 20000) (98490368769757 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880732928 33 20 (2278767 / 100000)
        (227877 / 10000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880732928 7880765696 88773 _ _ (2278767 / 100000) (445641 / 25000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880732928 7880765696 12 1413 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880765696 :
    ThetaLowerSegment 7880765696 7880798464 (98490368769757 / 12500) (98490772966231 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880765696 33 20 (142423 / 6250)
        (2278771 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880765696 7880798464 88773 _ _ (142423 / 6250) (891283 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880765696 7880798464 12 1419 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880798464 :
    ThetaLowerSegment 7880798464 7880831232 (98490772966231 / 12500) (98491190550467 / 12500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880798464 33 20 (142423 / 6250)
        (2278771 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880798464 7880831232 88773 _ _ (142423 / 6250) (891283 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880798464 7880831232 12 1466 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880831232 :
    ThetaLowerSegment 7880831232 7880864000 (98491190550467 / 12500) (19698319462111 / 2500) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880831232 33 20 (142423 / 6250)
        (2278771 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880831232 7880864000 88774 _ _ (142423 / 6250) (891283 / 50000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880831232 7880864000 12 1428 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880864000 :
    ThetaLowerSegment 7880864000 7880896768 (19698319462111 / 2500) (787936167013943 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880864000 33 20 (2278769 / 100000)
        (569693 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880864000 7880896768 88774 _ _ (2278769 / 100000) (1782567 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880864000 7880896768 12 1487 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880896768 :
    ThetaLowerSegment 7880896768 7880929536 (787936167013943 / 100000) (24623109544079 / 3125) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880896768 33 20 (2278769 / 100000)
        (569693 / 25000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880896768 7880929536 88774 _ _ (2278769 / 100000) (1782567 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880896768 7880929536 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880929536 :
    ThetaLowerSegment 7880929536 7880962304 (24623109544079 / 3125) (393971426461829 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880929536 33 20 (227877 / 10000)
        (2278773 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880929536 7880962304 88774 _ _ (227877 / 10000) (1782569 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880929536 7880962304 12 1469 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880962304 :
    ThetaLowerSegment 7880962304 7880995072 (393971426461829 / 50000)
      (393973044388529 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880962304 33 20 (227877 / 10000)
        (2278773 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880962304 7880995072 88774 _ _ (227877 / 10000) (1782569 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880962304 7880995072 12 1420 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7880995072 :
    ThetaLowerSegment 7880995072 7881027840 (393973044388529 / 50000)
      (787949299565397 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7880995072 33 20 (2278771 / 100000)
        (1139387 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7880995072 7881027840 88774 _ _ (2278771 / 100000) (1782571 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7880995072 7881027840 12 1409 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881027840 :
    ThetaLowerSegment 7881027840 7881060608 (787949299565397 / 100000)
      (787952571880553 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881027840 33 20 (2278771 / 100000)
        (1139387 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881027840 7881060608 88775 _ _ (2278771 / 100000) (1782571 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881027840 7881060608 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881060608 :
    ThetaLowerSegment 7881060608 7881093376 (787952571880553 / 100000) (9849448080931 / 1250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881060608 33 20 (2278771 / 100000)
        (1139387 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881060608 7881093376 88775 _ _ (2278771 / 100000) (1782571 / 100000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881060608 7881093376 12 1437 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881093376 :
    ThetaLowerSegment 7881093376 7881126144 (9849448080931 / 1250) (39397959243773 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881093376 33 20 (569693 / 25000) (91151 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881093376 7881126144 88775 _ _ (569693 / 25000) (445643 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881093376 7881126144 12 1465 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881126144 :
    ThetaLowerSegment 7881126144 7881158912 (39397959243773 / 5000) (39398123315357 / 5000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881126144 33 20 (569693 / 25000) (91151 / 4000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881126144 7881158912 88775 _ _ (569693 / 25000) (445643 / 25000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881126144 7881158912 12 1440 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881158912 :
    ThetaLowerSegment 7881158912 7881191680 (39398123315357 / 5000) (49247858664073 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881158912 33 20 (2278773 / 100000)
        (284847 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881158912 7881191680 88775 _ _ (2278773 / 100000) (891287 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881158912 7881191680 12 1436 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881191680 :
    ThetaLowerSegment 7881191680 7881224448 (49247858664073 / 6250) (7879691203243 / 1000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881191680 33 20 (2278773 / 100000)
        (284847 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881191680 7881224448 88776 _ _ (2278773 / 100000) (891287 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881191680 7881224448 12 1484 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881224448 :
    ThetaLowerSegment 7881224448 7881257216 (7879691203243 / 1000) (196993114111993 / 25000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881224448 33 20 (2278773 / 100000)
        (284847 / 12500) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881224448 7881257216 88776 _ _ (2278773 / 100000) (891287 / 50000)
      (by decide) (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881224448 7881257216 12 1464 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881257216 :
    ThetaLowerSegment 7881257216 7881289984 (196993114111993 / 25000) (49248477066183 / 6250) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881257216 33 20 (1139387 / 50000)
        (2278777 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881257216 7881289984 88776 _ _ (1139387 / 50000) (111411 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881257216 7881289984 12 1394 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881289984 :
    ThetaLowerSegment 7881289984 7881322752 (49248477066183 / 6250) (393989424204521 / 50000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881289984 33 20 (1139387 / 50000)
        (2278777 / 100000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881289984 7881322752 88776 _ _ (1139387 / 50000) (111411 / 6250) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881289984 7881322752 12 1411 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881322752 :
    ThetaLowerSegment 7881322752 7881339136 (393989424204521 / 50000)
      (787980473175617 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881322752 33 20 (91151 / 4000)
        (1139389 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881322752 7881339136 88776 _ _ (91151 / 4000) (1782577 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881322752 7881339136 11 713 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

private theorem cell7881339136 :
    ThetaLowerSegment 7881339136 7881341184 (787980473175617 / 100000)
      (787980696495567 / 100000) := by
  have hl :
    PseudoPrime.Analysis.rationalLogIntervalCheck 7881339136 33 20 (91151 / 4000)
        (1139389 / 50000) =
      true := by
    decide +kernel
  apply
    theta_restart_cell 7881339136 7881341184 88776 _ _ (91151 / 4000) (1782577 / 100000) (by decide)
      (by decide)
      (by
        simpa only [Rat.cast_ofNat, Nat.cast_ofNat] using
          (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact
    theta_restart_gain 7881339136 7881341184 8 98 33 _ _ _ _ (by decide) (by decide) (by decide)
      (by decide +kernel) hl (by decide +kernel)

/-- This window supplies its exit bound and covers its real interval from a scalar entrance. -/
public theorem gap_window_7881341184 :
    ThetaLowerSegment 7849341184 7881341184 (784782495993077 / 100000)
      (787980696495567 / 100000) := by
  exact
    ((((((((((cell7849341184.join cell7849373952).join (cell7849406720.join cell7849439488)).join
                                  ((cell7849472256.join cell7849505024).join
                                    (cell7849537792.join cell7849570560))).join
                              (((cell7849603328.join cell7849636096).join
                                    (cell7849668864.join cell7849701632)).join
                                ((cell7849734400.join cell7849767168).join
                                  (cell7849799936.join cell7849832704)))).join
                          ((((cell7849865472.join cell7849898240).join
                                    (cell7849931008.join cell7849963776)).join
                                ((cell7849996544.join cell7850029312).join
                                  (cell7850062080.join cell7850094848))).join
                            (((cell7850127616.join cell7850160384).join
                                  (cell7850193152.join cell7850225920)).join
                              ((cell7850258688.join cell7850291456).join
                                (cell7850324224.join cell7850356992))))).join
                      (((((cell7850389760.join cell7850422528).join
                                    (cell7850455296.join cell7850488064)).join
                                ((cell7850520832.join cell7850553600).join
                                  (cell7850586368.join cell7850619136))).join
                            (((cell7850651904.join cell7850684672).join
                                  (cell7850717440.join cell7850750208)).join
                              ((cell7850782976.join cell7850815744).join
                                (cell7850848512.join cell7850881280)))).join
                        ((((cell7850914048.join cell7850946816).join
                                  (cell7850979584.join cell7851012352)).join
                              ((cell7851045120.join cell7851077888).join
                                (cell7851110656.join cell7851143424))).join
                          (((cell7851176192.join cell7851208960).join
                                (cell7851241728.join cell7851274496)).join
                            ((cell7851307264.join cell7851340032).join
                              (cell7851372800.join cell7851405568)))))).join
                  ((((((cell7851438336.join cell7851471104).join
                                    (cell7851503872.join cell7851536640)).join
                                ((cell7851569408.join cell7851602176).join
                                  (cell7851634944.join cell7851667712))).join
                            (((cell7851700480.join cell7851733248).join
                                  (cell7851766016.join cell7851798784)).join
                              ((cell7851831552.join cell7851864320).join
                                (cell7851897088.join cell7851929856)))).join
                        ((((cell7851962624.join cell7851995392).join
                                  (cell7852028160.join cell7852060928)).join
                              ((cell7852093696.join cell7852126464).join
                                (cell7852159232.join cell7852192000))).join
                          (((cell7852224768.join cell7852257536).join
                                (cell7852290304.join cell7852323072)).join
                            ((cell7852355840.join cell7852388608).join
                              (cell7852421376.join cell7852454144))))).join
                    (((((cell7852486912.join cell7852519680).join
                                  (cell7852552448.join cell7852585216)).join
                              ((cell7852617984.join cell7852650752).join
                                (cell7852683520.join cell7852716288))).join
                          (((cell7852749056.join cell7852781824).join
                                (cell7852814592.join cell7852847360)).join
                            ((cell7852880128.join cell7852912896).join
                              (cell7852945664.join cell7852978432)))).join
                      ((((cell7853011200.join cell7853043968).join
                                (cell7853076736.join cell7853109504)).join
                            ((cell7853142272.join cell7853175040).join
                              (cell7853207808.join cell7853240576))).join
                        (((cell7853273344.join cell7853306112).join
                              (cell7853338880.join cell7853371648)).join
                          ((cell7853404416.join cell7853437184).join
                            (cell7853469952.join cell7853502720))))))).join
              (((((((cell7853535488.join cell7853568256).join
                                    (cell7853601024.join cell7853633792)).join
                                ((cell7853666560.join cell7853699328).join
                                  (cell7853732096.join cell7853764864))).join
                            (((cell7853797632.join cell7853830400).join
                                  (cell7853863168.join cell7853895936)).join
                              ((cell7853928704.join cell7853961472).join
                                (cell7853994240.join cell7854027008)))).join
                        ((((cell7854059776.join cell7854092544).join
                                  (cell7854125312.join cell7854158080)).join
                              ((cell7854190848.join cell7854223616).join
                                (cell7854256384.join cell7854289152))).join
                          (((cell7854321920.join cell7854354688).join
                                (cell7854387456.join cell7854420224)).join
                            ((cell7854452992.join cell7854485760).join
                              (cell7854518528.join cell7854551296))))).join
                    (((((cell7854584064.join cell7854616832).join
                                  (cell7854649600.join cell7854682368)).join
                              ((cell7854715136.join cell7854747904).join
                                (cell7854780672.join cell7854813440))).join
                          (((cell7854846208.join cell7854878976).join
                                (cell7854911744.join cell7854944512)).join
                            ((cell7854977280.join cell7855010048).join
                              (cell7855042816.join cell7855075584)))).join
                      ((((cell7855108352.join cell7855141120).join
                                (cell7855173888.join cell7855206656)).join
                            ((cell7855239424.join cell7855272192).join
                              (cell7855304960.join cell7855337728))).join
                        (((cell7855370496.join cell7855403264).join
                              (cell7855436032.join cell7855468800)).join
                          ((cell7855501568.join cell7855534336).join
                            (cell7855567104.join cell7855599872)))))).join
                ((((((cell7855632640.join cell7855665408).join
                                  (cell7855698176.join cell7855730944)).join
                              ((cell7855763712.join cell7855796480).join
                                (cell7855829248.join cell7855862016))).join
                          (((cell7855894784.join cell7855927552).join
                                (cell7855960320.join cell7855993088)).join
                            ((cell7856025856.join cell7856058624).join
                              (cell7856091392.join cell7856124160)))).join
                      ((((cell7856156928.join cell7856189696).join
                                (cell7856222464.join cell7856255232)).join
                            ((cell7856288000.join cell7856320768).join
                              (cell7856353536.join cell7856386304))).join
                        (((cell7856419072.join cell7856451840).join
                              (cell7856484608.join cell7856517376)).join
                          ((cell7856550144.join cell7856582912).join
                            (cell7856615680.join cell7856648448))))).join
                  (((((cell7856681216.join cell7856713984).join
                                (cell7856746752.join cell7856779520)).join
                            ((cell7856812288.join cell7856845056).join
                              (cell7856877824.join cell7856910592))).join
                        (((cell7856943360.join cell7856976128).join
                              (cell7857008896.join cell7857041664)).join
                          ((cell7857074432.join cell7857107200).join
                            (cell7857139968.join cell7857172736)))).join
                    ((((cell7857205504.join cell7857238272).join
                              (cell7857271040.join cell7857303808)).join
                          ((cell7857336576.join cell7857369344).join
                            (cell7857402112.join cell7857434880))).join
                      (((cell7857467648.join cell7857500416).join
                            (cell7857533184.join cell7857565952)).join
                        ((cell7857598720.join cell7857631488).join
                          (cell7857664256.join cell7857697024)))))))).join
          ((((((((cell7857729792.join cell7857762560).join
                                    (cell7857795328.join cell7857828096)).join
                                ((cell7857860864.join cell7857893632).join
                                  (cell7857926400.join cell7857959168))).join
                            (((cell7857991936.join cell7858024704).join
                                  (cell7858057472.join cell7858090240)).join
                              ((cell7858123008.join cell7858155776).join
                                (cell7858188544.join cell7858221312)))).join
                        ((((cell7858254080.join cell7858286848).join
                                  (cell7858319616.join cell7858352384)).join
                              ((cell7858385152.join cell7858417920).join
                                (cell7858450688.join cell7858483456))).join
                          (((cell7858516224.join cell7858548992).join
                                (cell7858581760.join cell7858614528)).join
                            ((cell7858647296.join cell7858680064).join
                              (cell7858712832.join cell7858745600))))).join
                    (((((cell7858778368.join cell7858811136).join
                                  (cell7858843904.join cell7858876672)).join
                              ((cell7858909440.join cell7858942208).join
                                (cell7858974976.join cell7859007744))).join
                          (((cell7859040512.join cell7859073280).join
                                (cell7859106048.join cell7859138816)).join
                            ((cell7859171584.join cell7859204352).join
                              (cell7859237120.join cell7859269888)))).join
                      ((((cell7859302656.join cell7859335424).join
                                (cell7859368192.join cell7859400960)).join
                            ((cell7859433728.join cell7859466496).join
                              (cell7859499264.join cell7859532032))).join
                        (((cell7859564800.join cell7859597568).join
                              (cell7859630336.join cell7859663104)).join
                          ((cell7859695872.join cell7859728640).join
                            (cell7859761408.join cell7859794176)))))).join
                ((((((cell7859826944.join cell7859859712).join
                                  (cell7859892480.join cell7859925248)).join
                              ((cell7859958016.join cell7859990784).join
                                (cell7860023552.join cell7860056320))).join
                          (((cell7860089088.join cell7860121856).join
                                (cell7860154624.join cell7860187392)).join
                            ((cell7860220160.join cell7860252928).join
                              (cell7860285696.join cell7860318464)))).join
                      ((((cell7860351232.join cell7860384000).join
                                (cell7860416768.join cell7860449536)).join
                            ((cell7860482304.join cell7860515072).join
                              (cell7860547840.join cell7860580608))).join
                        (((cell7860613376.join cell7860646144).join
                              (cell7860678912.join cell7860711680)).join
                          ((cell7860744448.join cell7860777216).join
                            (cell7860809984.join cell7860842752))))).join
                  (((((cell7860875520.join cell7860908288).join
                                (cell7860941056.join cell7860973824)).join
                            ((cell7861006592.join cell7861039360).join
                              (cell7861072128.join cell7861104896))).join
                        (((cell7861137664.join cell7861170432).join
                              (cell7861203200.join cell7861235968)).join
                          ((cell7861268736.join cell7861301504).join
                            (cell7861334272.join cell7861367040)))).join
                    ((((cell7861399808.join cell7861432576).join
                              (cell7861465344.join cell7861498112)).join
                          ((cell7861530880.join cell7861563648).join
                            (cell7861596416.join cell7861629184))).join
                      (((cell7861661952.join cell7861694720).join
                            (cell7861727488.join cell7861760256)).join
                        ((cell7861793024.join cell7861825792).join
                          (cell7861858560.join cell7861891328))))))).join
            (((((((cell7861924096.join cell7861956864).join
                                  (cell7861989632.join cell7862022400)).join
                              ((cell7862055168.join cell7862087936).join
                                (cell7862120704.join cell7862153472))).join
                          (((cell7862186240.join cell7862219008).join
                                (cell7862251776.join cell7862284544)).join
                            ((cell7862317312.join cell7862350080).join
                              (cell7862382848.join cell7862415616)))).join
                      ((((cell7862448384.join cell7862481152).join
                                (cell7862513920.join cell7862546688)).join
                            ((cell7862579456.join cell7862612224).join
                              (cell7862644992.join cell7862677760))).join
                        (((cell7862710528.join cell7862743296).join
                              (cell7862776064.join cell7862808832)).join
                          ((cell7862841600.join cell7862874368).join
                            (cell7862907136.join cell7862939904))))).join
                  (((((cell7862972672.join cell7863005440).join
                                (cell7863038208.join cell7863070976)).join
                            ((cell7863103744.join cell7863136512).join
                              (cell7863169280.join cell7863202048))).join
                        (((cell7863234816.join cell7863267584).join
                              (cell7863300352.join cell7863333120)).join
                          ((cell7863365888.join cell7863398656).join
                            (cell7863431424.join cell7863464192)))).join
                    ((((cell7863496960.join cell7863529728).join
                              (cell7863562496.join cell7863595264)).join
                          ((cell7863628032.join cell7863660800).join
                            (cell7863693568.join cell7863726336))).join
                      (((cell7863759104.join cell7863791872).join
                            (cell7863824640.join cell7863857408)).join
                        ((cell7863890176.join cell7863922944).join
                          (cell7863955712.join cell7863988480)))))).join
              ((((((cell7864021248.join cell7864054016).join
                                (cell7864086784.join cell7864119552)).join
                            ((cell7864152320.join cell7864185088).join
                              (cell7864217856.join cell7864250624))).join
                        (((cell7864283392.join cell7864316160).join
                              (cell7864348928.join cell7864381696)).join
                          ((cell7864414464.join cell7864447232).join
                            (cell7864480000.join cell7864512768)))).join
                    ((((cell7864545536.join cell7864578304).join
                              (cell7864611072.join cell7864643840)).join
                          ((cell7864676608.join cell7864709376).join
                            (cell7864742144.join cell7864774912))).join
                      (((cell7864807680.join cell7864840448).join
                            (cell7864873216.join cell7864905984)).join
                        ((cell7864938752.join cell7864971520).join
                          (cell7865004288.join cell7865037056))))).join
                (((((cell7865069824.join cell7865102592).join
                              (cell7865135360.join cell7865168128)).join
                          ((cell7865200896.join cell7865233664).join
                            (cell7865266432.join cell7865299200))).join
                      (((cell7865331968.join cell7865364736).join
                            (cell7865397504.join cell7865430272)).join
                        ((cell7865463040.join cell7865495808).join
                          (cell7865528576.join cell7865561344)))).join
                  ((((cell7865594112.join cell7865626880).join
                            (cell7865659648.join cell7865692416)).join
                        ((cell7865725184.join cell7865757952).join
                          (cell7865790720.join cell7865823488))).join
                    (((cell7865856256.join cell7865889024).join
                          (cell7865921792.join cell7865954560)).join
                      ((cell7865987328.join cell7866020096).join
                        (cell7866052864.join cell7866085632))))))))).join
      (((((((((cell7866118400.join cell7866151168).join (cell7866183936.join cell7866216704)).join
                                ((cell7866249472.join cell7866282240).join
                                  (cell7866315008.join cell7866347776))).join
                            (((cell7866380544.join cell7866413312).join
                                  (cell7866446080.join cell7866478848)).join
                              ((cell7866511616.join cell7866544384).join
                                (cell7866577152.join cell7866609920)))).join
                        ((((cell7866642688.join cell7866675456).join
                                  (cell7866708224.join cell7866740992)).join
                              ((cell7866773760.join cell7866806528).join
                                (cell7866839296.join cell7866872064))).join
                          (((cell7866904832.join cell7866937600).join
                                (cell7866970368.join cell7867003136)).join
                            ((cell7867035904.join cell7867068672).join
                              (cell7867101440.join cell7867134208))))).join
                    (((((cell7867166976.join cell7867199744).join
                                  (cell7867232512.join cell7867265280)).join
                              ((cell7867298048.join cell7867330816).join
                                (cell7867363584.join cell7867396352))).join
                          (((cell7867429120.join cell7867461888).join
                                (cell7867494656.join cell7867527424)).join
                            ((cell7867560192.join cell7867592960).join
                              (cell7867625728.join cell7867658496)))).join
                      ((((cell7867691264.join cell7867724032).join
                                (cell7867756800.join cell7867789568)).join
                            ((cell7867822336.join cell7867855104).join
                              (cell7867887872.join cell7867920640))).join
                        (((cell7867953408.join cell7867986176).join
                              (cell7868018944.join cell7868051712)).join
                          ((cell7868084480.join cell7868117248).join
                            (cell7868150016.join cell7868182784)))))).join
                ((((((cell7868215552.join cell7868248320).join
                                  (cell7868281088.join cell7868313856)).join
                              ((cell7868346624.join cell7868379392).join
                                (cell7868412160.join cell7868444928))).join
                          (((cell7868477696.join cell7868510464).join
                                (cell7868543232.join cell7868576000)).join
                            ((cell7868608768.join cell7868641536).join
                              (cell7868674304.join cell7868707072)))).join
                      ((((cell7868739840.join cell7868772608).join
                                (cell7868805376.join cell7868838144)).join
                            ((cell7868870912.join cell7868903680).join
                              (cell7868936448.join cell7868969216))).join
                        (((cell7869001984.join cell7869034752).join
                              (cell7869067520.join cell7869100288)).join
                          ((cell7869133056.join cell7869165824).join
                            (cell7869198592.join cell7869231360))))).join
                  (((((cell7869264128.join cell7869296896).join
                                (cell7869329664.join cell7869362432)).join
                            ((cell7869395200.join cell7869427968).join
                              (cell7869460736.join cell7869493504))).join
                        (((cell7869526272.join cell7869559040).join
                              (cell7869591808.join cell7869624576)).join
                          ((cell7869657344.join cell7869690112).join
                            (cell7869722880.join cell7869755648)))).join
                    ((((cell7869788416.join cell7869821184).join
                              (cell7869853952.join cell7869886720)).join
                          ((cell7869919488.join cell7869952256).join
                            (cell7869985024.join cell7870017792))).join
                      (((cell7870050560.join cell7870083328).join
                            (cell7870116096.join cell7870148864)).join
                        ((cell7870181632.join cell7870214400).join
                          (cell7870247168.join cell7870279936))))))).join
            (((((((cell7870312704.join cell7870345472).join
                                  (cell7870378240.join cell7870411008)).join
                              ((cell7870443776.join cell7870476544).join
                                (cell7870509312.join cell7870542080))).join
                          (((cell7870574848.join cell7870607616).join
                                (cell7870640384.join cell7870673152)).join
                            ((cell7870705920.join cell7870738688).join
                              (cell7870771456.join cell7870804224)))).join
                      ((((cell7870836992.join cell7870869760).join
                                (cell7870902528.join cell7870935296)).join
                            ((cell7870968064.join cell7871000832).join
                              (cell7871033600.join cell7871066368))).join
                        (((cell7871099136.join cell7871131904).join
                              (cell7871164672.join cell7871197440)).join
                          ((cell7871230208.join cell7871262976).join
                            (cell7871295744.join cell7871328512))))).join
                  (((((cell7871361280.join cell7871394048).join
                                (cell7871426816.join cell7871459584)).join
                            ((cell7871492352.join cell7871525120).join
                              (cell7871557888.join cell7871590656))).join
                        (((cell7871623424.join cell7871656192).join
                              (cell7871688960.join cell7871721728)).join
                          ((cell7871754496.join cell7871787264).join
                            (cell7871820032.join cell7871852800)))).join
                    ((((cell7871885568.join cell7871918336).join
                              (cell7871951104.join cell7871983872)).join
                          ((cell7872016640.join cell7872049408).join
                            (cell7872082176.join cell7872114944))).join
                      (((cell7872147712.join cell7872180480).join
                            (cell7872213248.join cell7872246016)).join
                        ((cell7872278784.join cell7872311552).join
                          (cell7872344320.join cell7872377088)))))).join
              ((((((cell7872409856.join cell7872442624).join
                                (cell7872475392.join cell7872508160)).join
                            ((cell7872540928.join cell7872573696).join
                              (cell7872606464.join cell7872639232))).join
                        (((cell7872672000.join cell7872704768).join
                              (cell7872737536.join cell7872770304)).join
                          ((cell7872803072.join cell7872835840).join
                            (cell7872868608.join cell7872901376)))).join
                    ((((cell7872934144.join cell7872966912).join
                              (cell7872999680.join cell7873032448)).join
                          ((cell7873065216.join cell7873097984).join
                            (cell7873130752.join cell7873163520))).join
                      (((cell7873196288.join cell7873229056).join
                            (cell7873261824.join cell7873294592)).join
                        ((cell7873327360.join cell7873360128).join
                          (cell7873392896.join cell7873425664))))).join
                (((((cell7873458432.join cell7873491200).join
                              (cell7873523968.join cell7873556736)).join
                          ((cell7873589504.join cell7873622272).join
                            (cell7873655040.join cell7873687808))).join
                      (((cell7873720576.join cell7873753344).join
                            (cell7873786112.join cell7873818880)).join
                        ((cell7873851648.join cell7873884416).join
                          (cell7873917184.join cell7873949952)))).join
                  ((((cell7873982720.join cell7874015488).join
                            (cell7874048256.join cell7874081024)).join
                        ((cell7874113792.join cell7874146560).join
                          (cell7874179328.join cell7874212096))).join
                    (((cell7874244864.join cell7874277632).join
                          (cell7874310400.join cell7874343168)).join
                      ((cell7874375936.join cell7874408704).join
                        (cell7874441472.join cell7874474240)))))))).join
        ((((((((cell7874507008.join cell7874539776).join (cell7874572544.join cell7874605312)).join
                              ((cell7874638080.join cell7874670848).join
                                (cell7874703616.join cell7874736384))).join
                          (((cell7874769152.join cell7874801920).join
                                (cell7874834688.join cell7874867456)).join
                            ((cell7874900224.join cell7874932992).join
                              (cell7874965760.join cell7874998528)))).join
                      ((((cell7875031296.join cell7875064064).join
                                (cell7875096832.join cell7875129600)).join
                            ((cell7875162368.join cell7875195136).join
                              (cell7875227904.join cell7875260672))).join
                        (((cell7875293440.join cell7875326208).join
                              (cell7875358976.join cell7875391744)).join
                          ((cell7875424512.join cell7875457280).join
                            (cell7875490048.join cell7875522816))))).join
                  (((((cell7875555584.join cell7875588352).join
                                (cell7875621120.join cell7875653888)).join
                            ((cell7875686656.join cell7875719424).join
                              (cell7875752192.join cell7875784960))).join
                        (((cell7875817728.join cell7875850496).join
                              (cell7875883264.join cell7875916032)).join
                          ((cell7875948800.join cell7875981568).join
                            (cell7876014336.join cell7876047104)))).join
                    ((((cell7876079872.join cell7876112640).join
                              (cell7876145408.join cell7876178176)).join
                          ((cell7876210944.join cell7876243712).join
                            (cell7876276480.join cell7876309248))).join
                      (((cell7876342016.join cell7876374784).join
                            (cell7876407552.join cell7876440320)).join
                        ((cell7876473088.join cell7876505856).join
                          (cell7876538624.join cell7876571392)))))).join
              ((((((cell7876604160.join cell7876636928).join
                                (cell7876669696.join cell7876702464)).join
                            ((cell7876735232.join cell7876768000).join
                              (cell7876800768.join cell7876833536))).join
                        (((cell7876866304.join cell7876899072).join
                              (cell7876931840.join cell7876964608)).join
                          ((cell7876997376.join cell7877030144).join
                            (cell7877062912.join cell7877095680)))).join
                    ((((cell7877128448.join cell7877161216).join
                              (cell7877193984.join cell7877226752)).join
                          ((cell7877259520.join cell7877292288).join
                            (cell7877325056.join cell7877357824))).join
                      (((cell7877390592.join cell7877423360).join
                            (cell7877456128.join cell7877488896)).join
                        ((cell7877521664.join cell7877554432).join
                          (cell7877587200.join cell7877619968))))).join
                (((((cell7877652736.join cell7877685504).join
                              (cell7877718272.join cell7877751040)).join
                          ((cell7877783808.join cell7877816576).join
                            (cell7877849344.join cell7877882112))).join
                      (((cell7877914880.join cell7877947648).join
                            (cell7877980416.join cell7878013184)).join
                        ((cell7878045952.join cell7878078720).join
                          (cell7878111488.join cell7878144256)))).join
                  ((((cell7878177024.join cell7878209792).join
                            (cell7878242560.join cell7878275328)).join
                        ((cell7878308096.join cell7878340864).join
                          (cell7878373632.join cell7878406400))).join
                    (((cell7878439168.join cell7878471936).join
                          (cell7878504704.join cell7878537472)).join
                      ((cell7878570240.join cell7878603008).join
                        (cell7878635776.join cell7878668544))))))).join
          (((((((cell7878701312.join cell7878734080).join (cell7878766848.join cell7878799616)).join
                            ((cell7878832384.join cell7878865152).join
                              (cell7878897920.join cell7878930688))).join
                        (((cell7878963456.join cell7878996224).join
                              (cell7879028992.join cell7879061760)).join
                          ((cell7879094528.join cell7879127296).join
                            (cell7879160064.join cell7879192832)))).join
                    ((((cell7879225600.join cell7879258368).join
                              (cell7879291136.join cell7879323904)).join
                          ((cell7879356672.join cell7879389440).join
                            (cell7879422208.join cell7879454976))).join
                      (((cell7879487744.join cell7879520512).join
                            (cell7879553280.join cell7879586048)).join
                        ((cell7879618816.join cell7879651584).join
                          (cell7879684352.join cell7879717120))))).join
                (((((cell7879749888.join cell7879782656).join
                              (cell7879815424.join cell7879848192)).join
                          ((cell7879880960.join cell7879913728).join
                            (cell7879946496.join cell7879979264))).join
                      (((cell7880012032.join cell7880044800).join
                            (cell7880077568.join cell7880110336)).join
                        ((cell7880143104.join cell7880175872).join
                          (cell7880208640.join cell7880241408)))).join
                  ((((cell7880274176.join cell7880306944).join
                            (cell7880339712.join cell7880372480)).join
                        ((cell7880405248.join cell7880438016).join
                          (cell7880470784.join cell7880503552))).join
                    (((cell7880536320.join cell7880569088).join
                          (cell7880601856.join cell7880634624)).join
                      ((cell7880667392.join cell7880700160).join
                        (cell7880732928.join cell7880765696)))))).join
            (((((cell7880798464.join cell7880831232).join (cell7880864000.join cell7880896768)).join
                      ((cell7880929536.join cell7880962304).join
                        (cell7880995072.join cell7881027840))).join
                  (((cell7881060608.join cell7881093376).join
                        (cell7881126144.join cell7881158912)).join
                    ((cell7881191680.join cell7881224448).join
                      (cell7881257216.join cell7881289984)))).join
              (cell7881322752.join cell7881339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
