/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7498389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466651904
    (h : (((93311287231993 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7466389760) :
    (((4665727418776 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7466651904 := by
  exact
    theta_restart_gain 7466389760 7466651904 15 11476 33 (93311287231993 / 12500)
      (4665727418776 / 625) (1136683 / 50000) (2273369 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466914048
    (h : (((4665727418776 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7466651904) :
    (((4665891328753 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7466914048 := by
  exact
    theta_restart_gain 7466651904 7466914048 15 11536 33 (4665727418776 / 625) (4665891328753 / 625)
      (227337 / 10000) (2273373 / 100000) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7467176192
    (h : (((4665891328753 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7466914048) :
    (((37328446912991 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467176192 := by
  exact
    theta_restart_gain 7466914048 7467176192 15 11580 33 (4665891328753 / 625)
      (37328446912991 / 5000) (2273373 / 100000) (71043 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7467438336
    (h : (((37328446912991 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467176192) :
    (((93324403448931 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7467438336 := by
  exact
    theta_restart_gain 7467176192 7467438336 15 11564 33 (37328446912991 / 5000)
      (93324403448931 / 12500) (2273377 / 100000) (113669 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7467700480
    (h : (((93324403448931 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7467438336) :
    (((186655417318557 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467700480 := by
  exact
    theta_restart_gain 7467438336 7467700480 15 11631 33 (93324403448931 / 12500)
      (186655417318557 / 25000) (113669 / 5000) (2273383 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7467962624
    (h : (((186655417318557 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467700480) :
    (((186661980009819 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467962624 := by
  exact
    theta_restart_gain 7467700480 7467962624 15 11547 33 (186655417318557 / 25000)
      (186661980009819 / 25000) (284173 / 12500) (2273387 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7468224768
    (h : (((186661980009819 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7467962624) :
    (((74667415947203 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468224768 := by
  exact
    theta_restart_gain 7467962624 7468224768 15 11542 33 (186661980009819 / 25000)
      (74667415947203 / 10000) (2273387 / 100000) (227339 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7468486912
    (h : (((74667415947203 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468224768) :
    (((373350297231289 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468486912 := by
  exact
    theta_restart_gain 7468224768 7468486912 15 11628 33 (74667415947203 / 10000)
      (373350297231289 / 50000) (2273391 / 100000) (1136697 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7468749056
    (h : (((373350297231289 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468486912) :
    (((373363398800911 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468749056 := by
  exact
    theta_restart_gain 7468486912 7468749056 15 11526 33 (373350297231289 / 50000)
      (373363398800911 / 50000) (1136697 / 50000) (2273397 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7469011200
    (h : (((373363398800911 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7468749056) :
    (((373376589056107 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469011200 := by
  exact
    theta_restart_gain 7468749056 7469011200 15 11604 33 (373363398800911 / 50000)
      (373376589056107 / 50000) (1136699 / 50000) (2273401 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7469273344
    (h : (((373376589056107 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469011200) :
    (((746779151718639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469273344 := by
  exact
    theta_restart_gain 7469011200 7469273344 15 11425 33 (373376589056107 / 50000)
      (746779151718639 / 100000) (2273401 / 100000) (568351 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7469535488
    (h : (((746779151718639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469273344) :
    (((373402751377997 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469535488 := by
  exact
    theta_restart_gain 7469273344 7469535488 15 11591 33 (746779151718639 / 100000)
      (373402751377997 / 50000) (454681 / 20000) (71044 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7469797632
    (h : (((373402751377997 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469535488) :
    (((373415765502093 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469797632 := by
  exact
    theta_restart_gain 7469535488 7469797632 15 11449 33 (373402751377997 / 50000)
      (373415765502093 / 50000) (71044 / 3125) (2273411 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7470059776
    (h : (((373415765502093 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7469797632) :
    (((373428780785793 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470059776 := by
  exact
    theta_restart_gain 7469797632 7470059776 15 11450 33 (373415765502093 / 50000)
      (373428780785793 / 50000) (568353 / 25000) (454683 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7470321920
    (h : (((373428780785793 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470059776) :
    (((746883885443871 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470321920 := by
  exact
    theta_restart_gain 7470059776 7470321920 15 11579 33 (373428780785793 / 50000)
      (746883885443871 / 100000) (454683 / 20000) (1136709 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7470584064
    (h : (((746883885443871 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470321920) :
    (((746910016121857 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470584064 := by
  exact
    theta_restart_gain 7470321920 7470584064 15 11494 33 (746883885443871 / 100000)
      (746910016121857 / 100000) (2273419 / 100000) (1136711 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7470846208
    (h : (((746910016121857 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470584064) :
    (((746935983147941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470846208 := by
  exact
    theta_restart_gain 7470584064 7470846208 15 11422 33 (746910016121857 / 100000)
      (746935983147941 / 100000) (1136711 / 50000) (90937 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7471108352
    (h : (((746935983147941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7470846208) :
    (((746961979774251 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471108352 := by
  exact
    theta_restart_gain 7470846208 7471108352 15 11435 33 (746935983147941 / 100000)
      (746961979774251 / 100000) (1136713 / 50000) (2273429 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7471370496
    (h : (((746961979774251 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471108352) :
    (((746987960520863 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471370496 := by
  exact
    theta_restart_gain 7471108352 7471370496 15 11428 33 (746961979774251 / 100000)
      (746987960520863 / 100000) (2273429 / 100000) (284179 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7471632640
    (h : (((746987960520863 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471370496) :
    (((373507133207053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471632640 := by
  exact
    theta_restart_gain 7471370496 7471632640 15 11571 33 (746987960520863 / 100000)
      (373507133207053 / 50000) (2273433 / 100000) (568359 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7471894784
    (h : (((373507133207053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471632640) :
    (((373520262299953 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471894784 := by
  exact
    theta_restart_gain 7471632640 7471894784 15 11550 33 (373507133207053 / 50000)
      (373520262299953 / 50000) (568359 / 25000) (2273439 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7472156928
    (h : (((373520262299953 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7471894784) :
    (((373533318665873 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472156928 := by
  exact
    theta_restart_gain 7471894784 7472156928 15 11486 33 (373520262299953 / 50000)
      (373533318665873 / 50000) (14209 / 625) (2273443 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7472419072
    (h : (((373533318665873 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472156928) :
    (((747092725090171 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472419072 := by
  exact
    theta_restart_gain 7472156928 7472419072 15 11475 33 (373533318665873 / 50000)
      (747092725090171 / 100000) (2273443 / 100000) (1136723 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7472681216
    (h : (((747092725090171 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472419072) :
    (((747118892465141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472681216 := by
  exact
    theta_restart_gain 7472419072 7472681216 15 11510 33 (747092725090171 / 100000)
      (747118892465141 / 100000) (2273447 / 100000) (45469 / 2000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7472943360
    (h : (((747118892465141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472681216) :
    (((747144975756991 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472943360 := by
  exact
    theta_restart_gain 7472681216 7472943360 15 11473 33 (747118892465141 / 100000)
      (747144975756991 / 100000) (45469 / 2000) (2273453 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7473205504
    (h : (((747144975756991 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7472943360) :
    (((747171220509967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473205504 := by
  exact
    theta_restart_gain 7472943360 7473205504 15 11544 33 (747144975756991 / 100000)
      (747171220509967 / 100000) (1136727 / 50000) (2273457 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7473467648
    (h : (((747171220509967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473205504) :
    (((747197165201251 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473467648 := by
  exact
    theta_restart_gain 7473205504 7473467648 15 11412 33 (747171220509967 / 100000)
      (747197165201251 / 100000) (2273457 / 100000) (113673 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7473729792
    (h : (((747197165201251 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473467648) :
    (((747223337284283 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473729792 := by
  exact
    theta_restart_gain 7473467648 7473729792 15 11512 33 (747197165201251 / 100000)
      (747223337284283 / 100000) (2273461 / 100000) (284183 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7473991936
    (h : (((747223337284283 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473729792) :
    (((373624821773899 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473991936 := by
  exact
    theta_restart_gain 7473729792 7473991936 15 11571 33 (747223337284283 / 100000)
      (373624821773899 / 50000) (454693 / 20000) (568367 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7474254080
    (h : (((373624821773899 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7473991936) :
    (((373637873753687 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474254080 := by
  exact
    theta_restart_gain 7473991936 7474254080 15 11482 33 (373624821773899 / 50000)
      (373637873753687 / 50000) (568367 / 25000) (2273471 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7474516224
    (h : (((373637873753687 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474254080) :
    (((373650980319767 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474516224 := by
  exact
    theta_restart_gain 7474254080 7474516224 15 11530 33 (373637873753687 / 50000)
      (373650980319767 / 50000) (71046 / 3125) (90939 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7474778368
    (h : (((373650980319767 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474516224) :
    (((747328148798059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474778368 := by
  exact
    theta_restart_gain 7474516224 7474778368 15 11519 33 (373650980319767 / 50000)
      (747328148798059 / 100000) (90939 / 4000) (1136739 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7475040512
    (h : (((747328148798059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7474778368) :
    (((373677261713969 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475040512 := by
  exact
    theta_restart_gain 7474778368 7475040512 15 11601 33 (747328148798059 / 100000)
      (373677261713969 / 50000) (2273479 / 100000) (1136741 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7475302656
    (h : (((373677261713969 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475040512) :
    (((373690304680203 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475302656 := by
  exact
    theta_restart_gain 7475040512 7475302656 15 11474 33 (373677261713969 / 50000)
      (373690304680203 / 50000) (1136741 / 50000) (454697 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7475564800
    (h : (((373690304680203 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475302656) :
    (((373703293105721 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475564800 := by
  exact
    theta_restart_gain 7475302656 7475564800 15 11426 33 (373690304680203 / 50000)
      (373703293105721 / 50000) (1136743 / 50000) (2273489 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7475826944
    (h : (((373703293105721 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7475564800) :
    (((93429121540597 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7475826944 := by
  exact
    theta_restart_gain 7475564800 7475826944 15 11606 33 (373703293105721 / 50000)
      (93429121540597 / 12500) (2273489 / 100000) (568373 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7476089088
    (h : (((93429121540597 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7475826944) :
    (((149491815768979 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476089088 := by
  exact
    theta_restart_gain 7475826944 7476089088 15 11483 33 (93429121540597 / 12500)
      (149491815768979 / 20000) (2273493 / 100000) (284187 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7476351232
    (h : (((149491815768979 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476089088) :
    (((29899411690151 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476351232 := by
  exact
    theta_restart_gain 7476089088 7476351232 15 11530 33 (149491815768979 / 20000)
      (29899411690151 / 4000) (284187 / 12500) (2273499 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7476613376
    (h : (((29899411690151 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476351232) :
    (((29900459409891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476613376 := by
  exact
    theta_restart_gain 7476351232 7476613376 15 11521 33 (29899411690151 / 4000)
      (29900459409891 / 4000) (4547 / 200) (2273503 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7476875520
    (h : (((29900459409891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476613376) :
    (((747537898805129 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476875520 := by
  exact
    theta_restart_gain 7476613376 7476875520 15 11618 33 (29900459409891 / 4000)
      (747537898805129 / 100000) (2273503 / 100000) (1136753 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7477137664
    (h : (((747537898805129 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7476875520) :
    (((373782143700439 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7477137664 := by
  exact
    theta_restart_gain 7476875520 7477137664 15 11607 33 (747537898805129 / 100000)
      (373782143700439 / 50000) (2273507 / 100000) (227351 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7477399808
    (h : (((373782143700439 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7477137664) :
    (((93448818589361 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7477399808 := by
  exact
    theta_restart_gain 7477137664 7477399808 15 11551 33 (373782143700439 / 50000)
      (93448818589361 / 12500) (227351 / 10000) (2273513 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7477661952
    (h : (((93448818589361 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7477399808) :
    (((93452124278717 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7477661952 := by
  exact
    theta_restart_gain 7477399808 7477661952 15 11632 33 (93448818589361 / 12500)
      (93452124278717 / 12500) (1136757 / 50000) (2273517 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7477924096
    (h : (((93452124278717 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7477661952) :
    (((29905718038933 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7477924096 := by
  exact
    theta_restart_gain 7477661952 7477924096 15 11417 33 (93452124278717 / 12500)
      (29905718038933 / 4000) (2273517 / 100000) (28419 / 1250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7478186240
    (h : (((29905718038933 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7477924096) :
    (((186917330385851 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478186240 := by
  exact
    theta_restart_gain 7477924096 7478186240 15 11599 33 (29905718038933 / 4000)
      (186917330385851 / 25000) (2273521 / 100000) (568381 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7478448384
    (h : (((186917330385851 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478186240) :
    (((186923876998209 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478448384 := by
  exact
    theta_restart_gain 7478186240 7478448384 15 11518 33 (186917330385851 / 25000)
      (186923876998209 / 25000) (568381 / 25000) (2273527 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7478710528
    (h : (((186923876998209 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478448384) :
    (((186930417369883 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478710528 := by
  exact
    theta_restart_gain 7478448384 7478710528 15 11507 33 (186923876998209 / 25000)
      (186930417369883 / 25000) (284191 / 12500) (2273531 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7478972672
    (h : (((186930417369883 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478710528) :
    (((747747826453687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478972672 := by
  exact
    theta_restart_gain 7478710528 7478972672 15 11505 33 (186930417369883 / 25000)
      (747747826453687 / 100000) (2273531 / 100000) (1136767 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7479234816
    (h : (((747747826453687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7478972672) :
    (((93471747365849 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7479234816 := by
  exact
    theta_restart_gain 7478972672 7479234816 15 11503 33 (747747826453687 / 100000)
      (93471747365849 / 12500) (454707 / 20000) (1136769 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7479496960
    (h : (((93471747365849 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7479234816) :
    (((46737513472207 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7479496960 := by
  exact
    theta_restart_gain 7479234816 7479496960 15 11540 33 (93471747365849 / 12500)
      (46737513472207 / 6250) (1136769 / 50000) (2273541 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7479759104
    (h : (((46737513472207 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7479496960) :
    (((373913318193447 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7479759104 := by
  exact
    theta_restart_gain 7479496960 7479759104 15 11621 33 (46737513472207 / 6250)
      (373913318193447 / 50000) (1136771 / 50000) (454709 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7480021248
    (h : (((373913318193447 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7479759104) :
    (((747852848087199 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7480021248 := by
  exact
    theta_restart_gain 7479759104 7480021248 15 11529 33 (373913318193447 / 50000)
      (747852848087199 / 100000) (454709 / 20000) (568387 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7480283392
    (h : (((747852848087199 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7480021248) :
    (((46742433850567 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7480283392 := by
  exact
    theta_restart_gain 7480021248 7480283392 15 11477 33 (747852848087199 / 100000)
      (46742433850567 / 6250) (2273549 / 100000) (142097 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7480545536
    (h : (((46742433850567 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7480283392) :
    (((46744068818649 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7480545536 := by
  exact
    theta_restart_gain 7480283392 7480545536 15 11506 33 (46742433850567 / 6250)
      (46744068818649 / 6250) (142097 / 6250) (454711 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7480807680
    (h : (((46744068818649 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7480545536) :
    (((93491398484991 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7480807680 := by
  exact
    theta_restart_gain 7480545536 7480807680 15 11474 33 (46744068818649 / 6250)
      (93491398484991 / 12500) (568389 / 25000) (2273559 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7481069824
    (h : (((93491398484991 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7480807680) :
    (((7479573519969 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481069824 := by
  exact
    theta_restart_gain 7480807680 7481069824 15 11508 33 (93491398484991 / 12500)
      (7479573519969 / 1000) (2273559 / 100000) (1136781 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7481331968
    (h : (((7479573519969 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481069824) :
    (((74798379353459 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481331968 := by
  exact
    theta_restart_gain 7481069824 7481331968 15 11630 33 (7479573519969 / 1000)
      (74798379353459 / 10000) (2273563 / 100000) (1136783 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7481594112
    (h : (((74798379353459 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481331968) :
    (((187002492274987 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481594112 := by
  exact
    theta_restart_gain 7481331968 7481594112 15 11513 33 (74798379353459 / 10000)
      (187002492274987 / 25000) (1136783 / 50000) (2273569 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7481856256
    (h : (((187002492274987 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481594112) :
    (((374018106459229 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481856256 := by
  exact
    theta_restart_gain 7481594112 7481856256 15 11543 33 (187002492274987 / 25000)
      (374018106459229 / 50000) (227357 / 10000) (2273573 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7482118400
    (h : (((374018106459229 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7481856256) :
    (((374031234069731 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482118400 := by
  exact
    theta_restart_gain 7481856256 7482118400 15 11548 33 (374018106459229 / 50000)
      (374031234069731 / 50000) (2273573 / 100000) (284197 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7482380544
    (h : (((374031234069731 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482118400) :
    (((748088525605459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482380544 := by
  exact
    theta_restart_gain 7482118400 7482380544 15 11461 33 (374031234069731 / 50000)
      (748088525605459 / 100000) (2273577 / 100000) (113679 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7482642688
    (h : (((748088525605459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482380544) :
    (((748115033274679 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482642688 := by
  exact
    theta_restart_gain 7482380544 7482642688 15 11659 33 (748088525605459 / 100000)
      (748115033274679 / 100000) (113679 / 5000) (2273583 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7482904832
    (h : (((748115033274679 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482642688) :
    (((149628228622667 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482904832 := by
  exact
    theta_restart_gain 7482642688 7482904832 15 11484 33 (748115033274679 / 100000)
      (149628228622667 / 20000) (142099 / 6250) (2273587 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7483166976
    (h : (((149628228622667 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7482904832) :
    (((748167307552531 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483166976 := by
  exact
    theta_restart_gain 7482904832 7483166976 15 11508 33 (149628228622667 / 20000)
      (748167307552531 / 100000) (2273587 / 100000) (227359 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7483429120
    (h : (((748167307552531 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483166976) :
    (((748193512962397 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483429120 := by
  exact
    theta_restart_gain 7483166976 7483429120 15 11526 33 (748167307552531 / 100000)
      (748193512962397 / 100000) (2273591 / 100000) (1136797 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7483691264
    (h : (((748193512962397 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483429120) :
    (((748219820718571 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483691264 := by
  exact
    theta_restart_gain 7483429120 7483691264 15 11571 33 (748193512962397 / 100000)
      (748219820718571 / 100000) (1136797 / 50000) (2273597 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7483953408
    (h : (((748219820718571 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483691264) :
    (((748246071681079 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483953408 := by
  exact
    theta_restart_gain 7483691264 7483953408 15 11546 33 (748219820718571 / 100000)
      (748246071681079 / 100000) (1136799 / 50000) (2273601 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7484215552
    (h : (((748246071681079 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7483953408) :
    (((748272281753407 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484215552 := by
  exact
    theta_restart_gain 7483953408 7484215552 15 11528 33 (748246071681079 / 100000)
      (748272281753407 / 100000) (2273601 / 100000) (568401 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7484477696
    (h : (((748272281753407 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484215552) :
    (((748298496419057 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484477696 := by
  exact
    theta_restart_gain 7484215552 7484477696 15 11530 33 (748272281753407 / 100000)
      (748298496419057 / 100000) (454721 / 20000) (284201 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7484739840
    (h : (((748298496419057 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484477696) :
    (((748324765685889 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484739840 := by
  exact
    theta_restart_gain 7484477696 7484739840 15 11554 33 (748298496419057 / 100000)
      (748324765685889 / 100000) (284201 / 12500) (2273611 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7485001984
    (h : (((748324765685889 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7484739840) :
    (((748350823553021 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485001984 := by
  exact
    theta_restart_gain 7484739840 7485001984 15 11461 33 (748324765685889 / 100000)
      (748350823553021 / 100000) (568403 / 25000) (454723 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7485264128
    (h : (((748350823553021 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485001984) :
    (((748377161109181 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485264128 := by
  exact
    theta_restart_gain 7485001984 7485264128 15 11584 33 (748350823553021 / 100000)
      (748377161109181 / 100000) (454723 / 20000) (1136809 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7485526272
    (h : (((748377161109181 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485264128) :
    (((374201570876747 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485526272 := by
  exact
    theta_restart_gain 7485264128 7485526272 15 11427 33 (748377161109181 / 100000)
      (374201570876747 / 50000) (2273619 / 100000) (1136811 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7485788416
    (h : (((374201570876747 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485526272) :
    (((374214623740649 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485788416 := by
  exact
    theta_restart_gain 7485526272 7485788416 15 11482 33 (374201570876747 / 50000)
      (374214623740649 / 50000) (1136811 / 50000) (18189 / 800) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7486050560
    (h : (((374214623740649 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7485788416) :
    (((374227765298929 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486050560 := by
  exact
    theta_restart_gain 7485788416 7486050560 15 11560 33 (374214623740649 / 50000)
      (374227765298929 / 50000) (1136813 / 50000) (2273629 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7486312704
    (h : (((374227765298929 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486050560) :
    (((374240775004067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486312704 := by
  exact
    theta_restart_gain 7486050560 7486312704 15 11444 33 (374227765298929 / 50000)
      (374240775004067 / 50000) (2273629 / 100000) (71051 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7486574848
    (h : (((374240775004067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486312704) :
    (((149701583466007 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486574848 := by
  exact
    theta_restart_gain 7486312704 7486574848 15 11597 33 (374240775004067 / 50000)
      (149701583466007 / 20000) (2273633 / 100000) (568409 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7486836992
    (h : (((149701583466007 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486574848) :
    (((748534300602179 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486836992 := by
  exact
    theta_restart_gain 7486574848 7486836992 15 11604 33 (149701583466007 / 20000)
      (748534300602179 / 100000) (568409 / 25000) (2273639 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7487099136
    (h : (((748534300602179 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7486836992) :
    (((748560774866339 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487099136 := by
  exact
    theta_restart_gain 7486836992 7487099136 15 11644 33 (748534300602179 / 100000)
      (748560774866339 / 100000) (56841 / 2500) (2273643 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7487361280
    (h : (((748560774866339 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487099136) :
    (((374293443828097 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487361280 := by
  exact
    theta_restart_gain 7487099136 7487361280 15 11485 33 (748560774866339 / 100000)
      (374293443828097 / 50000) (2273643 / 100000) (1136823 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7487623424
    (h : (((374293443828097 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487361280) :
    (((149722608283527 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487623424 := by
  exact
    theta_restart_gain 7487361280 7487623424 15 11503 33 (374293443828097 / 50000)
      (149722608283527 / 20000) (2273647 / 100000) (45473 / 2000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7487885568
    (h : (((149722608283527 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487623424) :
    (((149727824036627 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487885568 := by
  exact
    theta_restart_gain 7487623424 7487885568 15 11470 33 (149722608283527 / 20000)
      (149727824036627 / 20000) (45473 / 2000) (2273653 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7488147712
    (h : (((149727824036627 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7487885568) :
    (((149733067082751 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488147712 := by
  exact
    theta_restart_gain 7487885568 7488147712 15 11530 33 (149727824036627 / 20000)
      (149733067082751 / 20000) (1136827 / 50000) (2273657 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7488409856
    (h : (((149733067082751 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488147712) :
    (((748691814423177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488409856 := by
  exact
    theta_restart_gain 7488147712 7488409856 15 11646 33 (149733067082751 / 20000)
      (748691814423177 / 100000) (2273657 / 100000) (113683 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7488672000
    (h : (((748691814423177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488409856) :
    (((748717970619321 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488672000 := by
  exact
    theta_restart_gain 7488409856 7488672000 15 11504 33 (748691814423177 / 100000)
      (748717970619321 / 100000) (2273661 / 100000) (71052 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7488934144
    (h : (((748717970619321 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488672000) :
    (((748744149586617 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488934144 := by
  exact
    theta_restart_gain 7488672000 7488934144 15 11514 33 (748717970619321 / 100000)
      (748744149586617 / 100000) (71052 / 3125) (2273667 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7489196288
    (h : (((748744149586617 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7488934144) :
    (((748770303589621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489196288 := by
  exact
    theta_restart_gain 7488934144 7489196288 15 11503 33 (748744149586617 / 100000)
      (748770303589621 / 100000) (568417 / 25000) (2273671 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7489458432
    (h : (((748770303589621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489196288) :
    (((149759360190291 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489458432 := by
  exact
    theta_restart_gain 7489196288 7489458432 15 11654 33 (748770303589621 / 100000)
      (149759360190291 / 20000) (2273671 / 100000) (1136837 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7489720576
    (h : (((149759360190291 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489458432) :
    (((149764580548091 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489720576 := by
  exact
    theta_restart_gain 7489458432 7489720576 15 11480 33 (149759360190291 / 20000)
      (149764580548091 / 20000) (90947 / 4000) (1136839 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7489982720
    (h : (((149764580548091 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489720576) :
    (((748848949995623 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489982720 := by
  exact
    theta_restart_gain 7489720576 7489982720 15 11456 33 (149764580548091 / 20000)
      (748848949995623 / 100000) (1136839 / 50000) (2273681 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7490244864
    (h : (((748848949995623 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7489982720) :
    (((748875067780757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490244864 := by
  exact
    theta_restart_gain 7489982720 7490244864 15 11487 33 (748848949995623 / 100000)
      (748875067780757 / 100000) (1136841 / 50000) (454737 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7490507008
    (h : (((748875067780757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490244864) :
    (((374450745137071 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490507008 := by
  exact
    theta_restart_gain 7490244864 7490507008 15 11621 33 (748875067780757 / 100000)
      (374450745137071 / 50000) (454737 / 20000) (284211 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7490769152
    (h : (((374450745137071 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490507008) :
    (((748927639971331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490769152 := by
  exact
    theta_restart_gain 7490507008 7490769152 15 11501 33 (374450745137071 / 50000)
      (748927639971331 / 100000) (2273689 / 100000) (568423 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7491031296
    (h : (((748927639971331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7490769152) :
    (((748953980693151 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491031296 := by
  exact
    theta_restart_gain 7490769152 7491031296 15 11585 33 (748927639971331 / 100000)
      (748953980693151 / 100000) (568423 / 25000) (454739 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7491293440
    (h : (((748953980693151 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491031296) :
    (((748980225966079 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491293440 := by
  exact
    theta_restart_gain 7491031296 7491293440 15 11543 33 (748953980693151 / 100000)
      (748980225966079 / 100000) (71053 / 3125) (2273699 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7491555584
    (h : (((748980225966079 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491293440) :
    (((187251663292389 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491555584 := by
  exact
    theta_restart_gain 7491293440 7491555584 15 11623 33 (748980225966079 / 100000)
      (187251663292389 / 25000) (2273699 / 100000) (1136851 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7491817728
    (h : (((187251663292389 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491555584) :
    (((749032866691443 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491817728 := by
  exact
    theta_restart_gain 7491555584 7491817728 15 11529 33 (187251663292389 / 25000)
      (749032866691443 / 100000) (2273703 / 100000) (1136853 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7492079872
    (h : (((749032866691443 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7491817728) :
    (((749059209849159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492079872 := by
  exact
    theta_restart_gain 7491817728 7492079872 15 11586 33 (749032866691443 / 100000)
      (749059209849159 / 100000) (1136853 / 50000) (2273709 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7492342016
    (h : (((749059209849159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492079872) :
    (((749085282481729 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492342016 := by
  exact
    theta_restart_gain 7492079872 7492342016 15 11467 33 (749059209849159 / 100000)
      (749085282481729 / 100000) (227371 / 10000) (2273713 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7492604160
    (h : (((749085282481729 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492342016) :
    (((187277856976879 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492604160 := by
  exact
    theta_restart_gain 7492342016 7492604160 15 11499 33 (749085282481729 / 100000)
      (187277856976879 / 25000) (2273713 / 100000) (568429 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7492866304
    (h : (((187277856976879 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492604160) :
    (((187284409829273 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492866304 := by
  exact
    theta_restart_gain 7492604160 7492866304 15 11528 33 (187277856976879 / 25000)
      (187284409829273 / 25000) (2273717 / 100000) (56843 / 2500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7493128448
    (h : (((187284409829273 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7492866304) :
    (((187290980311643 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493128448 := by
  exact
    theta_restart_gain 7492866304 7493128448 15 11559 33 (187284409829273 / 25000)
      (187290980311643 / 25000) (56843 / 2500) (2273723 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7493390592
    (h : (((187290980311643 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493128448) :
    (((187297599122207 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493390592 := by
  exact
    theta_restart_gain 7493128448 7493390592 15 11644 33 (187290980311643 / 25000)
      (187297599122207 / 25000) (568431 / 25000) (2273727 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7493652736
    (h : (((187297599122207 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493390592) :
    (((374608342660201 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493652736 := by
  exact
    theta_restart_gain 7493390592 7493652736 15 11562 33 (187297599122207 / 25000)
      (374608342660201 / 50000) (2273727 / 100000) (227373 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7493914880
    (h : (((374608342660201 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493652736) :
    (((749242880975253 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493914880 := by
  exact
    theta_restart_gain 7493652736 7493914880 15 11521 33 (374608342660201 / 50000)
      (749242880975253 / 100000) (2273731 / 100000) (1136867 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7494177024
    (h : (((749242880975253 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7493914880) :
    (((29970764157979 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494177024 := by
  exact
    theta_restart_gain 7493914880 7494177024 15 11533 33 (749242880975253 / 100000)
      (29970764157979 / 4000) (1136867 / 50000) (2273737 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7494439168
    (h : (((29970764157979 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494177024) :
    (((749295424740563 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494439168 := by
  exact
    theta_restart_gain 7494177024 7494439168 15 11576 33 (29970764157979 / 4000)
      (749295424740563 / 100000) (1136869 / 50000) (2273741 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7494701312
    (h : (((749295424740563 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494439168) :
    (((187330389211469 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494701312 := by
  exact
    theta_restart_gain 7494439168 7494701312 15 11493 33 (749295424740563 / 100000)
      (187330389211469 / 25000) (2273741 / 100000) (142109 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7494963456
    (h : (((187330389211469 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494701312) :
    (((187336969429499 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494963456 := by
  exact
    theta_restart_gain 7494701312 7494963456 15 11576 33 (187330389211469 / 25000)
      (187336969429499 / 25000) (454749 / 20000) (568437 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7495225600
    (h : (((187336969429499 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7494963456) :
    (((187343578078061 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495225600 := by
  exact
    theta_restart_gain 7494963456 7495225600 15 11626 33 (187336969429499 / 25000)
      (187343578078061 / 25000) (568437 / 25000) (2273751 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7495487744
    (h : (((187343578078061 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495225600) :
    (((187350138421019 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495487744 := by
  exact
    theta_restart_gain 7495225600 7495487744 15 11541 33 (187343578078061 / 25000)
      (187350138421019 / 25000) (284219 / 12500) (454751 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7495749888
    (h : (((187350138421019 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495487744) :
    (((749426513144911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495749888 := by
  exact
    theta_restart_gain 7495487744 7495749888 15 11417 33 (187350138421019 / 25000)
      (749426513144911 / 100000) (454751 / 20000) (1136879 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7496012032
    (h : (((749426513144911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7495749888) :
    (((749452875106757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496012032 := by
  exact
    theta_restart_gain 7495749888 7496012032 15 11594 33 (749426513144911 / 100000)
      (749452875106757 / 100000) (2273759 / 100000) (1136881 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7496274176
    (h : (((749452875106757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496012032) :
    (((749478984715803 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496274176 := by
  exact
    theta_restart_gain 7496012032 7496274176 15 11483 33 (749452875106757 / 100000)
      (749478984715803 / 100000) (1136881 / 50000) (454753 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7496536320
    (h : (((749478984715803 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496274176) :
    (((749505085275717 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496536320 := by
  exact
    theta_restart_gain 7496274176 7496536320 15 11479 33 (749478984715803 / 100000)
      (749505085275717 / 100000) (1136883 / 50000) (2273769 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7496798464
    (h : (((749505085275717 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7496536320) :
    (((46845689453361 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7496798464 := by
  exact
    theta_restart_gain 7496536320 7496798464 15 11411 33 (749505085275717 / 100000)
      (46845689453361 / 6250) (2273769 / 100000) (568443 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7497060608
    (h : (((46845689453361 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7496798464) :
    (((374778576179 / 50) : ℚ) : ℝ) ≤ Chebyshev.theta 7497060608 := by
  exact
    theta_restart_gain 7496798464 7497060608 15 11488 33 (46845689453361 / 6250) (374778576179 / 50)
      (2273773 / 100000) (142111 / 6250) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7497322752 (h : (((374778576179 / 50) : ℚ) : ℝ) ≤ Chebyshev.theta 7497060608) :
    (((46848958288429 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7497322752 := by
  exact
    theta_restart_gain 7497060608 7497322752 15 11514 33 (374778576179 / 50) (46848958288429 / 6250)
      (142111 / 6250) (2273779 / 100000) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7497584896
    (h : (((46848958288429 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7497322752) :
    (((187402357196981 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7497584896 := by
  exact
    theta_restart_gain 7497322752 7497584896 15 11477 33 (46848958288429 / 6250)
      (187402357196981 / 25000) (113689 / 5000) (2273783 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7497847040
    (h : (((187402357196981 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7497584896) :
    (((749635802396941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7497847040 := by
  exact
    theta_restart_gain 7497584896 7497847040 15 11599 33 (187402357196981 / 25000)
      (749635802396941 / 100000) (2273783 / 100000) (1136893 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498109184
    (h : (((749635802396941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7497847040) :
    (((374830947051383 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498109184 := by
  exact
    theta_restart_gain 7497847040 7498109184 15 11475 33 (749635802396941 / 100000)
      (374830947051383 / 50000) (2273787 / 100000) (227379 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498371328
    (h : (((374830947051383 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498109184) :
    (((374844146402333 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498371328 := by
  exact
    theta_restart_gain 7498109184 7498371328 15 11610 33 (374830947051383 / 50000)
      (374844146402333 / 50000) (227379 / 10000) (2273793 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498387712
    (h : (((374844146402333 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498371328) :
    (((187422478504947 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498387712 := by
  exact
    theta_restart_gain 7498371328 7498387712 11 713 33 (374844146402333 / 50000)
      (187422478504947 / 25000) (1136897 / 50000) (2273797 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498389760
    (h : (((187422478504947 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498387712) :
    (((374845069562697 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498389760 := by
  exact
    theta_restart_gain 7498387712 7498389760 8 99 33 (187422478504947 / 25000)
      (374845069562697 / 50000) (1136897 / 50000) (2273797 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7498389760
    (h : (((93311287231993 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7466389760) :
    (((374845069562697 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7498389760 point7498387712)
                  (Function.comp point7498371328 point7498109184))
                (Function.comp (Function.comp point7497847040 point7497584896)
                  (Function.comp point7497322752 point7497060608)))
              (Function.comp
                (Function.comp (Function.comp point7496798464 point7496536320)
                  (Function.comp point7496274176 point7496012032))
                (Function.comp (Function.comp point7495749888 point7495487744)
                  (Function.comp point7495225600 point7494963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7494701312 point7494439168)
                  (Function.comp point7494177024 point7493914880))
                (Function.comp (Function.comp point7493652736 point7493390592)
                  (Function.comp point7493128448 point7492866304)))
              (Function.comp
                (Function.comp (Function.comp point7492604160 point7492342016)
                  (Function.comp point7492079872 point7491817728))
                (Function.comp (Function.comp point7491555584 point7491293440)
                  (Function.comp point7491031296 point7490769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7490507008 point7490244864)
                  (Function.comp point7489982720 point7489720576))
                (Function.comp (Function.comp point7489458432 point7489196288)
                  (Function.comp point7488934144 point7488672000)))
              (Function.comp
                (Function.comp (Function.comp point7488409856 point7488147712)
                  (Function.comp point7487885568 point7487623424))
                (Function.comp (Function.comp point7487361280 point7487099136)
                  (Function.comp point7486836992 point7486574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7486312704 point7486050560)
                  (Function.comp point7485788416 point7485526272))
                (Function.comp (Function.comp point7485264128 point7485001984)
                  (Function.comp point7484739840 point7484477696)))
              (Function.comp
                (Function.comp (Function.comp point7484215552 point7483953408)
                  (Function.comp point7483691264 point7483429120))
                (Function.comp (Function.comp point7483166976 point7482904832)
                  (Function.comp point7482642688 point7482380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7482118400 point7481856256)
                  (Function.comp point7481594112 point7481331968))
                (Function.comp (Function.comp point7481069824 point7480807680)
                  (Function.comp point7480545536 point7480283392)))
              (Function.comp
                (Function.comp (Function.comp point7480021248 point7479759104)
                  (Function.comp point7479496960 point7479234816))
                (Function.comp (Function.comp point7478972672 point7478710528)
                  (Function.comp point7478448384 point7478186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7477924096 point7477661952)
                  (Function.comp point7477399808 point7477137664))
                (Function.comp (Function.comp point7476875520 point7476613376)
                  (Function.comp point7476351232 point7476089088)))
              (Function.comp
                (Function.comp (Function.comp point7475826944 point7475564800)
                  (Function.comp point7475302656 point7475040512))
                (Function.comp (Function.comp point7474778368 point7474516224)
                  (Function.comp point7474254080 point7473991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7473729792 point7473467648)
                  (Function.comp point7473205504 point7472943360))
                (Function.comp (Function.comp point7472681216 point7472419072)
                  (Function.comp point7472156928 point7471894784)))
              (Function.comp
                (Function.comp (Function.comp point7471632640 point7471370496)
                  (Function.comp point7471108352 point7470846208))
                (Function.comp (Function.comp point7470584064 point7470321920)
                  (Function.comp point7470059776 point7469797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7469535488 point7469273344)
                  (Function.comp point7469011200 point7468749056))
                (Function.comp (Function.comp point7468486912 point7468224768)
                  (Function.comp point7467962624 point7467700480)))
              (Function.comp (Function.comp point7467438336 point7467176192)
                (Function.comp point7466914048 point7466651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
