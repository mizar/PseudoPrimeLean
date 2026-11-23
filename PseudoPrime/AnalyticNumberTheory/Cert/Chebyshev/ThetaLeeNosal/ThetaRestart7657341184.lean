/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7657341184 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626651904
    (h : (((381243490745971 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626389760) :
    (((15250266814667 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626651904 := by
  exact
    theta_restart_gain 7626389760 7626651904 15 11584 33 (381243490745971 / 50000)
      (15250266814667 / 2000) (2275487 / 100000) (227549 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626914048
    (h : (((15250266814667 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626651904) :
    (((15250786991681 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626914048 := by
  exact
    theta_restart_gain 7626651904 7626914048 15 11430 33 (15250266814667 / 2000)
      (15250786991681 / 2000) (227549 / 10000) (2275493 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7627176192
    (h : (((15250786991681 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626914048) :
    (((47660348557273 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7627176192 := by
  exact
    theta_restart_gain 7626914048 7627176192 15 11526 33 (15250786991681 / 2000)
      (47660348557273 / 6250) (2275493 / 100000) (284437 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7627438336
    (h : (((47660348557273 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7627176192) :
    (((30503672626891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627438336 := by
  exact
    theta_restart_gain 7627176192 7627438336 15 11531 33 (47660348557273 / 6250)
      (30503672626891 / 4000) (2275497 / 100000) (4551 / 200) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7627700480
    (h : (((30503672626891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627438336) :
    (((30504730552351 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627700480 := by
  exact
    theta_restart_gain 7627438336 7627700480 15 11623 33 (30503672626891 / 4000)
      (30504730552351 / 4000) (4551 / 200) (2275503 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7627962624
    (h : (((30504730552351 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627700480) :
    (((762644418451751 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627962624 := by
  exact
    theta_restart_gain 7627700480 7627962624 15 11494 33 (30504730552351 / 4000)
      (762644418451751 / 100000) (142219 / 6250) (2275507 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7628224768
    (h : (((762644418451751 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7627962624) :
    (((762670650496447 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628224768 := by
  exact
    theta_restart_gain 7627962624 7628224768 15 11528 33 (762644418451751 / 100000)
      (762670650496447 / 100000) (2275507 / 100000) (227551 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7628486912
    (h : (((762670650496447 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628224768) :
    (((30507877123899 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628486912 := by
  exact
    theta_restart_gain 7628224768 7628486912 15 11548 33 (762670650496447 / 100000)
      (30507877123899 / 4000) (2275511 / 100000) (1137757 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7628749056
    (h : (((30507877123899 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628486912) :
    (((30508914758283 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628749056 := by
  exact
    theta_restart_gain 7628486912 7628749056 15 11400 33 (30507877123899 / 4000)
      (30508914758283 / 4000) (1137757 / 50000) (2275517 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7629011200
    (h : (((30508914758283 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7628749056) :
    (((762749096566017 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629011200 := by
  exact
    theta_restart_gain 7628749056 7629011200 15 11526 33 (30508914758283 / 4000)
      (762749096566017 / 100000) (2275517 / 100000) (14222 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7629273344
    (h : (((762749096566017 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629011200) :
    (((381387697381107 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629273344 := by
  exact
    theta_restart_gain 7629011200 7629273344 15 11557 33 (762749096566017 / 100000)
      (381387697381107 / 50000) (2275521 / 100000) (568881 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7629535488
    (h : (((381387697381107 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629273344) :
    (((76280149274697 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629535488 := by
  exact
    theta_restart_gain 7629273344 7629535488 15 11469 33 (381387697381107 / 50000)
      (76280149274697 / 10000) (568881 / 25000) (2275527 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7629797632
    (h : (((76280149274697 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629535488) :
    (((381413823832901 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629797632 := by
  exact
    theta_restart_gain 7629535488 7629797632 15 11494 33 (76280149274697 / 10000)
      (381413823832901 / 50000) (284441 / 12500) (2275531 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7630059776
    (h : (((381413823832901 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7629797632) :
    (((381427062872259 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630059776 := by
  exact
    theta_restart_gain 7629797632 7630059776 15 11636 33 (381413823832901 / 50000)
      (381427062872259 / 50000) (2275531 / 100000) (1137767 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7630321920
    (h : (((381427062872259 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630059776) :
    (((381440115341019 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630321920 := by
  exact
    theta_restart_gain 7630059776 7630321920 15 11472 33 (381427062872259 / 50000)
      (381440115341019 / 50000) (455107 / 20000) (1137769 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7630584064
    (h : (((381440115341019 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630321920) :
    (((381453076805467 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630584064 := by
  exact
    theta_restart_gain 7630321920 7630584064 15 11392 33 (381440115341019 / 50000)
      (381453076805467 / 50000) (1137769 / 50000) (2275541 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7630846208
    (h : (((381453076805467 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630584064) :
    (((38146626698467 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630846208 := by
  exact
    theta_restart_gain 7630584064 7630846208 15 11593 33 (381453076805467 / 50000)
      (38146626698467 / 5000) (1137771 / 50000) (455109 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7631108352
    (h : (((38146626698467 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7630846208) :
    (((15259176694369 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631108352 := by
  exact
    theta_restart_gain 7630846208 7631108352 15 11558 33 (38146626698467 / 5000)
      (15259176694369 / 2000) (455109 / 20000) (568887 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7631370496
    (h : (((15259176694369 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631108352) :
    (((381492425529367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631370496 := by
  exact
    theta_restart_gain 7631108352 7631370496 15 11433 33 (15259176694369 / 2000)
      (381492425529367 / 50000) (568887 / 25000) (2275551 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7631632640
    (h : (((381492425529367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631370496) :
    (((381505506540039 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631632640 := by
  exact
    theta_restart_gain 7631370496 7631632640 15 11497 33 (381492425529367 / 50000)
      (381505506540039 / 50000) (71111 / 3125) (455111 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7631894784
    (h : (((381505506540039 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7631632640) :
    (((95379680171981 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7631894784 := by
  exact
    theta_restart_gain 7631632640 7631894784 15 11614 33 (381505506540039 / 50000)
      (95379680171981 / 12500) (455111 / 20000) (1137779 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7632156928
    (h : (((95379680171981 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7631894784) :
    (((381531761916553 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632156928 := by
  exact
    theta_restart_gain 7631894784 7632156928 15 11462 33 (95379680171981 / 12500)
      (381531761916553 / 50000) (2275559 / 100000) (1137781 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7632419072
    (h : (((381531761916553 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632156928) :
    (((76308987939219 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632419072 := by
  exact
    theta_restart_gain 7632156928 7632419072 15 11582 33 (381531761916553 / 50000)
      (76308987939219 / 10000) (1137781 / 50000) (455113 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7632681216
    (h : (((76308987939219 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632419072) :
    (((381557965035879 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632681216 := by
  exact
    theta_restart_gain 7632419072 7632681216 15 11448 33 (76308987939219 / 10000)
      (381557965035879 / 50000) (1137783 / 50000) (2275569 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7632943360
    (h : (((381557965035879 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7632681216) :
    (((95392775473929 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7632943360 := by
  exact
    theta_restart_gain 7632681216 7632943360 15 11546 33 (381557965035879 / 50000)
      (95392775473929 / 12500) (2275569 / 100000) (568893 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7633205504
    (h : (((95392775473929 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7632943360) :
    (((190792065341601 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633205504 := by
  exact
    theta_restart_gain 7632943360 7633205504 15 11451 33 (95392775473929 / 12500)
      (190792065341601 / 25000) (568893 / 25000) (91023 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7633467648
    (h : (((190792065341601 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633205504) :
    (((190798615018223 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633467648 := by
  exact
    theta_restart_gain 7633205504 7633467648 15 11513 33 (190792065341601 / 25000)
      (190798615018223 / 25000) (284447 / 12500) (2275579 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7633729792
    (h : (((190798615018223 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633467648) :
    (((30528836729197 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633729792 := by
  exact
    theta_restart_gain 7633467648 7633729792 15 11627 33 (190798615018223 / 25000)
      (30528836729197 / 4000) (2275579 / 100000) (1137791 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7633991936
    (h : (((30528836729197 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7633729792) :
    (((23851464157793 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7633991936 := by
  exact
    theta_restart_gain 7633729792 7633991936 15 11397 33 (30528836729197 / 4000)
      (23851464157793 / 3125) (2275583 / 100000) (1137793 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7634254080
    (h : (((23851464157793 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7633991936) :
    (((95409150541907 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7634254080 := by
  exact
    theta_restart_gain 7633991936 7634254080 15 11580 33 (23851464157793 / 3125)
      (95409150541907 / 12500) (1137793 / 50000) (2275589 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7634516224
    (h : (((95409150541907 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7634254080) :
    (((381649651538483 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7634516224 := by
  exact
    theta_restart_gain 7634254080 7634516224 15 11469 33 (95409150541907 / 12500)
      (381649651538483 / 50000) (227559 / 10000) (2275593 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7634778368
    (h : (((381649651538483 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7634516224) :
    (((763325588451709 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7634778368 := by
  exact
    theta_restart_gain 7634516224 7634778368 15 11551 33 (381649651538483 / 50000)
      (763325588451709 / 100000) (2275593 / 100000) (568899 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7635040512
    (h : (((763325588451709 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7634778368) :
    (((763351860207529 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635040512 := by
  exact
    theta_restart_gain 7634778368 7635040512 15 11545 33 (763325588451709 / 100000)
      (763351860207529 / 100000) (568899 / 25000) (2275599 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7635302656
    (h : (((763351860207529 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635040512) :
    (((763378202553129 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635302656 := by
  exact
    theta_restart_gain 7635040512 7635302656 15 11576 33 (763351860207529 / 100000)
      (763378202553129 / 100000) (5689 / 250) (2275603 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7635564800
    (h : (((763378202553129 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635302656) :
    (((190851186865531 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635564800 := by
  exact
    theta_restart_gain 7635302656 7635564800 15 11665 33 (763378202553129 / 100000)
      (190851186865531 / 25000) (2275603 / 100000) (1137803 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7635826944
    (h : (((190851186865531 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635564800) :
    (((381715469849347 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635826944 := by
  exact
    theta_restart_gain 7635564800 7635826944 15 11510 33 (190851186865531 / 25000)
      (381715469849347 / 50000) (2275607 / 100000) (227561 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7636089088
    (h : (((381715469849347 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7635826944) :
    (((381728540953187 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636089088 := by
  exact
    theta_restart_gain 7635826944 7636089088 15 11488 33 (381715469849347 / 50000)
      (381728540953187 / 50000) (227561 / 10000) (2275613 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7636351232
    (h : (((381728540953187 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636089088) :
    (((76348314678913 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636351232 := by
  exact
    theta_restart_gain 7636089088 7636351232 15 11454 33 (381728540953187 / 50000)
      (76348314678913 / 10000) (1137807 / 50000) (2275617 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7636613376
    (h : (((76348314678913 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636351232) :
    (((763509436992331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636613376 := by
  exact
    theta_restart_gain 7636351232 7636613376 15 11553 33 (76348314678913 / 10000)
      (763509436992331 / 100000) (2275617 / 100000) (113781 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7636875520
    (h : (((763509436992331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636613376) :
    (((381767738461717 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636875520 := by
  exact
    theta_restart_gain 7636613376 7636875520 15 11443 33 (763509436992331 / 100000)
      (381767738461717 / 50000) (2275621 / 100000) (284453 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7637137664
    (h : (((381767738461717 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7636875520) :
    (((381780945045601 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637137664 := by
  exact
    theta_restart_gain 7636875520 7637137664 15 11607 33 (381767738461717 / 50000)
      (381780945045601 / 50000) (284453 / 12500) (2275627 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7637399808
    (h : (((381780945045601 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637137664) :
    (((152717593300199 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637399808 := by
  exact
    theta_restart_gain 7637137664 7637399808 15 11459 33 (381780945045601 / 50000)
      (152717593300199 / 20000) (2275627 / 100000) (227563 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7637661952
    (h : (((152717593300199 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637399808) :
    (((38180715346491 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637661952 := by
  exact
    theta_restart_gain 7637399808 7637661952 15 11575 33 (152717593300199 / 20000)
      (38180715346491 / 5000) (2275631 / 100000) (1137817 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7637924096
    (h : (((38180715346491 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637661952) :
    (((190910126007107 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637924096 := by
  exact
    theta_restart_gain 7637661952 7637924096 15 11512 33 (38180715346491 / 5000)
      (190910126007107 / 25000) (1137817 / 50000) (2275637 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7638186240
    (h : (((190910126007107 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7637924096) :
    (((76366676261531 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638186240 := by
  exact
    theta_restart_gain 7637924096 7638186240 15 11539 33 (190910126007107 / 25000)
      (76366676261531 / 10000) (1137819 / 50000) (2275641 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7638448384
    (h : (((76366676261531 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638186240) :
    (((190923229708241 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638448384 := by
  exact
    theta_restart_gain 7638186240 7638448384 15 11494 33 (76366676261531 / 10000)
      (190923229708241 / 25000) (2275641 / 100000) (568911 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7638710528
    (h : (((190923229708241 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638448384) :
    (((381859610368937 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638710528 := by
  exact
    theta_restart_gain 7638448384 7638710528 15 11558 33 (190923229708241 / 25000)
      (381859610368937 / 50000) (455129 / 20000) (71114 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7638972672
    (h : (((381859610368937 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638710528) :
    (((381872573597769 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638972672 := by
  exact
    theta_restart_gain 7638710528 7638972672 15 11393 33 (381859610368937 / 50000)
      (381872573597769 / 50000) (71114 / 3125) (2275651 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7639234816
    (h : (((381872573597769 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7638972672) :
    (((381885585770187 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639234816 := by
  exact
    theta_restart_gain 7638972672 7639234816 15 11436 33 (381872573597769 / 50000)
      (381885585770187 / 50000) (2275651 / 100000) (1137827 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7639496960
    (h : (((381885585770187 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639234816) :
    (((763797393912939 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639496960 := by
  exact
    theta_restart_gain 7639234816 7639496960 15 11523 33 (381885585770187 / 50000)
      (763797393912939 / 100000) (455131 / 20000) (1137829 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7639759104
    (h : (((763797393912939 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639496960) :
    (((152764718257567 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639759104 := by
  exact
    theta_restart_gain 7639496960 7639759104 15 11512 33 (763797393912939 / 100000)
      (152764718257567 / 20000) (1137829 / 50000) (2275661 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7640021248
    (h : (((152764718257567 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7639759104) :
    (((763849877459597 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640021248 := by
  exact
    theta_restart_gain 7639759104 7640021248 15 11551 33 (152764718257567 / 20000)
      (763849877459597 / 100000) (1137831 / 50000) (455133 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7640283392
    (h : (((763849877459597 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640021248) :
    (((381938038595371 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640283392 := by
  exact
    theta_restart_gain 7640021248 7640283392 15 11513 33 (763849877459597 / 100000)
      (381938038595371 / 50000) (455133 / 20000) (568917 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7640545536
    (h : (((381938038595371 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640283392) :
    (((76390213815213 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640545536 := by
  exact
    theta_restart_gain 7640283392 7640545536 15 11452 33 (381938038595371 / 50000)
      (76390213815213 / 10000) (2275669 / 100000) (284459 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7640807680
    (h : (((76390213815213 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640545536) :
    (((381964204254849 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640807680 := by
  exact
    theta_restart_gain 7640545536 7640807680 15 11544 33 (76390213815213 / 10000)
      (381964204254849 / 50000) (284459 / 12500) (91027 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7641069824
    (h : (((381964204254849 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7640807680) :
    (((381977334899599 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641069824 := by
  exact
    theta_restart_gain 7640807680 7641069824 15 11540 33 (381964204254849 / 50000)
      (381977334899599 / 50000) (91027 / 4000) (1137839 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7641331968
    (h : (((381977334899599 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641069824) :
    (((763980951615969 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641331968 := by
  exact
    theta_restart_gain 7641069824 7641331968 15 11549 33 (381977334899599 / 50000)
      (763980951615969 / 100000) (2275679 / 100000) (1137841 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7641594112
    (h : (((763980951615969 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641331968) :
    (((764007099202149 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641594112 := by
  exact
    theta_restart_gain 7641331968 7641594112 15 11490 33 (763980951615969 / 100000)
      (764007099202149 / 100000) (1137841 / 50000) (455137 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7641856256
    (h : (((764007099202149 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641594112) :
    (((152806611135333 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641856256 := by
  exact
    theta_restart_gain 7641594112 7641856256 15 11406 33 (764007099202149 / 100000)
      (152806611135333 / 20000) (1137843 / 50000) (2275689 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7642118400
    (h : (((152806611135333 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7641856256) :
    (((764059449117687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642118400 := by
  exact
    theta_restart_gain 7641856256 7642118400 15 11598 33 (152806611135333 / 20000)
      (764059449117687 / 100000) (2275689 / 100000) (568923 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7642380544
    (h : (((764059449117687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642118400) :
    (((764085797091241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642380544 := by
  exact
    theta_restart_gain 7642118400 7642380544 15 11578 33 (764059449117687 / 100000)
      (764085797091241 / 100000) (2275693 / 100000) (142231 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7642642688
    (h : (((764085797091241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642380544) :
    (((30564474516529 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642642688 := by
  exact
    theta_restart_gain 7642380544 7642642688 15 11454 33 (764085797091241 / 100000)
      (30564474516529 / 4000) (142231 / 6250) (2275699 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7642904832
    (h : (((30564474516529 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7642642688) :
    (((95517247638831 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7642904832 := by
  exact
    theta_restart_gain 7642642688 7642904832 15 11477 33 (30564474516529 / 4000)
      (95517247638831 / 12500) (2275699 / 100000) (1137851 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7643166976
    (h : (((95517247638831 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7642904832) :
    (((764164185830693 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643166976 := by
  exact
    theta_restart_gain 7642904832 7643166976 15 11515 33 (95517247638831 / 12500)
      (764164185830693 / 100000) (2275703 / 100000) (1137853 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7643429120
    (h : (((764164185830693 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643166976) :
    (((764190388309577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643429120 := by
  exact
    theta_restart_gain 7643166976 7643429120 15 11514 33 (764164185830693 / 100000)
      (764190388309577 / 100000) (1137853 / 50000) (2275709 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7643691264
    (h : (((764190388309577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643429120) :
    (((764216406502007 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643691264 := by
  exact
    theta_restart_gain 7643429120 7643691264 15 11433 33 (764190388309577 / 100000)
      (764216406502007 / 100000) (227571 / 10000) (2275713 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7643953408
    (h : (((764216406502007 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643691264) :
    (((382121373939991 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643953408 := by
  exact
    theta_restart_gain 7643691264 7643953408 15 11575 33 (764216406502007 / 100000)
      (382121373939991 / 50000) (2275713 / 100000) (568929 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7644215552
    (h : (((382121373939991 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7643953408) :
    (((191067289962871 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644215552 := by
  exact
    theta_restart_gain 7643953408 7644215552 15 11606 33 (382121373939991 / 50000)
      (191067289962871 / 25000) (2275717 / 100000) (56893 / 2500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7644477696
    (h : (((191067289962871 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644215552) :
    (((191073812176391 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644477696 := by
  exact
    theta_restart_gain 7644215552 7644477696 15 11464 33 (191067289962871 / 25000)
      (191073812176391 / 25000) (56893 / 2500) (2275723 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7644739840
    (h : (((191073812176391 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644477696) :
    (((30572852866559 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644739840 := by
  exact
    theta_restart_gain 7644477696 7644739840 15 11457 33 (191073812176391 / 25000)
      (30572852866559 / 4000) (2275723 / 100000) (1137863 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7645001984
    (h : (((30572852866559 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7644739840) :
    (((382173761054463 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7645001984 := by
  exact
    theta_restart_gain 7644739840 7645001984 15 11513 33 (30572852866559 / 4000)
      (382173761054463 / 50000) (2275727 / 100000) (227573 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7645264128
    (h : (((382173761054463 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7645001984) :
    (((382186923876783 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7645264128 := by
  exact
    theta_restart_gain 7645001984 7645264128 15 11568 33 (382173761054463 / 50000)
      (382186923876783 / 50000) (227573 / 10000) (2275733 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7645526272
    (h : (((382186923876783 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7645264128) :
    (((19110001093191 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7645526272 := by
  exact
    theta_restart_gain 7645264128 7645526272 15 11511 33 (382186923876783 / 50000)
      (19110001093191 / 2500) (1137867 / 50000) (2275737 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7645788416
    (h : (((19110001093191 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7645526272) :
    (((23888321200743 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7645788416 := by
  exact
    theta_restart_gain 7645526272 7645788416 15 11528 33 (19110001093191 / 2500)
      (23888321200743 / 3125) (2275737 / 100000) (113787 / 5000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7646050560
    (h : (((23888321200743 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7645788416) :
    (((191113112361319 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646050560 := by
  exact
    theta_restart_gain 7645788416 7646050560 15 11500 33 (23888321200743 / 3125)
      (191113112361319 / 25000) (2275741 / 100000) (71117 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7646312704
    (h : (((191113112361319 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646050560) :
    (((191119606196823 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646312704 := by
  exact
    theta_restart_gain 7646050560 7646312704 15 11414 33 (191113112361319 / 25000)
      (191119606196823 / 25000) (71117 / 3125) (2275747 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7646574848
    (h : (((191119606196823 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646312704) :
    (((764504447954237 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646574848 := by
  exact
    theta_restart_gain 7646312704 7646574848 15 11435 33 (191119606196823 / 25000)
      (764504447954237 / 100000) (2275747 / 100000) (9103 / 400) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7646836992
    (h : (((764504447954237 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7646574848) :
    (((23891585900267 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7646836992 := by
  exact
    theta_restart_gain 7646574848 7646836992 15 11557 33 (764504447954237 / 100000)
      (23891585900267 / 3125) (2275751 / 100000) (1137877 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7647099136
    (h : (((23891585900267 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7646836992) :
    (((95569637754983 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7647099136 := by
  exact
    theta_restart_gain 7646836992 7647099136 15 11580 33 (23891585900267 / 3125)
      (95569637754983 / 12500) (1137877 / 50000) (2275757 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7647361280
    (h : (((95569637754983 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7647099136) :
    (((382291721969357 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647361280 := by
  exact
    theta_restart_gain 7647099136 7647361280 15 11575 33 (95569637754983 / 12500)
      (382291721969357 / 50000) (1137879 / 50000) (2275761 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7647623424
    (h : (((382291721969357 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647361280) :
    (((191152398108151 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647623424 := by
  exact
    theta_restart_gain 7647361280 7647623424 15 11490 33 (382291721969357 / 50000)
      (191152398108151 / 25000) (2275761 / 100000) (568941 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7647885568
    (h : (((191152398108151 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647623424) :
    (((764635756902809 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647885568 := by
  exact
    theta_restart_gain 7647623424 7647885568 15 11497 33 (191152398108151 / 25000)
      (764635756902809 / 100000) (455153 / 20000) (284471 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7648147712
    (h : (((764635756902809 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7647885568) :
    (((764661828101017 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648147712 := by
  exact
    theta_restart_gain 7647885568 7648147712 15 11456 33 (764635756902809 / 100000)
      (764661828101017 / 100000) (284471 / 12500) (2275771 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7648409856
    (h : (((764661828101017 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648147712) :
    (((764688004019059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648409856 := by
  exact
    theta_restart_gain 7648147712 7648409856 15 11502 33 (764661828101017 / 100000)
      (764688004019059 / 100000) (2275771 / 100000) (1137887 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7648672000
    (h : (((764688004019059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648409856) :
    (((764714430318359 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648672000 := by
  exact
    theta_restart_gain 7648409856 7648672000 15 11612 33 (764688004019059 / 100000)
      (764714430318359 / 100000) (91031 / 4000) (1137889 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7648934144
    (h : (((764714430318359 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648672000) :
    (((764740330947777 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648934144 := by
  exact
    theta_restart_gain 7648672000 7648934144 15 11381 33 (764714430318359 / 100000)
      (764740330947777 / 100000) (1137889 / 50000) (2275781 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7649196288
    (h : (((764740330947777 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7648934144) :
    (((764766645815043 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649196288 := by
  exact
    theta_restart_gain 7648934144 7649196288 15 11563 33 (764740330947777 / 100000)
      (764766645815043 / 100000) (1137891 / 50000) (455157 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7649458432
    (h : (((764766645815043 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649196288) :
    (((764793003956913 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649458432 := by
  exact
    theta_restart_gain 7649196288 7649458432 15 11582 33 (764766645815043 / 100000)
      (764793003956913 / 100000) (455157 / 20000) (568947 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7649720576
    (h : (((764793003956913 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649458432) :
    (((764819189185147 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649720576 := by
  exact
    theta_restart_gain 7649458432 7649720576 15 11506 33 (764793003956913 / 100000)
      (764819189185147 / 100000) (2275789 / 100000) (142237 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7649982720
    (h : (((764819189185147 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649720576) :
    (((764845115007611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649982720 := by
  exact
    theta_restart_gain 7649720576 7649982720 15 11392 33 (764819189185147 / 100000)
      (764845115007611 / 100000) (142237 / 6250) (455159 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7650244864
    (h : (((764845115007611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7649982720) :
    (((95608929891047 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7650244864 := by
  exact
    theta_restart_gain 7649982720 7650244864 15 11567 33 (764845115007611 / 100000)
      (95608929891047 / 12500) (455159 / 20000) (1137899 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7650507008
    (h : (((95608929891047 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7650244864) :
    (((382448794029443 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7650507008 := by
  exact
    theta_restart_gain 7650244864 7650507008 15 11490 33 (95608929891047 / 12500)
      (382448794029443 / 50000) (2275799 / 100000) (1137901 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7650769152
    (h : (((382448794029443 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7650507008) :
    (((4780775162817 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7650769152 := by
  exact
    theta_restart_gain 7650507008 7650769152 15 11617 33 (382448794029443 / 50000)
      (4780775162817 / 625) (1137901 / 50000) (455161 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7651031296
    (h : (((4780775162817 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7650769152) :
    (((38247515580501 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7651031296 := by
  exact
    theta_restart_gain 7650769152 7651031296 15 11550 33 (4780775162817 / 625)
      (38247515580501 / 5000) (1137903 / 50000) (2275809 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7651293440
    (h : (((38247515580501 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7651031296) :
    (((95622090012207 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7651293440 := by
  exact
    theta_restart_gain 7651031296 7651293440 15 11604 33 (38247515580501 / 5000)
      (95622090012207 / 12500) (2275809 / 100000) (568953 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7651555584
    (h : (((95622090012207 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7651293440) :
    (((23906337813059 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7651555584 := by
  exact
    theta_restart_gain 7651293440 7651555584 15 11464 33 (95622090012207 / 12500)
      (23906337813059 / 3125) (2275813 / 100000) (284477 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7651817728
    (h : (((23906337813059 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7651555584) :
    (((95628620746397 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7651817728 := by
  exact
    theta_restart_gain 7651555584 7651817728 15 11493 33 (23906337813059 / 3125)
      (95628620746397 / 12500) (284477 / 12500) (2275819 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7652079872
    (h : (((95628620746397 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7651817728) :
    (((95631897925757 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7652079872 := by
  exact
    theta_restart_gain 7651817728 7652079872 15 11520 33 (95628620746397 / 12500)
      (95631897925757 / 12500) (2275819 / 100000) (1137911 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7652342016
    (h : (((95631897925757 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7652079872) :
    (((47817590969173 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7652342016 := by
  exact
    theta_restart_gain 7652079872 7652342016 15 11544 33 (95631897925757 / 12500)
      (47817590969173 / 6250) (2275823 / 100000) (1137913 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7652604160
    (h : (((47817590969173 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7652342016) :
    (((191276898911051 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7652604160 := by
  exact
    theta_restart_gain 7652342016 7652604160 15 11486 33 (47817590969173 / 6250)
      (191276898911051 / 25000) (1137913 / 50000) (2275829 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7652866304
    (h : (((191276898911051 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7652604160) :
    (((191283460128941 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7652866304 := by
  exact
    theta_restart_gain 7652604160 7652866304 15 11532 33 (191276898911051 / 25000)
      (191283460128941 / 25000) (227583 / 10000) (2275833 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7653128448
    (h : (((191283460128941 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7652866304) :
    (((382580067745123 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653128448 := by
  exact
    theta_restart_gain 7652866304 7653128448 15 11554 33 (191283460128941 / 25000)
      (382580067745123 / 50000) (2275833 / 100000) (568959 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7653390592
    (h : (((382580067745123 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653128448) :
    (((765186560233653 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653390592 := by
  exact
    theta_restart_gain 7653128448 7653390592 15 11611 33 (382580067745123 / 50000)
      (765186560233653 / 100000) (2275837 / 100000) (14224 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7653652736
    (h : (((765186560233653 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653390592) :
    (((765212782462133 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653652736 := by
  exact
    theta_restart_gain 7653390592 7653652736 15 11522 33 (765186560233653 / 100000)
      (765212782462133 / 100000) (14224 / 625) (2275843 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7653914880
    (h : (((765212782462133 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653652736) :
    (((382619512603883 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653914880 := by
  exact
    theta_restart_gain 7653652736 7653914880 15 11531 33 (765212782462133 / 100000)
      (382619512603883 / 50000) (2275843 / 100000) (1137923 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7654177024
    (h : (((382619512603883 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7653914880) :
    (((95658154801689 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7654177024 := by
  exact
    theta_restart_gain 7653914880 7654177024 15 11518 33 (382619512603883 / 50000)
      (95658154801689 / 12500) (2275847 / 100000) (45517 / 2000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7654439168
    (h : (((95658154801689 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7654177024) :
    (((191322828775703 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654439168 := by
  exact
    theta_restart_gain 7654177024 7654439168 15 11458 33 (95658154801689 / 12500)
      (191322828775703 / 25000) (45517 / 2000) (2275853 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7654701312
    (h : (((191322828775703 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654439168) :
    (((382658860918387 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654701312 := by
  exact
    theta_restart_gain 7654439168 7654701312 15 11603 33 (191322828775703 / 25000)
      (382658860918387 / 50000) (1137927 / 50000) (2275857 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7654963456
    (h : (((382658860918387 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654701312) :
    (((382671947096137 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654963456 := by
  exact
    theta_restart_gain 7654701312 7654963456 15 11500 33 (382658860918387 / 50000)
      (382671947096137 / 50000) (2275857 / 100000) (113793 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7655225600
    (h : (((382671947096137 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7654963456) :
    (((765369791214593 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655225600 := by
  exact
    theta_restart_gain 7654963456 7655225600 15 11379 33 (382671947096137 / 50000)
      (765369791214593 / 100000) (2275861 / 100000) (284483 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7655487744
    (h : (((765369791214593 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655225600) :
    (((765395786133201 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655487744 := by
  exact
    theta_restart_gain 7655225600 7655487744 15 11422 33 (765369791214593 / 100000)
      (765395786133201 / 100000) (284483 / 12500) (2275867 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7655749888
    (h : (((765395786133201 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655487744) :
    (((76542220212147 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655749888 := by
  exact
    theta_restart_gain 7655487744 7655749888 15 11607 33 (765395786133201 / 100000)
      (76542220212147 / 10000) (2275867 / 100000) (227587 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7656012032
    (h : (((76542220212147 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7655749888) :
    (((382724269250341 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656012032 := by
  exact
    theta_restart_gain 7655749888 7656012032 15 11572 33 (76542220212147 / 10000)
      (382724269250341 / 50000) (2275871 / 100000) (1137937 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7656274176
    (h : (((382724269250341 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656012032) :
    (((382737330491227 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656274176 := by
  exact
    theta_restart_gain 7656012032 7656274176 15 11478 33 (382724269250341 / 50000)
      (382737330491227 / 50000) (1137937 / 50000) (2275877 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7656536320
    (h : (((382737330491227 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656274176) :
    (((382750325754607 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656536320 := by
  exact
    theta_restart_gain 7656274176 7656536320 15 11420 33 (382737330491227 / 50000)
      (382750325754607 / 50000) (1137939 / 50000) (2275881 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7656798464
    (h : (((382750325754607 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656536320) :
    (((191381620689641 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656798464 := by
  exact
    theta_restart_gain 7656536320 7656798464 15 11350 33 (382750325754607 / 50000)
      (191381620689641 / 25000) (2275881 / 100000) (568971 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7657060608
    (h : (((191381620689641 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7656798464) :
    (((95694094160947 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7657060608 := by
  exact
    theta_restart_gain 7656798464 7657060608 15 11543 33 (191381620689641 / 25000)
      (95694094160947 / 12500) (568971 / 25000) (2275887 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7657322752
    (h : (((95694094160947 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7657060608) :
    (((95697375706957 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7657322752 := by
  exact
    theta_restart_gain 7657060608 7657322752 15 11535 33 (95694094160947 / 12500)
      (95697375706957 / 12500) (142243 / 6250) (2275891 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7657339136
    (h : (((95697375706957 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7657322752) :
    (((382790310769133 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7657339136 := by
  exact
    theta_restart_gain 7657322752 7657339136 11 710 33 (95697375706957 / 12500)
      (382790310769133 / 50000) (2275891 / 100000) (1137947 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7657341184
    (h : (((382790310769133 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7657339136) :
    (((382790423425787 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7657341184 := by
  exact
    theta_restart_gain 7657339136 7657341184 8 99 33 (382790310769133 / 50000)
      (382790423425787 / 50000) (568973 / 25000) (455179 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7657341184
    (h : (((381243490745971 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626389760) :
    (((382790423425787 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7657341184 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7657341184 point7657339136)
                  (Function.comp point7657322752 point7657060608))
                (Function.comp (Function.comp point7656798464 point7656536320)
                  (Function.comp point7656274176 point7656012032)))
              (Function.comp
                (Function.comp (Function.comp point7655749888 point7655487744)
                  (Function.comp point7655225600 point7654963456))
                (Function.comp (Function.comp point7654701312 point7654439168)
                  (Function.comp point7654177024 point7653914880))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7653652736 point7653390592)
                  (Function.comp point7653128448 point7652866304))
                (Function.comp (Function.comp point7652604160 point7652342016)
                  (Function.comp point7652079872 point7651817728)))
              (Function.comp
                (Function.comp (Function.comp point7651555584 point7651293440)
                  (Function.comp point7651031296 point7650769152))
                (Function.comp (Function.comp point7650507008 point7650244864)
                  (Function.comp point7649982720 point7649720576)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7649458432 point7649196288)
                  (Function.comp point7648934144 point7648672000))
                (Function.comp (Function.comp point7648409856 point7648147712)
                  (Function.comp point7647885568 point7647623424)))
              (Function.comp
                (Function.comp (Function.comp point7647361280 point7647099136)
                  (Function.comp point7646836992 point7646574848))
                (Function.comp (Function.comp point7646312704 point7646050560)
                  (Function.comp point7645788416 point7645526272))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7645264128 point7645001984)
                  (Function.comp point7644739840 point7644477696))
                (Function.comp (Function.comp point7644215552 point7643953408)
                  (Function.comp point7643691264 point7643429120)))
              (Function.comp
                (Function.comp (Function.comp point7643166976 point7642904832)
                  (Function.comp point7642642688 point7642380544))
                (Function.comp (Function.comp point7642118400 point7641856256)
                  (Function.comp point7641594112 point7641331968))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7641069824 point7640807680)
                  (Function.comp point7640545536 point7640283392))
                (Function.comp (Function.comp point7640021248 point7639759104)
                  (Function.comp point7639496960 point7639234816)))
              (Function.comp
                (Function.comp (Function.comp point7638972672 point7638710528)
                  (Function.comp point7638448384 point7638186240))
                (Function.comp (Function.comp point7637924096 point7637661952)
                  (Function.comp point7637399808 point7637137664))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7636875520 point7636613376)
                  (Function.comp point7636351232 point7636089088))
                (Function.comp (Function.comp point7635826944 point7635564800)
                  (Function.comp point7635302656 point7635040512)))
              (Function.comp
                (Function.comp (Function.comp point7634778368 point7634516224)
                  (Function.comp point7634254080 point7633991936))
                (Function.comp (Function.comp point7633729792 point7633467648)
                  (Function.comp point7633205504 point7632943360)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7632681216 point7632419072)
                  (Function.comp point7632156928 point7631894784))
                (Function.comp (Function.comp point7631632640 point7631370496)
                  (Function.comp point7631108352 point7630846208)))
              (Function.comp
                (Function.comp (Function.comp point7630584064 point7630321920)
                  (Function.comp point7630059776 point7629797632))
                (Function.comp (Function.comp point7629535488 point7629273344)
                  (Function.comp point7629011200 point7628749056))))
            (Function.comp
              (Function.comp (Function.comp point7628486912 point7628224768)
                (Function.comp point7627962624 point7627700480))
              (Function.comp (Function.comp point7627438336 point7627176192)
                (Function.comp point7626914048 point7626651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
