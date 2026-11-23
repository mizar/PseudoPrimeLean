/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7466389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434651904
    (h : (((185822562677281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434389760) :
    (((371658187923501 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434651904 := by
  exact
    theta_restart_gain 7434389760 7434651904 15 11494 33 (185822562677281 / 25000)
      (371658187923501 / 50000) (2272937 / 100000) (113647 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434914048
    (h : (((371658187923501 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434651904) :
    (((371671359610801 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434914048 := by
  exact
    theta_restart_gain 7434651904 7434914048 15 11590 33 (371658187923501 / 50000)
      (371671359610801 / 50000) (113647 / 5000) (2272943 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7435176192
    (h : (((371671359610801 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434914048) :
    (((74336903309429 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7435176192 := by
  exact
    theta_restart_gain 7434914048 7435176192 15 11577 33 (371671359610801 / 50000)
      (74336903309429 / 10000) (142059 / 6250) (2272947 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7435438336
    (h : (((74336903309429 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7435176192) :
    (((743395283359193 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7435438336 := by
  exact
    theta_restart_gain 7435176192 7435438336 15 11549 33 (74336903309429 / 10000)
      (743395283359193 / 100000) (2272947 / 100000) (45459 / 2000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7435700480
    (h : (((743395283359193 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7435438336) :
    (((23231917528938 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7435700480 := by
  exact
    theta_restart_gain 7435438336 7435700480 15 11473 33 (743395283359193 / 100000)
      (23231917528938 / 3125) (2272951 / 100000) (1136477 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7435962624
    (h : (((23231917528938 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7435700480) :
    (((46465474994187 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7435962624 := by
  exact
    theta_restart_gain 7435700480 7435962624 15 11544 33 (23231917528938 / 3125)
      (46465474994187 / 6250) (1136477 / 50000) (2272957 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7436224768
    (h : (((46465474994187 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7435962624) :
    (((37173692174003 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436224768 := by
  exact
    theta_restart_gain 7435962624 7436224768 15 11546 33 (46465474994187 / 6250)
      (37173692174003 / 5000) (1136479 / 50000) (2272961 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7436486912
    (h : (((37173692174003 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436224768) :
    (((371749916258067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436486912 := by
  exact
    theta_restart_gain 7436224768 7436486912 15 11434 33 (37173692174003 / 5000)
      (371749916258067 / 50000) (2272961 / 100000) (568241 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7436749056
    (h : (((371749916258067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436486912) :
    (((743526078442989 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436749056 := by
  exact
    theta_restart_gain 7436486912 7436749056 15 11547 33 (371749916258067 / 50000)
      (743526078442989 / 100000) (454593 / 20000) (284121 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7437011200
    (h : (((743526078442989 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7436749056) :
    (((743552274399189 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437011200 := by
  exact
    theta_restart_gain 7436749056 7437011200 15 11525 33 (743526078442989 / 100000)
      (743552274399189 / 100000) (284121 / 12500) (2272971 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7437273344
    (h : (((743552274399189 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437011200) :
    (((743578393120441 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437273344 := by
  exact
    theta_restart_gain 7437011200 7437273344 15 11491 33 (743552274399189 / 100000)
      (743578393120441 / 100000) (568243 / 25000) (90919 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7437535488
    (h : (((743578393120441 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437273344) :
    (((743604511887657 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437535488 := by
  exact
    theta_restart_gain 7437273344 7437535488 15 11491 33 (743578393120441 / 100000)
      (743604511887657 / 100000) (142061 / 6250) (2272979 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7437797632
    (h : (((743604511887657 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437535488) :
    (((371815347166379 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437797632 := by
  exact
    theta_restart_gain 7437535488 7437797632 15 11519 33 (743604511887657 / 100000)
      (371815347166379 / 50000) (2272979 / 100000) (1136491 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7438059776
    (h : (((371815347166379 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7437797632) :
    (((185914257278449 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438059776 := by
  exact
    theta_restart_gain 7437797632 7438059776 15 11586 33 (371815347166379 / 50000)
      (185914257278449 / 25000) (2272983 / 100000) (1136493 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7438321920
    (h : (((185914257278449 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438059776) :
    (((371841621730667 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438321920 := by
  exact
    theta_restart_gain 7438059776 7438321920 15 11533 33 (185914257278449 / 25000)
      (371841621730667 / 50000) (1136493 / 50000) (2272989 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7438584064
    (h : (((371841621730667 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438321920) :
    (((371854698242137 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438584064 := by
  exact
    theta_restart_gain 7438321920 7438584064 15 11506 33 (371841621730667 / 50000)
      (371854698242137 / 50000) (227299 / 10000) (2272993 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7438846208
    (h : (((371854698242137 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438584064) :
    (((148747160368791 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438846208 := by
  exact
    theta_restart_gain 7438584064 7438846208 15 11617 33 (371854698242137 / 50000)
      (148747160368791 / 20000) (2272993 / 100000) (568249 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7439108352
    (h : (((148747160368791 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7438846208) :
    (((148752406445867 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439108352 := by
  exact
    theta_restart_gain 7438846208 7439108352 15 11540 33 (148747160368791 / 20000)
      (148752406445867 / 20000) (2272997 / 100000) (2273 / 100) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7439370496
    (h : (((148752406445867 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439108352) :
    (((148757638437267 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439370496 := by
  exact
    theta_restart_gain 7439108352 7439370496 15 11509 33 (148752406445867 / 20000)
      (148757638437267 / 20000) (2273 / 100) (2273003 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7439632640
    (h : (((148757638437267 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439370496) :
    (((743814522664671 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439632640 := by
  exact
    theta_restart_gain 7439370496 7439632640 15 11584 33 (148757638437267 / 20000)
      (743814522664671 / 100000) (568251 / 25000) (2273007 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7439894784
    (h : (((743814522664671 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439632640) :
    (((371920423179369 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439894784 := by
  exact
    theta_restart_gain 7439632640 7439894784 15 11581 33 (743814522664671 / 100000)
      (371920423179369 / 50000) (2273007 / 100000) (227301 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7440156928
    (h : (((371920423179369 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7439894784) :
    (((185966788547013 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440156928 := by
  exact
    theta_restart_gain 7439894784 7440156928 15 11574 33 (371920423179369 / 50000)
      (185966788547013 / 25000) (2273011 / 100000) (1136507 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7440419072
    (h : (((185966788547013 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440156928) :
    (((185973275728969 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440419072 := by
  exact
    theta_restart_gain 7440156928 7440419072 15 11416 33 (185966788547013 / 25000)
      (185973275728969 / 25000) (1136507 / 50000) (2273017 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7440681216
    (h : (((185973275728969 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440419072) :
    (((371959608809839 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440681216 := by
  exact
    theta_restart_gain 7440419072 7440681216 15 11489 33 (185973275728969 / 25000)
      (371959608809839 / 50000) (1136509 / 50000) (2273021 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7440943360
    (h : (((371959608809839 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440681216) :
    (((185986395029309 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440943360 := by
  exact
    theta_restart_gain 7440681216 7440943360 15 11598 33 (371959608809839 / 50000)
      (185986395029309 / 25000) (2273021 / 100000) (71032 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7441205504
    (h : (((185986395029309 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7440943360) :
    (((46498230221021 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7441205504 := by
  exact
    theta_restart_gain 7440943360 7441205504 15 11484 33 (185986395029309 / 25000)
      (46498230221021 / 6250) (90921 / 4000) (568257 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7441467648
    (h : (((46498230221021 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7441205504) :
    (((185999454134813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7441467648 := by
  exact
    theta_restart_gain 7441205504 7441467648 15 11497 33 (46498230221021 / 6250)
      (185999454134813 / 25000) (568257 / 25000) (2273031 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7441729792
    (h : (((185999454134813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7441467648) :
    (((186006018082971 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7441729792 := by
  exact
    theta_restart_gain 7441467648 7441729792 15 11551 33 (185999454134813 / 25000)
      (186006018082971 / 25000) (284129 / 12500) (454607 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7441991936
    (h : (((186006018082971 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7441729792) :
    (((93006324263033 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7441991936 := by
  exact
    theta_restart_gain 7441729792 7441991936 15 11668 33 (186006018082971 / 25000)
      (93006324263033 / 12500) (454607 / 20000) (1136519 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7442254080
    (h : (((93006324263033 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7441991936) :
    (((744076649950321 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442254080 := by
  exact
    theta_restart_gain 7441991936 7442254080 15 11463 33 (93006324263033 / 12500)
      (744076649950321 / 100000) (2273039 / 100000) (1136521 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7442516224
    (h : (((744076649950321 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442254080) :
    (((744102671735137 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442516224 := by
  exact
    theta_restart_gain 7442254080 7442516224 15 11448 33 (744076649950321 / 100000)
      (744102671735137 / 100000) (1136521 / 50000) (454609 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7442778368
    (h : (((744102671735137 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442516224) :
    (((744129054980059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442778368 := by
  exact
    theta_restart_gain 7442516224 7442778368 15 11607 33 (744102671735137 / 100000)
      (744129054980059 / 100000) (1136523 / 50000) (2273049 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7443040512
    (h : (((744129054980059 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7442778368) :
    (((744155249608259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7443040512 := by
  exact
    theta_restart_gain 7442778368 7443040512 15 11524 33 (744129054980059 / 100000)
      (744155249608259 / 100000) (45461 / 2000) (2273053 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7443302656
    (h : (((744155249608259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7443040512) :
    (((744181453363243 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7443302656 := by
  exact
    theta_restart_gain 7443040512 7443302656 15 11528 33 (744155249608259 / 100000)
      (744181453363243 / 100000) (2273053 / 100000) (71033 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7443564800
    (h : (((744181453363243 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7443302656) :
    (((46512978146573 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7443564800 := by
  exact
    theta_restart_gain 7443302656 7443564800 15 11525 33 (744181453363243 / 100000)
      (46512978146573 / 6250) (2273057 / 100000) (113653 / 5000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7443826944
    (h : (((46512978146573 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7443564800) :
    (((93029242569641 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7443826944 := by
  exact
    theta_restart_gain 7443564800 7443826944 15 11566 33 (46512978146573 / 6250)
      (93029242569641 / 12500) (113653 / 5000) (2273063 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7444089088
    (h : (((93029242569641 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7443826944) :
    (((93032515781801 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7444089088 := by
  exact
    theta_restart_gain 7443826944 7444089088 15 11520 33 (93029242569641 / 12500)
      (93032515781801 / 12500) (284133 / 12500) (2273067 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7444351232
    (h : (((93032515781801 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7444089088) :
    (((744286332443851 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444351232 := by
  exact
    theta_restart_gain 7444089088 7444351232 15 11529 33 (93032515781801 / 12500)
      (744286332443851 / 100000) (2273067 / 100000) (227307 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7444613376
    (h : (((744286332443851 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444351232) :
    (((29772502911019 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444613376 := by
  exact
    theta_restart_gain 7444351232 7444613376 15 11544 33 (744286332443851 / 100000)
      (29772502911019 / 4000) (2273071 / 100000) (1136537 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7444875520
    (h : (((29772502911019 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444613376) :
    (((744338831326323 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444875520 := by
  exact
    theta_restart_gain 7444613376 7444875520 15 11552 33 (29772502911019 / 4000)
      (744338831326323 / 100000) (1136537 / 50000) (2273077 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7445137664
    (h : (((744338831326323 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7444875520) :
    (((148873005255439 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445137664 := by
  exact
    theta_restart_gain 7444875520 7445137664 15 11524 33 (744338831326323 / 100000)
      (148873005255439 / 20000) (1136539 / 50000) (2273081 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7445399808
    (h : (((148873005255439 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445137664) :
    (((148878210610929 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445399808 := by
  exact
    theta_restart_gain 7445137664 7445399808 15 11450 33 (148873005255439 / 20000)
      (148878210610929 / 20000) (2273081 / 100000) (568271 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7445661952
    (h : (((148878210610929 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445399808) :
    (((74441742311373 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445661952 := by
  exact
    theta_restart_gain 7445399808 7445661952 15 11601 33 (148878210610929 / 20000)
      (74441742311373 / 10000) (454617 / 20000) (71034 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7445924096
    (h : (((74441742311373 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445661952) :
    (((372221811363009 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445924096 := by
  exact
    theta_restart_gain 7445661952 7445924096 15 11526 33 (74441742311373 / 10000)
      (372221811363009 / 50000) (71034 / 3125) (2273091 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7446186240
    (h : (((372221811363009 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7445924096) :
    (((372234937332763 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446186240 := by
  exact
    theta_restart_gain 7445924096 7446186240 15 11549 33 (372221811363009 / 50000)
      (372234937332763 / 50000) (568273 / 25000) (454619 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7446448384
    (h : (((372234937332763 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446186240) :
    (((744496135732061 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446448384 := by
  exact
    theta_restart_gain 7446186240 7446448384 15 11553 33 (372234937332763 / 50000)
      (744496135732061 / 100000) (454619 / 20000) (1136549 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7446710528
    (h : (((744496135732061 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446448384) :
    (((744522430941293 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446710528 := by
  exact
    theta_restart_gain 7446448384 7446710528 15 11568 33 (744496135732061 / 100000)
      (744522430941293 / 100000) (2273099 / 100000) (1136551 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7446972672
    (h : (((744522430941293 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446710528) :
    (((744548817109309 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446972672 := by
  exact
    theta_restart_gain 7446710528 7446972672 15 11608 33 (744522430941293 / 100000)
      (744548817109309 / 100000) (1136551 / 50000) (454621 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7447234816
    (h : (((744548817109309 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7446972672) :
    (((744575246512771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7447234816 := by
  exact
    theta_restart_gain 7446972672 7447234816 15 11627 33 (744548817109309 / 100000)
      (744575246512771 / 100000) (1136553 / 50000) (2273109 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7447496960
    (h : (((744575246512771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7447234816) :
    (((74460150319483 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7447496960 := by
  exact
    theta_restart_gain 7447234816 7447496960 15 11551 33 (744575246512771 / 100000)
      (74460150319483 / 10000) (2273109 / 100000) (284139 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7447759104
    (h : (((74460150319483 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7447496960) :
    (((46539228602063 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7447759104 := by
  exact
    theta_restart_gain 7447496960 7447759104 15 11506 33 (74460150319483 / 10000)
      (46539228602063 / 6250) (2273113 / 100000) (568279 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7448021248
    (h : (((46539228602063 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7447759104) :
    (((1861634564361 / 250) : ℚ) : ℝ) ≤ Chebyshev.theta 7448021248 := by
  exact
    theta_restart_gain 7447759104 7448021248 15 11512 33 (46539228602063 / 6250)
      (1861634564361 / 250) (568279 / 25000) (2273119 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7448283392
    (h : (((1861634564361 / 250) : ℚ) : ℝ) ≤ Chebyshev.theta 7448021248) :
    (((9308499525977 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7448283392 := by
  exact
    theta_restart_gain 7448021248 7448283392 15 11498 33 (1861634564361 / 250)
      (9308499525977 / 1250) (14207 / 625) (2273123 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7448545536
    (h : (((9308499525977 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7448283392) :
    (((744706191644457 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7448545536 := by
  exact
    theta_restart_gain 7448283392 7448545536 15 11539 33 (9308499525977 / 1250)
      (744706191644457 / 100000) (2273123 / 100000) (1136563 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7448807680
    (h : (((744706191644457 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7448545536) :
    (((372366328831059 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7448807680 := by
  exact
    theta_restart_gain 7448545536 7448807680 15 11643 33 (744706191644457 / 100000)
      (372366328831059 / 50000) (2273127 / 100000) (227313 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7449069824
    (h : (((372366328831059 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7448807680) :
    (((186189751377987 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7449069824 := by
  exact
    theta_restart_gain 7448807680 7449069824 15 11591 33 (372366328831059 / 50000)
      (186189751377987 / 25000) (227313 / 10000) (2273133 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7449331968
    (h : (((186189751377987 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7449069824) :
    (((4654909126534 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7449331968 := by
  exact
    theta_restart_gain 7449069824 7449331968 15 11638 33 (186189751377987 / 25000)
      (4654909126534 / 625) (1136567 / 50000) (2273137 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7449594112
    (h : (((4654909126534 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7449331968) :
    (((46550708603027 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7449594112 := by
  exact
    theta_restart_gain 7449331968 7449594112 15 11384 33 (4654909126534 / 625)
      (46550708603027 / 6250) (1136569 / 50000) (2273141 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7449856256
    (h : (((46550708603027 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7449594112) :
    (((744837117340513 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7449856256 := by
  exact
    theta_restart_gain 7449594112 7449856256 15 11341 33 (46550708603027 / 6250)
      (744837117340513 / 100000) (2273141 / 100000) (284143 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7450118400
    (h : (((744837117340513 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7449856256) :
    (((744863372165263 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450118400 := by
  exact
    theta_restart_gain 7449856256 7450118400 15 11550 33 (744837117340513 / 100000)
      (744863372165263 / 100000) (454629 / 20000) (568287 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7450380544
    (h : (((744863372165263 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450118400) :
    (((148977940862339 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450380544 := by
  exact
    theta_restart_gain 7450118400 7450380544 15 11584 33 (744863372165263 / 100000)
      (148977940862339 / 20000) (568287 / 25000) (2273151 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7450642688
    (h : (((148977940862339 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450380544) :
    (((148983203209219 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450642688 := by
  exact
    theta_restart_gain 7450380544 7450642688 15 11575 33 (148977940862339 / 20000)
      (148983203209219 / 20000) (71036 / 3125) (454631 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7450904832
    (h : (((148983203209219 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450642688) :
    (((74494228689843 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450904832 := by
  exact
    theta_restart_gain 7450642688 7450904832 15 11557 33 (148983203209219 / 20000)
      (74494228689843 / 10000) (454631 / 20000) (1136579 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7451166976
    (h : (((74494228689843 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7450904832) :
    (((744968566889629 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451166976 := by
  exact
    theta_restart_gain 7450904832 7451166976 15 11561 33 (74494228689843 / 10000)
      (744968566889629 / 100000) (2273159 / 100000) (1136581 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7451429120
    (h : (((744968566889629 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451166976) :
    (((744994671882037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451429120 := by
  exact
    theta_restart_gain 7451166976 7451429120 15 11484 33 (744968566889629 / 100000)
      (744994671882037 / 100000) (1136581 / 50000) (454633 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7451691264
    (h : (((744994671882037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451429120) :
    (((745020560969611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451691264 := by
  exact
    theta_restart_gain 7451429120 7451691264 15 11389 33 (744994671882037 / 100000)
      (745020560969611 / 100000) (1136583 / 50000) (2273169 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7451953408
    (h : (((745020560969611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451691264) :
    (((745047188871277 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451953408 := by
  exact
    theta_restart_gain 7451691264 7451953408 15 11714 33 (745020560969611 / 100000)
      (745047188871277 / 100000) (2273169 / 100000) (568293 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7452215552
    (h : (((745047188871277 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7451953408) :
    (((372536861809853 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452215552 := by
  exact
    theta_restart_gain 7451953408 7452215552 15 11673 33 (745047188871277 / 100000)
      (372536861809853 / 50000) (2273173 / 100000) (284147 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7452477696
    (h : (((372536861809853 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452215552) :
    (((74509997652933 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452477696 := by
  exact
    theta_restart_gain 7452215552 7452477696 15 11549 33 (372536861809853 / 50000)
      (74509997652933 / 10000) (284147 / 12500) (2273179 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7452739840
    (h : (((74509997652933 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452477696) :
    (((74512589078133 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452739840 := by
  exact
    theta_restart_gain 7452477696 7452739840 15 11400 33 (74509997652933 / 10000)
      (74512589078133 / 10000) (113659 / 5000) (2273183 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7453001984
    (h : (((74512589078133 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7452739840) :
    (((372576125305699 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453001984 := by
  exact
    theta_restart_gain 7452739840 7453001984 15 11596 33 (74512589078133 / 10000)
      (372576125305699 / 50000) (2273183 / 100000) (1136593 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7453264128
    (h : (((372576125305699 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453001984) :
    (((46573645254143 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7453264128 := by
  exact
    theta_restart_gain 7453001984 7453264128 15 11470 33 (372576125305699 / 50000)
      (46573645254143 / 6250) (2273187 / 100000) (227319 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7453526272
    (h : (((46573645254143 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7453264128) :
    (((186301108481657 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453526272 := by
  exact
    theta_restart_gain 7453264128 7453526272 15 11486 33 (46573645254143 / 6250)
      (186301108481657 / 25000) (227319 / 10000) (2273193 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7453788416
    (h : (((186301108481657 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453526272) :
    (((372615454908573 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453788416 := by
  exact
    theta_restart_gain 7453526272 7453788416 15 11647 33 (186301108481657 / 25000)
      (372615454908573 / 50000) (1136597 / 50000) (2273197 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7454050560
    (h : (((372615454908573 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7453788416) :
    (((37262864172437 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454050560 := by
  exact
    theta_restart_gain 7453788416 7454050560 15 11602 33 (372615454908573 / 50000)
      (37262864172437 / 5000) (2273197 / 100000) (5683 / 250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7454312704
    (h : (((37262864172437 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454050560) :
    (((372641601243271 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454312704 := by
  exact
    theta_restart_gain 7454050560 7454312704 15 11402 33 (37262864172437 / 5000)
      (372641601243271 / 50000) (2273201 / 100000) (568301 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7454574848
    (h : (((372641601243271 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454312704) :
    (((372654707400933 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454574848 := by
  exact
    theta_restart_gain 7454312704 7454574848 15 11531 33 (372641601243271 / 50000)
      (372654707400933 / 50000) (568301 / 25000) (2273207 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7454836992
    (h : (((372654707400933 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454574848) :
    (((372667807898637 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454836992 := by
  exact
    theta_restart_gain 7454574848 7454836992 15 11526 33 (372654707400933 / 50000)
      (372667807898637 / 50000) (284151 / 12500) (2273211 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7455099136
    (h : (((372667807898637 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7454836992) :
    (((745361950946709 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7455099136 := by
  exact
    theta_restart_gain 7454836992 7455099136 15 11585 33 (372667807898637 / 50000)
      (745361950946709 / 100000) (2273211 / 100000) (1136607 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7455361280
    (h : (((745361950946709 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7455099136) :
    (((93173539177633 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7455361280 := by
  exact
    theta_restart_gain 7455099136 7455361280 15 11597 33 (745361950946709 / 100000)
      (93173539177633 / 12500) (454643 / 20000) (1136609 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7455623424
    (h : (((93173539177633 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7455361280) :
    (((46588404600863 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7455623424 := by
  exact
    theta_restart_gain 7455361280 7455623424 15 11508 33 (93173539177633 / 12500)
      (46588404600863 / 6250) (1136609 / 50000) (2273221 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7455885568
    (h : (((46588404600863 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7455623424) :
    (((74544057247559 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7455885568 := by
  exact
    theta_restart_gain 7455623424 7455885568 15 11481 33 (46588404600863 / 6250)
      (74544057247559 / 10000) (1136611 / 50000) (90929 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7456147712
    (h : (((74544057247559 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7455885568) :
    (((149093353369453 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456147712 := by
  exact
    theta_restart_gain 7455885568 7456147712 15 11523 33 (74544057247559 / 10000)
      (149093353369453 / 20000) (90929 / 4000) (568307 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7456409856
    (h : (((149093353369453 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456147712) :
    (((149098545424489 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456409856 := by
  exact
    theta_restart_gain 7456147712 7456409856 15 11420 33 (149093353369453 / 20000)
      (149098545424489 / 20000) (2273229 / 100000) (142077 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7456672000
    (h : (((149098545424489 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456409856) :
    (((29820756135557 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456672000 := by
  exact
    theta_restart_gain 7456409856 7456672000 15 11515 33 (149098545424489 / 20000)
      (29820756135557 / 4000) (142077 / 6250) (454647 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7456934144
    (h : (((29820756135557 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456672000) :
    (((745545031963509 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456934144 := by
  exact
    theta_restart_gain 7456672000 7456934144 15 11494 33 (29820756135557 / 4000)
      (745545031963509 / 100000) (568309 / 25000) (2273239 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7457196288
    (h : (((745545031963509 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7456934144) :
    (((745571167403789 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457196288 := by
  exact
    theta_restart_gain 7456934144 7457196288 15 11497 33 (745545031963509 / 100000)
      (745571167403789 / 100000) (56831 / 2500) (2273243 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7457458432
    (h : (((745571167403789 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457196288) :
    (((745597227861541 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457458432 := by
  exact
    theta_restart_gain 7457196288 7457458432 15 11464 33 (745571167403789 / 100000)
      (745597227861541 / 100000) (2273243 / 100000) (1136623 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7457720576
    (h : (((745597227861541 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457458432) :
    (((372811747615313 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457720576 := by
  exact
    theta_restart_gain 7457458432 7457720576 15 11555 33 (745597227861541 / 100000)
      (372811747615313 / 50000) (2273247 / 100000) (9093 / 400) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7457982720
    (h : (((372811747615313 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457720576) :
    (((186412425882469 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457982720 := by
  exact
    theta_restart_gain 7457720576 7457982720 15 11529 33 (372811747615313 / 50000)
      (186412425882469 / 25000) (9093 / 400) (2273253 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7458244864
    (h : (((186412425882469 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7457982720) :
    (((93209501771459 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7458244864 := by
  exact
    theta_restart_gain 7457982720 7458244864 15 11574 33 (186412425882469 / 25000)
      (93209501771459 / 12500) (1136627 / 50000) (2273257 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7458507008
    (h : (((93209501771459 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7458244864) :
    (((149140435417297 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7458507008 := by
  exact
    theta_restart_gain 7458244864 7458507008 15 11509 33 (93209501771459 / 12500)
      (149140435417297 / 20000) (2273257 / 100000) (113663 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7458769152
    (h : (((149140435417297 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7458507008) :
    (((372864183663233 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7458769152 := by
  exact
    theta_restart_gain 7458507008 7458769152 15 11521 33 (149140435417297 / 20000)
      (372864183663233 / 50000) (2273261 / 100000) (142079 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7459031296
    (h : (((372864183663233 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7458769152) :
    (((372877271980713 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459031296 := by
  exact
    theta_restart_gain 7458769152 7459031296 15 11515 33 (372864183663233 / 50000)
      (372877271980713 / 50000) (142079 / 6250) (2273267 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7459293440
    (h : (((372877271980713 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459031296) :
    (((372890356911321 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459293440 := by
  exact
    theta_restart_gain 7459031296 7459293440 15 11512 33 (372877271980713 / 50000)
      (372890356911321 / 50000) (568317 / 25000) (2273271 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7459555584
    (h : (((372890356911321 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459293440) :
    (((745807040574093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459555584 := by
  exact
    theta_restart_gain 7459293440 7459555584 15 11581 33 (372890356911321 / 50000)
      (745807040574093 / 100000) (2273271 / 100000) (1136637 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7459817728
    (h : (((745807040574093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459555584) :
    (((745833346912393 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459817728 := by
  exact
    theta_restart_gain 7459555584 7459817728 15 11572 33 (745807040574093 / 100000)
      (745833346912393 / 100000) (90931 / 4000) (1136639 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7460079872
    (h : (((745833346912393 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7459817728) :
    (((745859955631383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460079872 := by
  exact
    theta_restart_gain 7459817728 7460079872 15 11705 33 (745833346912393 / 100000)
      (745859955631383 / 100000) (1136639 / 50000) (2273281 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7460342016
    (h : (((745859955631383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460079872) :
    (((745886057455307 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460342016 := by
  exact
    theta_restart_gain 7460079872 7460342016 15 11482 33 (745859955631383 / 100000)
      (745886057455307 / 100000) (1136641 / 50000) (454657 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7460604160
    (h : (((745886057455307 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460342016) :
    (((186478036986813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460604160 := by
  exact
    theta_restart_gain 7460342016 7460604160 15 11477 33 (745886057455307 / 100000)
      (186478036986813 / 25000) (454657 / 20000) (284161 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7460866304
    (h : (((186478036986813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7460604160) :
    (((23310576133164 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7460866304 := by
  exact
    theta_restart_gain 7460604160 7460866304 15 11564 33 (186478036986813 / 25000)
      (23310576133164 / 3125) (2273289 / 100000) (568323 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7461128448
    (h : (((23310576133164 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7460866304) :
    (((93245547952017 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7461128448 := by
  exact
    theta_restart_gain 7460866304 7461128448 15 11414 33 (23310576133164 / 3125)
      (93245547952017 / 12500) (568323 / 25000) (454659 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7461390592
    (h : (((93245547952017 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7461128448) :
    (((93248808710967 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7461390592 := by
  exact
    theta_restart_gain 7461128448 7461390592 15 11475 33 (93245547952017 / 12500)
      (93248808710967 / 12500) (142081 / 6250) (2273299 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7461652736
    (h : (((93248808710967 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7461390592) :
    (((186504180436147 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7461652736 := by
  exact
    theta_restart_gain 7461390592 7461652736 15 11548 33 (93248808710967 / 12500)
      (186504180436147 / 25000) (2273299 / 100000) (1136651 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7461914880
    (h : (((186504180436147 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7461652736) :
    (((373021420998029 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7461914880 := by
  exact
    theta_restart_gain 7461652736 7461914880 15 11490 33 (186504180436147 / 25000)
      (373021420998029 / 50000) (2273303 / 100000) (1136653 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7462177024
    (h : (((373021420998029 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7461914880) :
    (((4662933244944 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7462177024 := by
  exact
    theta_restart_gain 7461914880 7462177024 15 11647 33 (373021420998029 / 50000)
      (4662933244944 / 625) (1136653 / 50000) (2273309 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7462439168
    (h : (((4662933244944 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7462177024) :
    (((14921905653291 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462439168 := by
  exact
    theta_restart_gain 7462177024 7462439168 15 11421 33 (4662933244944 / 625)
      (14921905653291 / 2000) (227331 / 10000) (2273313 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7462701312
    (h : (((14921905653291 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462439168) :
    (((373060658322513 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462701312 := by
  exact
    theta_restart_gain 7462439168 7462701312 15 11452 33 (14921905653291 / 2000)
      (373060658322513 / 50000) (2273313 / 100000) (568329 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7462963456
    (h : (((373060658322513 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462701312) :
    (((373073761721701 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462963456 := by
  exact
    theta_restart_gain 7462701312 7462963456 15 11528 33 (373060658322513 / 50000)
      (373073761721701 / 50000) (2273317 / 100000) (56833 / 2500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7463225600
    (h : (((373073761721701 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7462963456) :
    (((373087027680561 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463225600 := by
  exact
    theta_restart_gain 7462963456 7463225600 15 11671 33 (373073761721701 / 50000)
      (373087027680561 / 50000) (56833 / 2500) (2273323 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7463487744
    (h : (((373087027680561 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463225600) :
    (((373100035640489 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463487744 := by
  exact
    theta_restart_gain 7463225600 7463487744 15 11444 33 (373087027680561 / 50000)
      (373100035640489 / 50000) (568331 / 25000) (2273327 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7463749888
    (h : (((373100035640489 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463487744) :
    (((149245229722999 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463749888 := by
  exact
    theta_restart_gain 7463487744 7463749888 15 11471 33 (373100035640489 / 50000)
      (149245229722999 / 20000) (2273327 / 100000) (227333 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7464012032
    (h : (((149245229722999 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7463749888) :
    (((746252523801257 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464012032 := by
  exact
    theta_restart_gain 7463749888 7464012032 15 11602 33 (149245229722999 / 20000)
      (746252523801257 / 100000) (2273331 / 100000) (1136667 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7464274176
    (h : (((746252523801257 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464012032) :
    (((746278573935563 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464274176 := by
  exact
    theta_restart_gain 7464012032 7464274176 15 11459 33 (746252523801257 / 100000)
      (746278573935563 / 100000) (1136667 / 50000) (2273337 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7464536320
    (h : (((746278573935563 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464274176) :
    (((746304742329281 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464536320 := by
  exact
    theta_restart_gain 7464274176 7464536320 15 11511 33 (746278573935563 / 100000)
      (746304742329281 / 100000) (1136669 / 50000) (2273341 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7464798464
    (h : (((746304742329281 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464536320) :
    (((37316546447213 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464798464 := by
  exact
    theta_restart_gain 7464536320 7464798464 15 11519 33 (746304742329281 / 100000)
      (37316546447213 / 5000) (2273341 / 100000) (71042 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7465060608
    (h : (((37316546447213 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7464798464) :
    (((149271424030401 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465060608 := by
  exact
    theta_restart_gain 7464798464 7465060608 15 11521 33 (37316546447213 / 5000)
      (149271424030401 / 20000) (454669 / 20000) (568337 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7465322752
    (h : (((149271424030401 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465060608) :
    (((746383450068541 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465322752 := by
  exact
    theta_restart_gain 7465060608 7465322752 15 11582 33 (149271424030401 / 20000)
      (746383450068541 / 100000) (568337 / 25000) (2273351 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7465584896
    (h : (((746383450068541 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465322752) :
    (((746409668637157 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465584896 := by
  exact
    theta_restart_gain 7465322752 7465584896 15 11533 33 (746383450068541 / 100000)
      (746409668637157 / 100000) (284169 / 12500) (454671 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7465847040
    (h : (((746409668637157 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465584896) :
    (((373217804945531 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465847040 := by
  exact
    theta_restart_gain 7465584896 7465847040 15 11411 33 (746409668637157 / 100000)
      (373217804945531 / 50000) (454671 / 20000) (1136679 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466109184
    (h : (((373217804945531 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7465847040) :
    (((37323099270109 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466109184 := by
  exact
    theta_restart_gain 7465847040 7466109184 15 11602 33 (373217804945531 / 50000)
      (37323099270109 / 5000) (2273359 / 100000) (1136681 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466371328
    (h : (((37323099270109 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466109184) :
    (((37324417820069 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466371328 := by
  exact
    theta_restart_gain 7466109184 7466371328 15 11600 33 (37323099270109 / 5000)
      (37324417820069 / 5000) (1136681 / 50000) (454673 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466387712
    (h : (((37324417820069 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466371328) :
    (((373245031849623 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466387712 := by
  exact
    theta_restart_gain 7466371328 7466387712 11 751 33 (37324417820069 / 5000)
      (373245031849623 / 50000) (1136683 / 50000) (2273369 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7466389760
    (h : (((373245031849623 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7466387712) :
    (((93311287231993 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7466389760 := by
  exact
    theta_restart_gain 7466387712 7466389760 8 103 33 (373245031849623 / 50000)
      (93311287231993 / 12500) (1136683 / 50000) (2273369 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7466389760
    (h : (((185822562677281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434389760) :
    (((93311287231993 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7466389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7466389760 point7466387712)
                  (Function.comp point7466371328 point7466109184))
                (Function.comp (Function.comp point7465847040 point7465584896)
                  (Function.comp point7465322752 point7465060608)))
              (Function.comp
                (Function.comp (Function.comp point7464798464 point7464536320)
                  (Function.comp point7464274176 point7464012032))
                (Function.comp (Function.comp point7463749888 point7463487744)
                  (Function.comp point7463225600 point7462963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7462701312 point7462439168)
                  (Function.comp point7462177024 point7461914880))
                (Function.comp (Function.comp point7461652736 point7461390592)
                  (Function.comp point7461128448 point7460866304)))
              (Function.comp
                (Function.comp (Function.comp point7460604160 point7460342016)
                  (Function.comp point7460079872 point7459817728))
                (Function.comp (Function.comp point7459555584 point7459293440)
                  (Function.comp point7459031296 point7458769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7458507008 point7458244864)
                  (Function.comp point7457982720 point7457720576))
                (Function.comp (Function.comp point7457458432 point7457196288)
                  (Function.comp point7456934144 point7456672000)))
              (Function.comp
                (Function.comp (Function.comp point7456409856 point7456147712)
                  (Function.comp point7455885568 point7455623424))
                (Function.comp (Function.comp point7455361280 point7455099136)
                  (Function.comp point7454836992 point7454574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7454312704 point7454050560)
                  (Function.comp point7453788416 point7453526272))
                (Function.comp (Function.comp point7453264128 point7453001984)
                  (Function.comp point7452739840 point7452477696)))
              (Function.comp
                (Function.comp (Function.comp point7452215552 point7451953408)
                  (Function.comp point7451691264 point7451429120))
                (Function.comp (Function.comp point7451166976 point7450904832)
                  (Function.comp point7450642688 point7450380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7450118400 point7449856256)
                  (Function.comp point7449594112 point7449331968))
                (Function.comp (Function.comp point7449069824 point7448807680)
                  (Function.comp point7448545536 point7448283392)))
              (Function.comp
                (Function.comp (Function.comp point7448021248 point7447759104)
                  (Function.comp point7447496960 point7447234816))
                (Function.comp (Function.comp point7446972672 point7446710528)
                  (Function.comp point7446448384 point7446186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7445924096 point7445661952)
                  (Function.comp point7445399808 point7445137664))
                (Function.comp (Function.comp point7444875520 point7444613376)
                  (Function.comp point7444351232 point7444089088)))
              (Function.comp
                (Function.comp (Function.comp point7443826944 point7443564800)
                  (Function.comp point7443302656 point7443040512))
                (Function.comp (Function.comp point7442778368 point7442516224)
                  (Function.comp point7442254080 point7441991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7441729792 point7441467648)
                  (Function.comp point7441205504 point7440943360))
                (Function.comp (Function.comp point7440681216 point7440419072)
                  (Function.comp point7440156928 point7439894784)))
              (Function.comp
                (Function.comp (Function.comp point7439632640 point7439370496)
                  (Function.comp point7439108352 point7438846208))
                (Function.comp (Function.comp point7438584064 point7438321920)
                  (Function.comp point7438059776 point7437797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7437535488 point7437273344)
                  (Function.comp point7437011200 point7436749056))
                (Function.comp (Function.comp point7436486912 point7436224768)
                  (Function.comp point7435962624 point7435700480)))
              (Function.comp (Function.comp point7435438336 point7435176192)
                (Function.comp point7434914048 point7434651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
