/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7626389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594651904
    (h : (((47455422479953 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7594389760) :
    (((15186258322261 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594651904 := by
  exact
    theta_restart_gain 7594389760 7594651904 15 11497 33 (47455422479953 / 6250)
      (15186258322261 / 2000) (1137533 / 50000) (2275069 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594914048
    (h : (((15186258322261 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594651904) :
    (((75933902481637 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594914048 := by
  exact
    theta_restart_gain 7594651904 7594914048 15 11476 33 (15186258322261 / 2000)
      (75933902481637 / 10000) (227507 / 10000) (2275073 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7595176192
    (h : (((75933902481637 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594914048) :
    (((9492066273869 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7595176192 := by
  exact
    theta_restart_gain 7594914048 7595176192 15 11550 33 (75933902481637 / 10000)
      (9492066273869 / 1250) (2275073 / 100000) (568769 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7595438336
    (h : (((9492066273869 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7595176192) :
    (((189847825938281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595438336 := by
  exact
    theta_restart_gain 7595176192 7595438336 15 11429 33 (9492066273869 / 1250)
      (189847825938281 / 25000) (568769 / 25000) (2275079 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7595700480
    (h : (((189847825938281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595438336) :
    (((189854388975311 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595700480 := by
  exact
    theta_restart_gain 7595438336 7595700480 15 11539 33 (189847825938281 / 25000)
      (189854388975311 / 25000) (56877 / 2500) (2275083 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7595962624
    (h : (((189854388975311 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595700480) :
    (((151888737955933 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595962624 := by
  exact
    theta_restart_gain 7595700480 7595962624 15 11487 33 (189854388975311 / 25000)
      (151888737955933 / 20000) (2275083 / 100000) (1137543 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7596224768
    (h : (((151888737955933 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7595962624) :
    (((15189399568199 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596224768 := by
  exact
    theta_restart_gain 7595962624 7596224768 15 11555 33 (151888737955933 / 20000)
      (15189399568199 / 2000) (2275087 / 100000) (227509 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7596486912
    (h : (((15189399568199 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596224768) :
    (((75949615104531 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596486912 := by
  exact
    theta_restart_gain 7596224768 7596486912 15 11504 33 (15189399568199 / 2000)
      (75949615104531 / 10000) (227509 / 10000) (2275093 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7596749056
    (h : (((75949615104531 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596486912) :
    (((379761155038061 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596749056 := by
  exact
    theta_restart_gain 7596486912 7596749056 15 11498 33 (75949615104531 / 10000)
      (379761155038061 / 50000) (1137547 / 50000) (2275097 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7597011200
    (h : (((379761155038061 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7596749056) :
    (((759548680725449 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597011200 := by
  exact
    theta_restart_gain 7596749056 7597011200 15 11591 33 (379761155038061 / 50000)
      (759548680725449 / 100000) (2275097 / 100000) (22751 / 1000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7597273344
    (h : (((759548680725449 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597011200) :
    (((759574826186141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597273344 := by
  exact
    theta_restart_gain 7597011200 7597273344 15 11492 33 (759548680725449 / 100000)
      (759574826186141 / 100000) (2275101 / 100000) (71097 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7597535488
    (h : (((759574826186141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597273344) :
    (((759601028558909 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597535488 := by
  exact
    theta_restart_gain 7597273344 7597535488 15 11517 33 (759574826186141 / 100000)
      (759601028558909 / 100000) (71097 / 3125) (2275107 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7597797632
    (h : (((759601028558909 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7597535488) :
    (((23738355802297 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7597797632 := by
  exact
    theta_restart_gain 7597535488 7597797632 15 11585 33 (759601028558909 / 100000)
      (23738355802297 / 3125) (2275107 / 100000) (227511 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7598059776
    (h : (((23738355802297 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7597797632) :
    (((37982674742367 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598059776 := by
  exact
    theta_restart_gain 7597797632 7598059776 15 11476 33 (23738355802297 / 3125)
      (37982674742367 / 5000) (2275111 / 100000) (1137557 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7598321920
    (h : (((37982674742367 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598059776) :
    (((189919946516181 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598321920 := by
  exact
    theta_restart_gain 7598059776 7598321920 15 11556 33 (37982674742367 / 5000)
      (189919946516181 / 25000) (1137557 / 50000) (2275117 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7598584064
    (h : (((189919946516181 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598321920) :
    (((379853030701253 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598584064 := by
  exact
    theta_restart_gain 7598321920 7598584064 15 11549 33 (189919946516181 / 25000)
      (379853030701253 / 50000) (1137559 / 50000) (2275121 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7598846208
    (h : (((379853030701253 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598584064) :
    (((759732546086067 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598846208 := by
  exact
    theta_restart_gain 7598584064 7598846208 15 11641 33 (379853030701253 / 50000)
      (759732546086067 / 100000) (2275121 / 100000) (568781 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7599108352
    (h : (((759732546086067 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7598846208) :
    (((759758932985817 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599108352 := by
  exact
    theta_restart_gain 7598846208 7599108352 15 11598 33 (759732546086067 / 100000)
      (759758932985817 / 100000) (18201 / 800) (284391 / 12500) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7599370496
    (h : (((759758932985817 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599108352) :
    (((759785058280641 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599370496 := by
  exact
    theta_restart_gain 7599108352 7599370496 15 11483 33 (759758932985817 / 100000)
      (759785058280641 / 100000) (284391 / 12500) (2275131 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7599632640
    (h : (((759785058280641 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599370496) :
    (((759811452086973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599632640 := by
  exact
    theta_restart_gain 7599370496 7599632640 15 11601 33 (759785058280641 / 100000)
      (759811452086973 / 100000) (568783 / 25000) (455027 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7599894784
    (h : (((759811452086973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599632640) :
    (((189959365926357 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599894784 := by
  exact
    theta_restart_gain 7599632640 7599894784 15 11433 33 (759811452086973 / 100000)
      (189959365926357 / 25000) (455027 / 20000) (1137569 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7600156928
    (h : (((189959365926357 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7599894784) :
    (((37993180025113 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600156928 := by
  exact
    theta_restart_gain 7599894784 7600156928 15 11488 33 (189959365926357 / 25000)
      (37993180025113 / 5000) (2275139 / 100000) (1137571 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7600419072
    (h : (((37993180025113 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600156928) :
    (((379944769698101 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600419072 := by
  exact
    theta_restart_gain 7600156928 7600419072 15 11401 33 (37993180025113 / 5000)
      (379944769698101 / 50000) (1137571 / 50000) (455029 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7600681216
    (h : (((379944769698101 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600419072) :
    (((189978929303643 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600681216 := by
  exact
    theta_restart_gain 7600419072 7600681216 15 11506 33 (379944769698101 / 50000)
      (189978929303643 / 25000) (455029 / 20000) (568787 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7600943360
    (h : (((189978929303643 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600681216) :
    (((759941733543387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600943360 := by
  exact
    theta_restart_gain 7600681216 7600943360 15 11435 33 (189978929303643 / 25000)
      (759941733543387 / 100000) (2275149 / 100000) (142197 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7601205504
    (h : (((759941733543387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7600943360) :
    (((759967777208331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7601205504 := by
  exact
    theta_restart_gain 7600943360 7601205504 15 11447 33 (759941733543387 / 100000)
      (759967777208331 / 100000) (142197 / 6250) (455031 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7601467648
    (h : (((759967777208331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7601205504) :
    (((151998892502611 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7601467648 := by
  exact
    theta_restart_gain 7601205504 7601467648 15 11729 33 (759967777208331 / 100000)
      (151998892502611 / 20000) (568789 / 25000) (2275159 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7601729792
    (h : (((151998892502611 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7601467648) :
    (((3800102622297 / 500) : ℚ) : ℝ) ≤ Chebyshev.theta 7601729792 := by
  exact
    theta_restart_gain 7601467648 7601729792 15 11455 33 (151998892502611 / 20000)
      (3800102622297 / 500) (2275159 / 100000) (1137581 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7601991936
    (h : (((3800102622297 / 500) : ℚ) : ℝ) ≤ Chebyshev.theta 7601729792) :
    (((95005832691493 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7601991936 := by
  exact
    theta_restart_gain 7601729792 7601991936 15 11488 33 (3800102622297 / 500)
      (95005832691493 / 12500) (2275163 / 100000) (1137583 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7602254080
    (h : (((95005832691493 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7601991936) :
    (((76007250969287 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602254080 := by
  exact
    theta_restart_gain 7601991936 7602254080 15 11361 33 (95005832691493 / 12500)
      (76007250969287 / 10000) (1137583 / 50000) (2275169 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7602516224
    (h : (((76007250969287 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602254080) :
    (((76009857404039 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602516224 := by
  exact
    theta_restart_gain 7602254080 7602516224 15 11456 33 (76007250969287 / 10000)
      (76009857404039 / 10000) (227517 / 10000) (2275173 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7602778368
    (h : (((76009857404039 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602516224) :
    (((760124581542953 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602778368 := by
  exact
    theta_restart_gain 7602516224 7602778368 15 11431 33 (76009857404039 / 10000)
      (760124581542953 / 100000) (2275173 / 100000) (284397 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7603040512
    (h : (((760124581542953 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7602778368) :
    (((760151041839833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603040512 := by
  exact
    theta_restart_gain 7602778368 7603040512 15 11630 33 (760124581542953 / 100000)
      (760151041839833 / 100000) (284397 / 12500) (2275179 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7603302656
    (h : (((760151041839833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603040512) :
    (((760177254188613 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603302656 := by
  exact
    theta_restart_gain 7603040512 7603302656 15 11521 33 (760151041839833 / 100000)
      (760177254188613 / 100000) (113759 / 5000) (2275183 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7603564800
    (h : (((760177254188613 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603302656) :
    (((76020337101427 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603564800 := by
  exact
    theta_restart_gain 7603302656 7603564800 15 11479 33 (760177254188613 / 100000)
      (76020337101427 / 10000) (2275183 / 100000) (1137593 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7603826944
    (h : (((76020337101427 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603564800) :
    (((760229378676867 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603826944 := by
  exact
    theta_restart_gain 7603564800 7603826944 15 11431 33 (76020337101427 / 10000)
      (760229378676867 / 100000) (2275187 / 100000) (227519 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7604089088
    (h : (((760229378676867 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7603826944) :
    (((760256002950247 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604089088 := by
  exact
    theta_restart_gain 7603826944 7604089088 15 11702 33 (760229378676867 / 100000)
      (760256002950247 / 100000) (227519 / 10000) (2275193 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7604351232
    (h : (((760256002950247 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604089088) :
    (((760282420227781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604351232 := by
  exact
    theta_restart_gain 7604089088 7604351232 15 11611 33 (760256002950247 / 100000)
      (760282420227781 / 100000) (1137597 / 50000) (2275197 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7604613376
    (h : (((760282420227781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604351232) :
    (((380154293634239 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604613376 := by
  exact
    theta_restart_gain 7604351232 7604613376 15 11501 33 (760282420227781 / 100000)
      (380154293634239 / 50000) (2275197 / 100000) (2844 / 125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7604875520
    (h : (((380154293634239 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604613376) :
    (((760334545036687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604875520 := by
  exact
    theta_restart_gain 7604613376 7604875520 15 11409 33 (380154293634239 / 50000)
      (760334545036687 / 100000) (2275201 / 100000) (568801 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7605137664
    (h : (((760334545036687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7604875520) :
    (((760360596122487 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605137664 := by
  exact
    theta_restart_gain 7604875520 7605137664 15 11450 33 (760334545036687 / 100000)
      (760360596122487 / 100000) (568801 / 25000) (2275207 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7605399808
    (h : (((760360596122487 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605137664) :
    (((95048380106681 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7605399808 := by
  exact
    theta_restart_gain 7605137664 7605399808 15 11623 33 (760360596122487 / 100000)
      (95048380106681 / 12500) (2275207 / 100000) (227521 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7605661952
    (h : (((95048380106681 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7605399808) :
    (((760413044239967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605661952 := by
  exact
    theta_restart_gain 7605399808 7605661952 15 11429 33 (95048380106681 / 12500)
      (760413044239967 / 100000) (2275211 / 100000) (1137607 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7605924096
    (h : (((760413044239967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605661952) :
    (((760439266081317 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605924096 := by
  exact
    theta_restart_gain 7605661952 7605924096 15 11525 33 (760413044239967 / 100000)
      (760439266081317 / 100000) (1137607 / 50000) (2275217 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7606186240
    (h : (((760439266081317 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7605924096) :
    (((760465412886573 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606186240 := by
  exact
    theta_restart_gain 7605924096 7606186240 15 11492 33 (760439266081317 / 100000)
      (760465412886573 / 100000) (1137609 / 50000) (2275221 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7606448384
    (h : (((760465412886573 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606186240) :
    (((380245835606067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606448384 := by
  exact
    theta_restart_gain 7606186240 7606448384 15 11541 33 (760465412886573 / 100000)
      (380245835606067 / 50000) (2275221 / 100000) (284403 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7606710528
    (h : (((380245835606067 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606448384) :
    (((760517834024409 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606710528 := by
  exact
    theta_restart_gain 7606448384 7606710528 15 11499 33 (380245835606067 / 50000)
      (760517834024409 / 100000) (91009 / 4000) (568807 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7606972672
    (h : (((760517834024409 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606710528) :
    (((760544187990333 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606972672 := by
  exact
    theta_restart_gain 7606710528 7606972672 15 11583 33 (760517834024409 / 100000)
      (760544187990333 / 100000) (568807 / 25000) (2275231 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7607234816
    (h : (((760544187990333 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7606972672) :
    (((760570485121789 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607234816 := by
  exact
    theta_restart_gain 7606972672 7607234816 15 11558 33 (760544187990333 / 100000)
      (760570485121789 / 100000) (71101 / 3125) (455047 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7607496960
    (h : (((760570485121789 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607234816) :
    (((760596691278519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607496960 := by
  exact
    theta_restart_gain 7607234816 7607496960 15 11518 33 (760570485121789 / 100000)
      (760596691278519 / 100000) (455047 / 20000) (1137619 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7607759104
    (h : (((760596691278519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607496960) :
    (((760622770067937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607759104 := by
  exact
    theta_restart_gain 7607496960 7607759104 15 11462 33 (760596691278519 / 100000)
      (760622770067937 / 100000) (2275239 / 100000) (1137621 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7608021248
    (h : (((760622770067937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7607759104) :
    (((760649005883439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608021248 := by
  exact
    theta_restart_gain 7607759104 7608021248 15 11531 33 (760622770067937 / 100000)
      (760649005883439 / 100000) (1137621 / 50000) (455049 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7608283392
    (h : (((760649005883439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608021248) :
    (((380337629967747 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608283392 := by
  exact
    theta_restart_gain 7608021248 7608283392 15 11539 33 (760649005883439 / 100000)
      (380337629967747 / 50000) (455049 / 20000) (142203 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7608545536
    (h : (((380337629967747 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608283392) :
    (((190175434820839 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608545536 := by
  exact
    theta_restart_gain 7608283392 7608545536 15 11638 33 (380337629967747 / 50000)
      (190175434820839 / 25000) (2275249 / 100000) (568813 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7608807680
    (h : (((190175434820839 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608545536) :
    (((190181980720843 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608807680 := by
  exact
    theta_restart_gain 7608545536 7608807680 15 11508 33 (190175434820839 / 25000)
      (190181980720843 / 25000) (568813 / 25000) (455051 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7609069824
    (h : (((190181980720843 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7608807680) :
    (((190188508999121 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609069824 := by
  exact
    theta_restart_gain 7608807680 7609069824 15 11477 33 (190181980720843 / 25000)
      (190188508999121 / 25000) (284407 / 12500) (2275259 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7609331968
    (h : (((190188508999121 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609069824) :
    (((95097525184373 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7609331968 := by
  exact
    theta_restart_gain 7609069824 7609331968 15 11500 33 (190188508999121 / 25000)
      (95097525184373 / 12500) (2275259 / 100000) (1137631 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7609594112
    (h : (((95097525184373 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7609331968) :
    (((190201582648819 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609594112 := by
  exact
    theta_restart_gain 7609331968 7609594112 15 11484 33 (95097525184373 / 12500)
      (190201582648819 / 25000) (2275263 / 100000) (1137633 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7609856256
    (h : (((190201582648819 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609594112) :
    (((380416256040569 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609856256 := by
  exact
    theta_restart_gain 7609594112 7609856256 15 11507 33 (190201582648819 / 25000)
      (380416256040569 / 50000) (1137633 / 50000) (2275269 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7610118400
    (h : (((380416256040569 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7609856256) :
    (((380429432129139 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610118400 := by
  exact
    theta_restart_gain 7609856256 7610118400 15 11582 33 (380416256040569 / 50000)
      (380429432129139 / 50000) (227527 / 10000) (2275273 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7610380544
    (h : (((380429432129139 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610118400) :
    (((380442560454349 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610380544 := by
  exact
    theta_restart_gain 7610118400 7610380544 15 11540 33 (380429432129139 / 50000)
      (380442560454349 / 50000) (2275273 / 100000) (568819 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7610642688
    (h : (((380442560454349 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610380544) :
    (((380455729751837 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610642688 := by
  exact
    theta_restart_gain 7610380544 7610642688 15 11576 33 (380442560454349 / 50000)
      (380455729751837 / 50000) (568819 / 25000) (2275279 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7610904832
    (h : (((380455729751837 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610642688) :
    (((380468790996677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610904832 := by
  exact
    theta_restart_gain 7610642688 7610904832 15 11481 33 (380455729751837 / 50000)
      (380468790996677 / 50000) (28441 / 1250) (2275283 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7611166976
    (h : (((380468790996677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7610904832) :
    (((38048173963223 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611166976 := by
  exact
    theta_restart_gain 7610904832 7611166976 15 11382 33 (380468790996677 / 50000)
      (38048173963223 / 5000) (2275283 / 100000) (1137643 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7611429120
    (h : (((38048173963223 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611166976) :
    (((760989624587377 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611429120 := by
  exact
    theta_restart_gain 7611166976 7611429120 15 11491 33 (38048173963223 / 5000)
      (760989624587377 / 100000) (2275287 / 100000) (227529 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7611691264
    (h : (((760989624587377 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611429120) :
    (((761015942866807 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611691264 := by
  exact
    theta_restart_gain 7611429120 7611691264 15 11567 33 (760989624587377 / 100000)
      (761015942866807 / 100000) (227529 / 10000) (2275293 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7611953408
    (h : (((761015942866807 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611691264) :
    (((761041910797229 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611953408 := by
  exact
    theta_restart_gain 7611691264 7611953408 15 11413 33 (761015942866807 / 100000)
      (761041910797229 / 100000) (1137647 / 50000) (2275297 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7612215552
    (h : (((761041910797229 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7611953408) :
    (((761068063060947 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612215552 := by
  exact
    theta_restart_gain 7611953408 7612215552 15 11494 33 (761041910797229 / 100000)
      (761068063060947 / 100000) (2275297 / 100000) (22753 / 1000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7612477696
    (h : (((761068063060947 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612215552) :
    (((761094342787497 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612477696 := by
  exact
    theta_restart_gain 7612215552 7612477696 15 11550 33 (761068063060947 / 100000)
      (761094342787497 / 100000) (2275301 / 100000) (284413 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7612739840
    (h : (((761094342787497 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612477696) :
    (((761120574767313 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612739840 := by
  exact
    theta_restart_gain 7612477696 7612739840 15 11529 33 (761094342787497 / 100000)
      (761120574767313 / 100000) (284413 / 12500) (2275307 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7613001984
    (h : (((761120574767313 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7612739840) :
    (((152229337238089 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613001984 := by
  exact
    theta_restart_gain 7612739840 7613001984 15 11476 33 (761120574767313 / 100000)
      (152229337238089 / 20000) (2275307 / 100000) (227531 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7613264128
    (h : (((152229337238089 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613001984) :
    (((95146604542471 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7613264128 := by
  exact
    theta_restart_gain 7613001984 7613264128 15 11493 33 (152229337238089 / 20000)
      (95146604542471 / 12500) (2275311 / 100000) (1137657 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7613526272
    (h : (((95146604542471 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7613264128) :
    (((76119907753613 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613526272 := by
  exact
    theta_restart_gain 7613264128 7613526272 15 11533 33 (95146604542471 / 12500)
      (76119907753613 / 10000) (1137657 / 50000) (2275317 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7613788416
    (h : (((76119907753613 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613526272) :
    (((76122528919949 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613788416 := by
  exact
    theta_restart_gain 7613526272 7613788416 15 11520 33 (76119907753613 / 10000)
      (76122528919949 / 10000) (1137659 / 50000) (2275321 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7614050560
    (h : (((76122528919949 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7613788416) :
    (((190312867260729 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614050560 := by
  exact
    theta_restart_gain 7613788416 7614050560 15 11506 33 (76122528919949 / 10000)
      (190312867260729 / 25000) (2275321 / 100000) (568831 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7614312704
    (h : (((190312867260729 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614050560) :
    (((761277769524591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614312704 := by
  exact
    theta_restart_gain 7614050560 7614312704 15 11559 33 (190312867260729 / 25000)
      (761277769524591 / 100000) (91013 / 4000) (71104 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7614574848
    (h : (((761277769524591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614312704) :
    (((761304183807343 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614574848 := by
  exact
    theta_restart_gain 7614312704 7614574848 15 11609 33 (761277769524591 / 100000)
      (761304183807343 / 100000) (71104 / 3125) (2275331 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7614836992
    (h : (((761304183807343 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614574848) :
    (((30453225108169 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614836992 := by
  exact
    theta_restart_gain 7614574848 7614836992 15 11622 33 (761304183807343 / 100000)
      (30453225108169 / 4000) (2275331 / 100000) (1137667 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7615099136
    (h : (((30453225108169 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7614836992) :
    (((30454271762269 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615099136 := by
  exact
    theta_restart_gain 7614836992 7615099136 15 11500 33 (30453225108169 / 4000)
      (30454271762269 / 4000) (455067 / 20000) (1137669 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7615361280
    (h : (((30454271762269 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615099136) :
    (((761382958168387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615361280 := by
  exact
    theta_restart_gain 7615099136 7615361280 15 11499 33 (30454271762269 / 4000)
      (761382958168387 / 100000) (1137669 / 50000) (2275341 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7615623424
    (h : (((761382958168387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615361280) :
    (((761408851560347 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615623424 := by
  exact
    theta_restart_gain 7615361280 7615623424 15 11380 33 (761382958168387 / 100000)
      (761408851560347 / 100000) (1137671 / 50000) (455069 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7615885568
    (h : (((761408851560347 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615623424) :
    (((190358766452523 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615885568 := by
  exact
    theta_restart_gain 7615623424 7615885568 15 11521 33 (761408851560347 / 100000)
      (190358766452523 / 25000) (455069 / 20000) (568837 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7616147712
    (h : (((190358766452523 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7615885568) :
    (((152292281505093 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616147712 := by
  exact
    theta_restart_gain 7615885568 7616147712 15 11577 33 (190358766452523 / 25000)
      (152292281505093 / 20000) (2275349 / 100000) (284419 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7616409856
    (h : (((152292281505093 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616147712) :
    (((761487655986137 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616409856 := by
  exact
    theta_restart_gain 7616147712 7616409856 15 11536 33 (152292281505093 / 20000)
      (761487655986137 / 100000) (284419 / 12500) (455071 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7616672000
    (h : (((761487655986137 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616409856) :
    (((761513540435993 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616672000 := by
  exact
    theta_restart_gain 7616409856 7616672000 15 11376 33 (761487655986137 / 100000)
      (761513540435993 / 100000) (568839 / 25000) (2275359 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7616934144
    (h : (((761513540435993 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616672000) :
    (((152307926850601 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616934144 := by
  exact
    theta_restart_gain 7616672000 7616934144 15 11468 33 (761513540435993 / 100000)
      (152307926850601 / 20000) (2275359 / 100000) (1137681 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7617196288
    (h : (((152307926850601 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7616934144) :
    (((761565887379761 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617196288 := by
  exact
    theta_restart_gain 7616934144 7617196288 15 11538 33 (152307926850601 / 20000)
      (761565887379761 / 100000) (1137681 / 50000) (455073 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7617458432
    (h : (((761565887379761 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617196288) :
    (((761592265697799 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617458432 := by
  exact
    theta_restart_gain 7617196288 7617458432 15 11593 33 (761565887379761 / 100000)
      (761592265697799 / 100000) (1137683 / 50000) (2275369 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7617720576
    (h : (((761592265697799 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617458432) :
    (((190404608679167 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617720576 := by
  exact
    theta_restart_gain 7617458432 7617720576 15 11501 33 (761592265697799 / 100000)
      (190404608679167 / 25000) (2275369 / 100000) (568843 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7617982720
    (h : (((190404608679167 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617720576) :
    (((761644649289001 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617982720 := by
  exact
    theta_restart_gain 7617720576 7617982720 15 11521 33 (190404608679167 / 25000)
      (761644649289001 / 100000) (2275373 / 100000) (142211 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7618244864
    (h : (((761644649289001 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7617982720) :
    (((761671055027481 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618244864 := by
  exact
    theta_restart_gain 7617982720 7618244864 15 11605 33 (761644649289001 / 100000)
      (761671055027481 / 100000) (142211 / 6250) (2275379 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7618507008
    (h : (((761671055027481 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618244864) :
    (((761697319738821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618507008 := by
  exact
    theta_restart_gain 7618244864 7618507008 15 11543 33 (761671055027481 / 100000)
      (761697319738821 / 100000) (113769 / 5000) (2275383 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7618769152
    (h : (((761697319738821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618507008) :
    (((761723723283153 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618769152 := by
  exact
    theta_restart_gain 7618507008 7618769152 15 11604 33 (761697319738821 / 100000)
      (761723723283153 / 100000) (2275383 / 100000) (1137693 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7619031296
    (h : (((761723723283153 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7618769152) :
    (((761749963046037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619031296 := by
  exact
    theta_restart_gain 7618769152 7619031296 15 11532 33 (761723723283153 / 100000)
      (761749963046037 / 100000) (2275387 / 100000) (227539 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7619293440
    (h : (((761749963046037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619031296) :
    (((761776123204867 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619293440 := by
  exact
    theta_restart_gain 7619031296 7619293440 15 11497 33 (761749963046037 / 100000)
      (761776123204867 / 100000) (227539 / 10000) (2275393 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7619555584
    (h : (((761776123204867 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619293440) :
    (((23806325053707 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7619555584 := by
  exact
    theta_restart_gain 7619293440 7619555584 15 11549 33 (761776123204867 / 100000)
      (23806325053707 / 3125) (2275393 / 100000) (568849 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7619817728
    (h : (((23806325053707 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7619555584) :
    (((380914364030957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619817728 := by
  exact
    theta_restart_gain 7619555584 7619817728 15 11570 33 (23806325053707 / 3125)
      (380914364030957 / 50000) (2275397 / 100000) (11377 / 500) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7620079872
    (h : (((380914364030957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7619817728) :
    (((380927604583557 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620079872 := by
  exact
    theta_restart_gain 7619817728 7620079872 15 11638 33 (380914364030957 / 50000)
      (380927604583557 / 50000) (11377 / 500) (2275403 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7620342016
    (h : (((380927604583557 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620079872) :
    (((380940733664637 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620342016 := by
  exact
    theta_restart_gain 7620079872 7620342016 15 11540 33 (380927604583557 / 50000)
      (380940733664637 / 50000) (568851 / 25000) (2275407 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7620604160
    (h : (((380940733664637 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620342016) :
    (((380953844559771 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620604160 := by
  exact
    theta_restart_gain 7620342016 7620604160 15 11524 33 (380940733664637 / 50000)
      (380953844559771 / 50000) (2275407 / 100000) (227541 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7620866304
    (h : (((380953844559771 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620604160) :
    (((152386758981989 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620866304 := by
  exact
    theta_restart_gain 7620604160 7620866304 15 11473 33 (380953844559771 / 50000)
      (152386758981989 / 20000) (2275411 / 100000) (1137707 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7621128448
    (h : (((152386758981989 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7620866304) :
    (((761960248873109 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621128448 := by
  exact
    theta_restart_gain 7620866304 7621128448 15 11626 33 (152386758981989 / 20000)
      (761960248873109 / 100000) (1137707 / 50000) (2275417 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7621390592
    (h : (((761960248873109 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621128448) :
    (((152397256841173 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621390592 := by
  exact
    theta_restart_gain 7621128448 7621390592 15 11442 33 (761960248873109 / 100000)
      (152397256841173 / 20000) (1137709 / 50000) (2275421 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7621652736
    (h : (((152397256841173 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621390592) :
    (((762012669987781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621652736 := by
  exact
    theta_restart_gain 7621390592 7621652736 15 11596 33 (152397256841173 / 20000)
      (762012669987781 / 100000) (2275421 / 100000) (71107 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7621914880
    (h : (((762012669987781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621652736) :
    (((762039003469733 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621914880 := by
  exact
    theta_restart_gain 7621652736 7621914880 15 11573 33 (762012669987781 / 100000)
      (762039003469733 / 100000) (71107 / 3125) (2275427 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7622177024
    (h : (((762039003469733 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7621914880) :
    (((762065095802609 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622177024 := by
  exact
    theta_restart_gain 7621914880 7622177024 15 11467 33 (762039003469733 / 100000)
      (762065095802609 / 100000) (568857 / 25000) (2275431 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7622439168
    (h : (((762065095802609 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622177024) :
    (((95261395676947 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7622439168 := by
  exact
    theta_restart_gain 7622177024 7622439168 15 11457 33 (762065095802609 / 100000)
      (95261395676947 / 12500) (2275431 / 100000) (1137717 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7622701312
    (h : (((95261395676947 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7622439168) :
    (((381058823464053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622701312 := by
  exact
    theta_restart_gain 7622439168 7622701312 15 11638 33 (95261395676947 / 12500)
      (381058823464053 / 50000) (455087 / 20000) (1137719 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7622963456
    (h : (((381058823464053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622701312) :
    (((381071920885181 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622963456 := by
  exact
    theta_restart_gain 7622701312 7622963456 15 11512 33 (381058823464053 / 50000)
      (381071920885181 / 50000) (1137719 / 50000) (2275441 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7623225600
    (h : (((381071920885181 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7622963456) :
    (((23817817272069 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7623225600 := by
  exact
    theta_restart_gain 7622963456 7623225600 15 11563 33 (381071920885181 / 50000)
      (23817817272069 / 3125) (1137721 / 50000) (455089 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7623487744
    (h : (((23817817272069 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7623225600) :
    (((762196263437583 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7623487744 := by
  exact
    theta_restart_gain 7623225600 7623487744 15 11475 33 (23817817272069 / 3125)
      (762196263437583 / 100000) (455089 / 20000) (284431 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7623749888
    (h : (((762196263437583 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7623487744) :
    (((762222738275063 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7623749888 := by
  exact
    theta_restart_gain 7623487744 7623749888 15 11635 33 (762196263437583 / 100000)
      (762222738275063 / 100000) (284431 / 12500) (2275451 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7624012032
    (h : (((762222738275063 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7623749888) :
    (((762248878667639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624012032 := by
  exact
    theta_restart_gain 7623749888 7624012032 15 11488 33 (762222738275063 / 100000)
      (762248878667639 / 100000) (568863 / 25000) (455091 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7624274176
    (h : (((762248878667639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624012032) :
    (((381137647212367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624274176 := by
  exact
    theta_restart_gain 7624012032 7624274176 15 11609 33 (762248878667639 / 100000)
      (381137647212367 / 50000) (455091 / 20000) (1137729 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7624536320
    (h : (((381137647212367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624274176) :
    (((762301637413577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624536320 := by
  exact
    theta_restart_gain 7624274176 7624536320 15 11577 33 (381137647212367 / 50000)
      (762301637413577 / 100000) (2275459 / 100000) (1137731 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7624798464
    (h : (((762301637413577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624536320) :
    (((762327898520519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624798464 := by
  exact
    theta_restart_gain 7624536320 7624798464 15 11541 33 (762301637413577 / 100000)
      (762327898520519 / 100000) (1137731 / 50000) (455093 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7625060608
    (h : (((762327898520519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7624798464) :
    (((762354116439771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625060608 := by
  exact
    theta_restart_gain 7624798464 7625060608 15 11522 33 (762327898520519 / 100000)
      (762354116439771 / 100000) (1137733 / 50000) (2275469 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7625322752
    (h : (((762354116439771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625060608) :
    (((15247605277081 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625322752 := by
  exact
    theta_restart_gain 7625060608 7625322752 15 11491 33 (762354116439771 / 100000)
      (15247605277081 / 2000) (2275469 / 100000) (142217 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7625584896
    (h : (((15247605277081 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625322752) :
    (((762406607004971 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625584896 := by
  exact
    theta_restart_gain 7625322752 7625584896 15 11577 33 (15247605277081 / 2000)
      (762406607004971 / 100000) (2275473 / 100000) (568869 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7625847040
    (h : (((762406607004971 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625584896) :
    (((762432779529923 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625847040 := by
  exact
    theta_restart_gain 7625584896 7625847040 15 11502 33 (762406607004971 / 100000)
      (762432779529923 / 100000) (568869 / 25000) (2275479 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626109184
    (h : (((762432779529923 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7625847040) :
    (((762458688133817 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626109184 := by
  exact
    theta_restart_gain 7625847040 7626109184 15 11386 33 (762432779529923 / 100000)
      (762458688133817 / 100000) (2275479 / 100000) (1137741 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626371328
    (h : (((762458688133817 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626109184) :
    (((762485156552073 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626371328 := by
  exact
    theta_restart_gain 7626109184 7626371328 15 11632 33 (762458688133817 / 100000)
      (762485156552073 / 100000) (2275483 / 100000) (1137743 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626387712
    (h : (((762485156552073 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626371328) :
    (((762486760769703 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626387712 := by
  exact
    theta_restart_gain 7626371328 7626387712 11 705 33 (762485156552073 / 100000)
      (762486760769703 / 100000) (1137743 / 50000) (2275489 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7626389760
    (h : (((762486760769703 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626387712) :
    (((381243490745971 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626389760 := by
  exact
    theta_restart_gain 7626387712 7626389760 8 97 33 (762486760769703 / 100000)
      (381243490745971 / 50000) (2275487 / 100000) (227549 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7626389760
    (h : (((47455422479953 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7594389760) :
    (((381243490745971 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7626389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7626389760 point7626387712)
                  (Function.comp point7626371328 point7626109184))
                (Function.comp (Function.comp point7625847040 point7625584896)
                  (Function.comp point7625322752 point7625060608)))
              (Function.comp
                (Function.comp (Function.comp point7624798464 point7624536320)
                  (Function.comp point7624274176 point7624012032))
                (Function.comp (Function.comp point7623749888 point7623487744)
                  (Function.comp point7623225600 point7622963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7622701312 point7622439168)
                  (Function.comp point7622177024 point7621914880))
                (Function.comp (Function.comp point7621652736 point7621390592)
                  (Function.comp point7621128448 point7620866304)))
              (Function.comp
                (Function.comp (Function.comp point7620604160 point7620342016)
                  (Function.comp point7620079872 point7619817728))
                (Function.comp (Function.comp point7619555584 point7619293440)
                  (Function.comp point7619031296 point7618769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7618507008 point7618244864)
                  (Function.comp point7617982720 point7617720576))
                (Function.comp (Function.comp point7617458432 point7617196288)
                  (Function.comp point7616934144 point7616672000)))
              (Function.comp
                (Function.comp (Function.comp point7616409856 point7616147712)
                  (Function.comp point7615885568 point7615623424))
                (Function.comp (Function.comp point7615361280 point7615099136)
                  (Function.comp point7614836992 point7614574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7614312704 point7614050560)
                  (Function.comp point7613788416 point7613526272))
                (Function.comp (Function.comp point7613264128 point7613001984)
                  (Function.comp point7612739840 point7612477696)))
              (Function.comp
                (Function.comp (Function.comp point7612215552 point7611953408)
                  (Function.comp point7611691264 point7611429120))
                (Function.comp (Function.comp point7611166976 point7610904832)
                  (Function.comp point7610642688 point7610380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7610118400 point7609856256)
                  (Function.comp point7609594112 point7609331968))
                (Function.comp (Function.comp point7609069824 point7608807680)
                  (Function.comp point7608545536 point7608283392)))
              (Function.comp
                (Function.comp (Function.comp point7608021248 point7607759104)
                  (Function.comp point7607496960 point7607234816))
                (Function.comp (Function.comp point7606972672 point7606710528)
                  (Function.comp point7606448384 point7606186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7605924096 point7605661952)
                  (Function.comp point7605399808 point7605137664))
                (Function.comp (Function.comp point7604875520 point7604613376)
                  (Function.comp point7604351232 point7604089088)))
              (Function.comp
                (Function.comp (Function.comp point7603826944 point7603564800)
                  (Function.comp point7603302656 point7603040512))
                (Function.comp (Function.comp point7602778368 point7602516224)
                  (Function.comp point7602254080 point7601991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7601729792 point7601467648)
                  (Function.comp point7601205504 point7600943360))
                (Function.comp (Function.comp point7600681216 point7600419072)
                  (Function.comp point7600156928 point7599894784)))
              (Function.comp
                (Function.comp (Function.comp point7599632640 point7599370496)
                  (Function.comp point7599108352 point7598846208))
                (Function.comp (Function.comp point7598584064 point7598321920)
                  (Function.comp point7598059776 point7597797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7597535488 point7597273344)
                  (Function.comp point7597011200 point7596749056))
                (Function.comp (Function.comp point7596486912 point7596224768)
                  (Function.comp point7595962624 point7595700480)))
              (Function.comp (Function.comp point7595438336 point7595176192)
                (Function.comp point7594914048 point7594651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
