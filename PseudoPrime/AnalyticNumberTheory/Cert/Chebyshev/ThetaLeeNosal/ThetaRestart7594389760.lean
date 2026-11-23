/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7594389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562651904
    (h : (((756089196367119 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562389760) :
    (((756115600434671 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562651904 := by
  exact
    theta_restart_gain 7562389760 7562651904 15 11608 33 (756089196367119 / 100000)
      (756115600434671 / 100000) (568661 / 25000) (2274647 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562914048
    (h : (((756115600434671 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562651904) :
    (((756141499565413 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562914048 := by
  exact
    theta_restart_gain 7562651904 7562914048 15 11386 33 (756115600434671 / 100000)
      (756141499565413 / 100000) (2274647 / 100000) (45493 / 2000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7563176192
    (h : (((756141499565413 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562914048) :
    (((378083941621181 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7563176192 := by
  exact
    theta_restart_gain 7562914048 7563176192 15 11599 33 (756141499565413 / 100000)
      (378083941621181 / 50000) (2274651 / 100000) (1137327 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7563438336
    (h : (((378083941621181 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7563176192) :
    (((23631066150842 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7563438336 := by
  exact
    theta_restart_gain 7563176192 7563438336 15 11533 33 (378083941621181 / 50000)
      (23631066150842 / 3125) (1137327 / 50000) (2274657 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7563700480
    (h : (((23631066150842 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7563438336) :
    (((94527527600269 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7563700480 := by
  exact
    theta_restart_gain 7563438336 7563700480 15 11476 33 (23631066150842 / 3125)
      (94527527600269 / 12500) (1137329 / 50000) (2274661 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7563962624
    (h : (((94527527600269 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7563700480) :
    (((189061585752269 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7563962624 := by
  exact
    theta_restart_gain 7563700480 7563962624 15 11484 33 (94527527600269 / 12500)
      (189061585752269 / 25000) (2274661 / 100000) (284333 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7564224768
    (h : (((189061585752269 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7563962624) :
    (((756272453888611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564224768 := by
  exact
    theta_restart_gain 7563962624 7564224768 15 11479 33 (189061585752269 / 25000)
      (756272453888611 / 100000) (454933 / 20000) (568667 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7564486912
    (h : (((756272453888611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564224768) :
    (((756298774072039 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564486912 := by
  exact
    theta_restart_gain 7564224768 7564486912 15 11571 33 (756272453888611 / 100000)
      (756298774072039 / 100000) (568667 / 25000) (2274671 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7564749056
    (h : (((756298774072039 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564486912) :
    (((756325107949783 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564749056 := by
  exact
    theta_restart_gain 7564486912 7564749056 15 11577 33 (756298774072039 / 100000)
      (756325107949783 / 100000) (142167 / 6250) (90987 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7565011200
    (h : (((756325107949783 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7564749056) :
    (((189087822933427 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565011200 := by
  exact
    theta_restart_gain 7564749056 7565011200 15 11511 33 (756325107949783 / 100000)
      (189087822933427 / 25000) (90987 / 4000) (1137339 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7565273344
    (h : (((189087822933427 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565011200) :
    (((378188790093677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565273344 := by
  exact
    theta_restart_gain 7565011200 7565273344 15 11557 33 (189087822933427 / 25000)
      (378188790093677 / 50000) (1137339 / 50000) (2274681 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7565535488
    (h : (((378188790093677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565273344) :
    (((18910101607747 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7565535488 := by
  exact
    theta_restart_gain 7565273344 7565535488 15 11643 33 (378188790093677 / 50000)
      (18910101607747 / 2500) (1137341 / 50000) (454937 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7565797632
    (h : (((18910101607747 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7565535488) :
    (((75643056439013 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565797632 := by
  exact
    theta_restart_gain 7565535488 7565797632 15 11650 33 (18910101607747 / 2500)
      (75643056439013 / 10000) (454937 / 20000) (71084 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7566059776
    (h : (((75643056439013 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7565797632) :
    (((94557088708187 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7566059776 := by
  exact
    theta_restart_gain 7565797632 7566059776 15 11494 33 (75643056439013 / 10000)
      (94557088708187 / 12500) (2274689 / 100000) (568673 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7566321920
    (h : (((94557088708187 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7566059776) :
    (((189120767767771 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7566321920 := by
  exact
    theta_restart_gain 7566059776 7566321920 15 11589 33 (94557088708187 / 12500)
      (189120767767771 / 25000) (568673 / 25000) (454939 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7566584064
    (h : (((189120767767771 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7566321920) :
    (((189127322872969 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7566584064 := by
  exact
    theta_restart_gain 7566321920 7566584064 15 11527 33 (189120767767771 / 25000)
      (189127322872969 / 25000) (284337 / 12500) (2274699 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7566846208
    (h : (((189127322872969 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7566584064) :
    (((9456694723919 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7566846208 := by
  exact
    theta_restart_gain 7566584064 7566846208 15 11556 33 (189127322872969 / 25000)
      (9456694723919 / 1250) (2274699 / 100000) (1137351 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7567108352
    (h : (((9456694723919 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7566846208) :
    (((94570220536807 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7567108352 := by
  exact
    theta_restart_gain 7566846208 7567108352 15 11512 33 (9456694723919 / 1250)
      (94570220536807 / 12500) (2274703 / 100000) (1137353 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7567370496
    (h : (((94570220536807 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7567108352) :
    (((189146981990717 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7567370496 := by
  exact
    theta_restart_gain 7567108352 7567370496 15 11502 33 (94570220536807 / 12500)
      (189146981990717 / 25000) (1137353 / 50000) (2274709 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7567632640
    (h : (((189146981990717 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7567370496) :
    (((23644195198674 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7567632640 := by
  exact
    theta_restart_gain 7567370496 7567632640 15 11570 33 (189146981990717 / 25000)
      (23644195198674 / 3125) (227471 / 10000) (2274713 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7567894784
    (h : (((23644195198674 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7567632640) :
    (((756640444227189 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7567894784 := by
  exact
    theta_restart_gain 7567632640 7567894784 15 11517 33 (23644195198674 / 3125)
      (756640444227189 / 100000) (2274713 / 100000) (568679 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7568156928
    (h : (((756640444227189 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7567894784) :
    (((756666594373821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568156928 := by
  exact
    theta_restart_gain 7567894784 7568156928 15 11496 33 (756640444227189 / 100000)
      (756666594373821 / 100000) (2274717 / 100000) (14217 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7568419072
    (h : (((756666594373821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568156928) :
    (((756692649016701 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568419072 := by
  exact
    theta_restart_gain 7568156928 7568419072 15 11454 33 (756666594373821 / 100000)
      (756692649016701 / 100000) (14217 / 625) (2274723 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7568681216
    (h : (((756692649016701 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568419072) :
    (((756718985771173 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568681216 := by
  exact
    theta_restart_gain 7568419072 7568681216 15 11578 33 (756692649016701 / 100000)
      (756718985771173 / 100000) (568681 / 25000) (2274727 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7568943360
    (h : (((756718985771173 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568681216) :
    (((756745217922937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568943360 := by
  exact
    theta_restart_gain 7568681216 7568943360 15 11532 33 (756718985771173 / 100000)
      (756745217922937 / 100000) (2274727 / 100000) (227473 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7569205504
    (h : (((756745217922937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7568943360) :
    (((756771591142557 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569205504 := by
  exact
    theta_restart_gain 7568943360 7569205504 15 11594 33 (756745217922937 / 100000)
      (756771591142557 / 100000) (227473 / 10000) (2274733 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7569467648
    (h : (((756771591142557 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569205504) :
    (((756797532209093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569467648 := by
  exact
    theta_restart_gain 7569205504 7569467648 15 11404 33 (756771591142557 / 100000)
      (756797532209093 / 100000) (1137367 / 50000) (2274737 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7569729792
    (h : (((756797532209093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569467648) :
    (((189205970121941 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569729792 := by
  exact
    theta_restart_gain 7569467648 7569729792 15 11583 33 (756797532209093 / 100000)
      (189205970121941 / 25000) (2274737 / 100000) (113737 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7569991936
    (h : (((189205970121941 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569729792) :
    (((378424967685589 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569991936 := by
  exact
    theta_restart_gain 7569729792 7569991936 15 11454 33 (189205970121941 / 25000)
      (378424967685589 / 50000) (2274741 / 100000) (284343 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7570254080
    (h : (((378424967685589 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7569991936) :
    (((378437943962737 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570254080 := by
  exact
    theta_restart_gain 7569991936 7570254080 15 11409 33 (378424967685589 / 50000)
      (378437943962737 / 50000) (284343 / 12500) (2274747 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7570516224
    (h : (((378437943962737 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570254080) :
    (((378451072670819 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570516224 := by
  exact
    theta_restart_gain 7570254080 7570516224 15 11543 33 (378437943962737 / 50000)
      (378451072670819 / 50000) (568687 / 25000) (2274751 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7570778368
    (h : (((378451072670819 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570516224) :
    (((756928339099403 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570778368 := by
  exact
    theta_restart_gain 7570516224 7570778368 15 11515 33 (378451072670819 / 50000)
      (756928339099403 / 100000) (2274751 / 100000) (1137377 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7571040512
    (h : (((756928339099403 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7570778368) :
    (((378477482553339 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571040512 := by
  exact
    theta_restart_gain 7570778368 7571040512 15 11705 33 (756928339099403 / 100000)
      (378477482553339 / 50000) (454951 / 20000) (1137379 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7571302656
    (h : (((378477482553339 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571040512) :
    (((378490619280789 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571302656 := by
  exact
    theta_restart_gain 7571040512 7571302656 15 11550 33 (378477482553339 / 50000)
      (378490619280789 / 50000) (1137379 / 50000) (2274761 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7571564800
    (h : (((378490619280789 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571302656) :
    (((189251831951739 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571564800 := by
  exact
    theta_restart_gain 7571302656 7571564800 15 11469 33 (378490619280789 / 50000)
      (189251831951739 / 25000) (1137381 / 50000) (454953 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7571826944
    (h : (((189251831951739 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571564800) :
    (((757033781049141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571826944 := by
  exact
    theta_restart_gain 7571564800 7571826944 15 11629 33 (189251831951739 / 25000)
      (757033781049141 / 100000) (454953 / 20000) (142173 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7572089088
    (h : (((757033781049141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7571826944) :
    (((757059763460659 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572089088 := by
  exact
    theta_restart_gain 7571826944 7572089088 15 11422 33 (757033781049141 / 100000)
      (757059763460659 / 100000) (2274769 / 100000) (568693 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7572351232
    (h : (((757059763460659 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572089088) :
    (((757086041626803 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572351232 := by
  exact
    theta_restart_gain 7572089088 7572351232 15 11552 33 (757059763460659 / 100000)
      (757086041626803 / 100000) (568693 / 25000) (90991 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7572613376
    (h : (((757086041626803 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572351232) :
    (((378556074609739 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572613376 := by
  exact
    theta_restart_gain 7572351232 7572613376 15 11477 33 (757086041626803 / 100000)
      (378556074609739 / 50000) (90991 / 4000) (1137389 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7572875520
    (h : (((378556074609739 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572613376) :
    (((757138479786403 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572875520 := by
  exact
    theta_restart_gain 7572613376 7572875520 15 11575 33 (378556074609739 / 50000)
      (757138479786403 / 100000) (2274779 / 100000) (1137391 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7573137664
    (h : (((757138479786403 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7572875520) :
    (((30286582952429 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573137664 := by
  exact
    theta_restart_gain 7572875520 7573137664 15 11471 33 (757138479786403 / 100000)
      (30286582952429 / 4000) (1137391 / 50000) (454957 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7573399808
    (h : (((30286582952429 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573137664) :
    (((151438119472513 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573399808 := by
  exact
    theta_restart_gain 7573137664 7573399808 15 11440 33 (30286582952429 / 4000)
      (151438119472513 / 20000) (1137393 / 50000) (2274789 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7573661952
    (h : (((151438119472513 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573399808) :
    (((37860844127473 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573661952 := by
  exact
    theta_restart_gain 7573399808 7573661952 15 11555 33 (151438119472513 / 20000)
      (37860844127473 / 5000) (2274789 / 100000) (284349 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7573924096
    (h : (((37860844127473 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573661952) :
    (((757242858410727 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573924096 := by
  exact
    theta_restart_gain 7573661952 7573924096 15 11419 33 (37860844127473 / 5000)
      (757242858410727 / 100000) (2274793 / 100000) (568699 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7574186240
    (h : (((757242858410727 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7573924096) :
    (((757269052686667 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574186240 := by
  exact
    theta_restart_gain 7573924096 7574186240 15 11515 33 (757242858410727 / 100000)
      (757269052686667 / 100000) (568699 / 25000) (2274799 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7574448384
    (h : (((757269052686667 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574186240) :
    (((757295317527467 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574448384 := by
  exact
    theta_restart_gain 7574186240 7574448384 15 11546 33 (757269052686667 / 100000)
      (757295317527467 / 100000) (5687 / 250) (2274803 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7574710528
    (h : (((757295317527467 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574448384) :
    (((757321568754087 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574710528 := by
  exact
    theta_restart_gain 7574448384 7574710528 15 11540 33 (757295317527467 / 100000)
      (757321568754087 / 100000) (2274803 / 100000) (1137403 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7574972672
    (h : (((757321568754087 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574710528) :
    (((757348083904479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574972672 := by
  exact
    theta_restart_gain 7574710528 7574972672 15 11656 33 (757321568754087 / 100000)
      (757348083904479 / 100000) (2274807 / 100000) (227481 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7575234816
    (h : (((757348083904479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7574972672) :
    (((757374417105039 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575234816 := by
  exact
    theta_restart_gain 7574972672 7575234816 15 11576 33 (757348083904479 / 100000)
      (757374417105039 / 100000) (227481 / 10000) (2274813 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7575496960
    (h : (((757374417105039 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575234816) :
    (((757400466000153 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575496960 := by
  exact
    theta_restart_gain 7575234816 7575496960 15 11451 33 (757374417105039 / 100000)
      (757400466000153 / 100000) (1137407 / 50000) (2274817 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7575759104
    (h : (((757400466000153 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575496960) :
    (((757426544502241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575759104 := by
  exact
    theta_restart_gain 7575496960 7575759104 15 11464 33 (757400466000153 / 100000)
      (757426544502241 / 100000) (2274817 / 100000) (113741 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7576021248
    (h : (((757426544502241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7575759104) :
    (((757452327312121 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576021248 := by
  exact
    theta_restart_gain 7575759104 7576021248 15 11334 33 (757426544502241 / 100000)
      (757452327312121 / 100000) (113741 / 5000) (2274823 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7576283392
    (h : (((757452327312121 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576021248) :
    (((757478556032841 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576283392 := by
  exact
    theta_restart_gain 7576021248 7576283392 15 11530 33 (757452327312121 / 100000)
      (757478556032841 / 100000) (284353 / 12500) (2274827 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7576545536
    (h : (((757478556032841 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576283392) :
    (((757504616450953 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576545536 := by
  exact
    theta_restart_gain 7576283392 7576545536 15 11456 33 (757478556032841 / 100000)
      (757504616450953 / 100000) (2274827 / 100000) (227483 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7576807680
    (h : (((757504616450953 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576545536) :
    (((151506147212099 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576807680 := by
  exact
    theta_restart_gain 7576545536 7576807680 15 11482 33 (757504616450953 / 100000)
      (151506147212099 / 20000) (2274831 / 100000) (1137417 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7577069824
    (h : (((151506147212099 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7576807680) :
    (((757556701015771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577069824 := by
  exact
    theta_restart_gain 7576807680 7577069824 15 11414 33 (151506147212099 / 20000)
      (757556701015771 / 100000) (1137417 / 50000) (2274837 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7577331968
    (h : (((757556701015771 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577069824) :
    (((757583211977823 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577331968 := by
  exact
    theta_restart_gain 7577069824 7577331968 15 11654 33 (757556701015771 / 100000)
      (757583211977823 / 100000) (1137419 / 50000) (2274841 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7577594112
    (h : (((757583211977823 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577331968) :
    (((757609245258227 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577594112 := by
  exact
    theta_restart_gain 7577331968 7577594112 15 11444 33 (757583211977823 / 100000)
      (757609245258227 / 100000) (2274841 / 100000) (568711 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7577856256
    (h : (((757609245258227 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577594112) :
    (((757635401426037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577856256 := by
  exact
    theta_restart_gain 7577594112 7577856256 15 11498 33 (757609245258227 / 100000)
      (757635401426037 / 100000) (454969 / 20000) (71089 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7578118400
    (h : (((757635401426037 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7577856256) :
    (((757661398388981 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578118400 := by
  exact
    theta_restart_gain 7577856256 7578118400 15 11428 33 (757635401426037 / 100000)
      (757661398388981 / 100000) (71089 / 3125) (2274851 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7578380544
    (h : (((757661398388981 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578118400) :
    (((151537537770709 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578380544 := by
  exact
    theta_restart_gain 7578118400 7578380544 15 11557 33 (757661398388981 / 100000)
      (151537537770709 / 20000) (568713 / 25000) (454971 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7578642688
    (h : (((151537537770709 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578380544) :
    (((30308557263233 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578642688 := by
  exact
    theta_restart_gain 7578380544 7578642688 15 11536 33 (151537537770709 / 20000)
      (30308557263233 / 4000) (454971 / 20000) (1137429 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7578904832
    (h : (((30308557263233 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578642688) :
    (((757739805815717 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578904832 := by
  exact
    theta_restart_gain 7578642688 7578904832 15 11374 33 (30308557263233 / 4000)
      (757739805815717 / 100000) (1137429 / 50000) (2274861 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7579166976
    (h : (((757739805815717 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7578904832) :
    (((757765855260479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579166976 := by
  exact
    theta_restart_gain 7578904832 7579166976 15 11451 33 (757739805815717 / 100000)
      (757765855260479 / 100000) (1137431 / 50000) (454973 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7579429120
    (h : (((757765855260479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579166976) :
    (((757792084453929 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579429120 := by
  exact
    theta_restart_gain 7579166976 7579429120 15 11530 33 (757765855260479 / 100000)
      (757792084453929 / 100000) (454973 / 20000) (568717 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7579691264
    (h : (((757792084453929 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579429120) :
    (((75781831141863 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579691264 := by
  exact
    theta_restart_gain 7579429120 7579691264 15 11529 33 (757792084453929 / 100000)
      (75781831141863 / 10000) (2274869 / 100000) (284359 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7579953408
    (h : (((75781831141863 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579691264) :
    (((378922290820243 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579953408 := by
  exact
    theta_restart_gain 7579691264 7579953408 15 11548 33 (75781831141863 / 10000)
      (378922290820243 / 50000) (284359 / 12500) (18199 / 800) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7580215552
    (h : (((378922290820243 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7579953408) :
    (((378935366807491 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580215552 := by
  exact
    theta_restart_gain 7579953408 7580215552 15 11496 33 (378922290820243 / 50000)
      (378935366807491 / 50000) (568719 / 25000) (2274879 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7580477696
    (h : (((378935366807491 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580215552) :
    (((75789692202203 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580477696 := by
  exact
    theta_restart_gain 7580215552 7580477696 15 11512 33 (378935366807491 / 50000)
      (75789692202203 / 10000) (2274879 / 100000) (1137441 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7580739840
    (h : (((75789692202203 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580477696) :
    (((757923144598371 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580739840 := by
  exact
    theta_restart_gain 7580477696 7580739840 15 11527 33 (75789692202203 / 10000)
      (757923144598371 / 100000) (2274883 / 100000) (1137443 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7581001984
    (h : (((757923144598371 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7580739840) :
    (((757949364934407 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581001984 := by
  exact
    theta_restart_gain 7580739840 7581001984 15 11526 33 (757923144598371 / 100000)
      (757949364934407 / 100000) (1137443 / 50000) (2274889 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7581264128
    (h : (((757949364934407 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581001984) :
    (((757975635364127 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581264128 := by
  exact
    theta_restart_gain 7581001984 7581264128 15 11548 33 (757949364934407 / 100000)
      (757975635364127 / 100000) (227489 / 10000) (2274893 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7581526272
    (h : (((757975635364127 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581264128) :
    (((151600371156169 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581526272 := by
  exact
    theta_restart_gain 7581264128 7581526272 15 11526 33 (757975635364127 / 100000)
      (151600371156169 / 20000) (2274893 / 100000) (142181 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7581788416
    (h : (((151600371156169 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7581526272) :
    (((94753515502063 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7581788416 := by
  exact
    theta_restart_gain 7581526272 7581788416 15 11547 33 (151600371156169 / 20000)
      (94753515502063 / 12500) (2274897 / 100000) (22749 / 1000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7582050560
    (h : (((94753515502063 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7581788416) :
    (((23689195706797 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7582050560 := by
  exact
    theta_restart_gain 7581788416 7582050560 15 11490 33 (94753515502063 / 12500)
      (23689195706797 / 3125) (22749 / 1000) (2274903 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7582312704
    (h : (((23689195706797 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7582050560) :
    (((758080453575743 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582312704 := by
  exact
    theta_restart_gain 7582050560 7582312704 15 11513 33 (23689195706797 / 3125)
      (758080453575743 / 100000) (2274903 / 100000) (1137453 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7582574848
    (h : (((758080453575743 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582312704) :
    (((7581062760451 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582574848 := by
  exact
    theta_restart_gain 7582312704 7582574848 15 11351 33 (758080453575743 / 100000)
      (7581062760451 / 1000) (2274907 / 100000) (227491 / 10000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7582836992
    (h : (((7581062760451 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582574848) :
    (((75813233968897 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582836992 := by
  exact
    theta_restart_gain 7582574848 7582836992 15 11457 33 (7581062760451 / 1000)
      (75813233968897 / 10000) (227491 / 10000) (2274913 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7583099136
    (h : (((75813233968897 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7582836992) :
    (((94769829427487 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7583099136 := by
  exact
    theta_restart_gain 7582836992 7583099136 15 11559 33 (75813233968897 / 10000)
      (94769829427487 / 12500) (1137457 / 50000) (2274917 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7583361280
    (h : (((94769829427487 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7583099136) :
    (((758184553549277 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583361280 := by
  exact
    theta_restart_gain 7583099136 7583361280 15 11393 33 (94769829427487 / 12500)
      (758184553549277 / 100000) (2274917 / 100000) (56873 / 2500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7583623424
    (h : (((758184553549277 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583361280) :
    (((189552666841859 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583623424 := by
  exact
    theta_restart_gain 7583361280 7583623424 15 11479 33 (758184553549277 / 100000)
      (189552666841859 / 25000) (2274921 / 100000) (568731 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7583885568
    (h : (((189552666841859 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583623424) :
    (((189559319857097 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583885568 := by
  exact
    theta_restart_gain 7583623424 7583885568 15 11698 33 (189552666841859 / 25000)
      (189559319857097 / 25000) (568731 / 25000) (2274927 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7584147712
    (h : (((189559319857097 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7583885568) :
    (((189565923404349 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584147712 := by
  exact
    theta_restart_gain 7583885568 7584147712 15 11611 33 (189559319857097 / 25000)
      (189565923404349 / 25000) (142183 / 6250) (2274931 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7584409856
    (h : (((189565923404349 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584147712) :
    (((379145039133567 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584409856 := by
  exact
    theta_restart_gain 7584147712 7584409856 15 11598 33 (189565923404349 / 25000)
      (379145039133567 / 50000) (2274931 / 100000) (1137467 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7584672000
    (h : (((379145039133567 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584409856) :
    (((379158165508517 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584672000 := by
  exact
    theta_restart_gain 7584409856 7584672000 15 11540 33 (379145039133567 / 50000)
      (379158165508517 / 50000) (454987 / 20000) (1137469 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7584934144
    (h : (((379158165508517 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584672000) :
    (((379171148579683 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584934144 := by
  exact
    theta_restart_gain 7584672000 7584934144 15 11414 33 (379158165508517 / 50000)
      (379171148579683 / 50000) (1137469 / 50000) (2274941 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7585196288
    (h : (((379171148579683 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7584934144) :
    (((189592093133277 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585196288 := by
  exact
    theta_restart_gain 7584934144 7585196288 15 11462 33 (379171148579683 / 50000)
      (189592093133277 / 25000) (2274941 / 100000) (71092 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7585458432
    (h : (((189592093133277 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585196288) :
    (((758394686821923 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585458432 := by
  exact
    theta_restart_gain 7585196288 7585458432 15 11567 33 (189592093133277 / 25000)
      (758394686821923 / 100000) (454989 / 20000) (568737 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7585720576
    (h : (((758394686821923 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585458432) :
    (((758420976121011 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585720576 := by
  exact
    theta_restart_gain 7585458432 7585720576 15 11556 33 (758394686821923 / 100000)
      (758420976121011 / 100000) (568737 / 25000) (2274951 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7585982720
    (h : (((758420976121011 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585720576) :
    (((758447081195211 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585982720 := by
  exact
    theta_restart_gain 7585720576 7585982720 15 11475 33 (758420976121011 / 100000)
      (758447081195211 / 100000) (284369 / 12500) (454991 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7586244864
    (h : (((758447081195211 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7585982720) :
    (((758473502522581 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586244864 := by
  exact
    theta_restart_gain 7585982720 7586244864 15 11614 33 (758447081195211 / 100000)
      (758473502522581 / 100000) (454991 / 20000) (1137479 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7586507008
    (h : (((758473502522581 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586244864) :
    (((758499669100999 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586507008 := by
  exact
    theta_restart_gain 7586244864 7586507008 15 11502 33 (758473502522581 / 100000)
      (758499669100999 / 100000) (2274959 / 100000) (1137481 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7586769152
    (h : (((758499669100999 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586507008) :
    (((758525858463543 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586769152 := by
  exact
    theta_restart_gain 7586507008 7586769152 15 11512 33 (758499669100999 / 100000)
      (758525858463543 / 100000) (1137481 / 50000) (454993 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7587031296
    (h : (((758525858463543 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7586769152) :
    (((758552011472679 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587031296 := by
  exact
    theta_restart_gain 7586769152 7587031296 15 11496 33 (758525858463543 / 100000)
      (758552011472679 / 100000) (1137483 / 50000) (2274969 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7587293440
    (h : (((758552011472679 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587031296) :
    (((189644557622601 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587293440 := by
  exact
    theta_restart_gain 7587031296 7587293440 15 11525 33 (758552011472679 / 100000)
      (189644557622601 / 25000) (2274969 / 100000) (568743 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7587555584
    (h : (((189644557622601 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587293440) :
    (((758604508703527 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587555584 := by
  exact
    theta_restart_gain 7587293440 7587555584 15 11551 33 (189644557622601 / 25000)
      (758604508703527 / 100000) (2274973 / 100000) (71093 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7587817728
    (h : (((758604508703527 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587555584) :
    (((151726108250779 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587817728 := by
  exact
    theta_restart_gain 7587555584 7587817728 15 11443 33 (758604508703527 / 100000)
      (151726108250779 / 20000) (71093 / 3125) (2274979 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7588079872
    (h : (((151726108250779 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7587817728) :
    (((758656789961597 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588079872 := by
  exact
    theta_restart_gain 7587817728 7588079872 15 11538 33 (151726108250779 / 20000)
      (758656789961597 / 100000) (2274979 / 100000) (1137491 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7588342016
    (h : (((758656789961597 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588079872) :
    (((379341434045863 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588342016 := by
  exact
    theta_restart_gain 7588079872 7588342016 15 11463 33 (758656789961597 / 100000)
      (379341434045863 / 50000) (2274983 / 100000) (1137493 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7588604160
    (h : (((379341434045863 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588342016) :
    (((37935462782717 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588604160 := by
  exact
    theta_restart_gain 7588342016 7588604160 15 11599 33 (379341434045863 / 50000)
      (37935462782717 / 5000) (1137493 / 50000) (2274989 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7588866304
    (h : (((37935462782717 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588604160) :
    (((75873538391449 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588866304 := by
  exact
    theta_restart_gain 7588604160 7588866304 15 11485 33 (37935462782717 / 5000)
      (75873538391449 / 10000) (227499 / 10000) (2274993 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7589128448
    (h : (((75873538391449 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7588866304) :
    (((189690394545973 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589128448 := by
  exact
    theta_restart_gain 7588866304 7589128448 15 11514 33 (75873538391449 / 10000)
      (189690394545973 / 25000) (2274993 / 100000) (568749 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7589390592
    (h : (((189690394545973 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589128448) :
    (((758787888524197 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589390592 := by
  exact
    theta_restart_gain 7589128448 7589390592 15 11565 33 (189690394545973 / 25000)
      (758787888524197 / 100000) (2274997 / 100000) (91 / 4) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7589652736
    (h : (((758787888524197 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589390592) :
    (((758813919074197 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589652736 := by
  exact
    theta_restart_gain 7589390592 7589652736 15 11442 33 (758787888524197 / 100000)
      (758813919074197 / 100000) (91 / 4) (2275003 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7589914880
    (h : (((758813919074197 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589652736) :
    (((758840379645721 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589914880 := by
  exact
    theta_restart_gain 7589652736 7589914880 15 11631 33 (758813919074197 / 100000)
      (758840379645721 / 100000) (568751 / 25000) (2275007 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7590177024
    (h : (((758840379645721 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7589914880) :
    (((758866401175787 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590177024 := by
  exact
    theta_restart_gain 7589914880 7590177024 15 11438 33 (758840379645721 / 100000)
      (758866401175787 / 100000) (2275007 / 100000) (227501 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7590439168
    (h : (((758866401175787 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590177024) :
    (((758892591102419 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590439168 := by
  exact
    theta_restart_gain 7590177024 7590439168 15 11512 33 (758866401175787 / 100000)
      (758892591102419 / 100000) (2275011 / 100000) (1137507 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7590701312
    (h : (((758892591102419 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590439168) :
    (((758918988089861 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590701312 := by
  exact
    theta_restart_gain 7590439168 7590701312 15 11603 33 (758892591102419 / 100000)
      (758918988089861 / 100000) (1137507 / 50000) (2275017 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7590963456
    (h : (((758918988089861 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590701312) :
    (((30357809853443 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590963456 := by
  exact
    theta_restart_gain 7590701312 7590963456 15 11542 33 (758918988089861 / 100000)
      (30357809853443 / 4000) (2275017 / 100000) (113751 / 5000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7591225600
    (h : (((30357809853443 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7590963456) :
    (((379485544149807 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591225600 := by
  exact
    theta_restart_gain 7590963456 7591225600 15 11359 33 (30357809853443 / 4000)
      (379485544149807 / 50000) (2275021 / 100000) (142189 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7591487744
    (h : (((379485544149807 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591225600) :
    (((379498528849287 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591487744 := by
  exact
    theta_restart_gain 7591225600 7591487744 15 11415 33 (379485544149807 / 50000)
      (379498528849287 / 50000) (142189 / 6250) (2275027 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7591749888
    (h : (((379498528849287 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591487744) :
    (((379511554522101 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591749888 := by
  exact
    theta_restart_gain 7591487744 7591749888 15 11451 33 (379498528849287 / 50000)
      (379511554522101 / 50000) (568757 / 25000) (2275031 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7592012032
    (h : (((379511554522101 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7591749888) :
    (((379524649600537 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592012032 := by
  exact
    theta_restart_gain 7591749888 7592012032 15 11512 33 (379511554522101 / 50000)
      (379524649600537 / 50000) (2275031 / 100000) (1137517 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7592274176
    (h : (((379524649600537 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592012032) :
    (((759075673681829 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592274176 := by
  exact
    theta_restart_gain 7592012032 7592274176 15 11593 33 (379524649600537 / 50000)
      (759075673681829 / 100000) (455007 / 20000) (1137519 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7592536320
    (h : (((759075673681829 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592274176) :
    (((759102036822173 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592536320 := by
  exact
    theta_restart_gain 7592274176 7592536320 15 11588 33 (759075673681829 / 100000)
      (759102036822173 / 100000) (1137519 / 50000) (2275041 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7592798464
    (h : (((759102036822173 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592536320) :
    (((759128402283911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592798464 := by
  exact
    theta_restart_gain 7592536320 7592798464 15 11589 33 (759102036822173 / 100000)
      (759128402283911 / 100000) (1137521 / 50000) (455009 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7593060608
    (h : (((759128402283911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7592798464) :
    (((379577208711743 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593060608 := by
  exact
    theta_restart_gain 7592798464 7593060608 15 11435 33 (759128402283911 / 100000)
      (379577208711743 / 50000) (455009 / 20000) (284381 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7593322752
    (h : (((379577208711743 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593060608) :
    (((379590326644277 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593322752 := by
  exact
    theta_restart_gain 7593060608 7593322752 15 11532 33 (379577208711743 / 50000)
      (379590326644277 / 50000) (2275049 / 100000) (568763 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7593584896
    (h : (((379590326644277 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593322752) :
    (((75920680046119 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593584896 := by
  exact
    theta_restart_gain 7593322752 7593584896 15 11493 33 (379590326644277 / 50000)
      (75920680046119 / 10000) (568763 / 25000) (455011 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7593847040
    (h : (((75920680046119 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593584896) :
    (((30369311900587 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593847040 := by
  exact
    theta_restart_gain 7593584896 7593847040 15 11427 33 (75920680046119 / 10000)
      (30369311900587 / 4000) (455011 / 20000) (1137529 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594109184
    (h : (((30369311900587 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7593847040) :
    (((94907350464263 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7594109184 := by
  exact
    theta_restart_gain 7593847040 7594109184 15 11431 33 (30369311900587 / 4000)
      (94907350464263 / 12500) (2275059 / 100000) (1137531 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594371328
    (h : (((94907350464263 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7594109184) :
    (((189821222393749 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594371328 := by
  exact
    theta_restart_gain 7594109184 7594371328 15 11466 33 (94907350464263 / 12500)
      (189821222393749 / 25000) (1137531 / 50000) (455013 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594387712
    (h : (((189821222393749 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594371328) :
    (((7592865822241 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594387712 := by
  exact
    theta_restart_gain 7594371328 7594387712 11 744 33 (189821222393749 / 25000)
      (7592865822241 / 1000) (1137533 / 50000) (2275069 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7594389760
    (h : (((7592865822241 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7594387712) :
    (((47455422479953 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7594389760 := by
  exact
    theta_restart_gain 7594387712 7594389760 8 78 33 (7592865822241 / 1000) (47455422479953 / 6250)
      (1137533 / 50000) (2275069 / 100000) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7594389760
    (h : (((756089196367119 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562389760) :
    (((47455422479953 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7594389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7594389760 point7594387712)
                  (Function.comp point7594371328 point7594109184))
                (Function.comp (Function.comp point7593847040 point7593584896)
                  (Function.comp point7593322752 point7593060608)))
              (Function.comp
                (Function.comp (Function.comp point7592798464 point7592536320)
                  (Function.comp point7592274176 point7592012032))
                (Function.comp (Function.comp point7591749888 point7591487744)
                  (Function.comp point7591225600 point7590963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7590701312 point7590439168)
                  (Function.comp point7590177024 point7589914880))
                (Function.comp (Function.comp point7589652736 point7589390592)
                  (Function.comp point7589128448 point7588866304)))
              (Function.comp
                (Function.comp (Function.comp point7588604160 point7588342016)
                  (Function.comp point7588079872 point7587817728))
                (Function.comp (Function.comp point7587555584 point7587293440)
                  (Function.comp point7587031296 point7586769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7586507008 point7586244864)
                  (Function.comp point7585982720 point7585720576))
                (Function.comp (Function.comp point7585458432 point7585196288)
                  (Function.comp point7584934144 point7584672000)))
              (Function.comp
                (Function.comp (Function.comp point7584409856 point7584147712)
                  (Function.comp point7583885568 point7583623424))
                (Function.comp (Function.comp point7583361280 point7583099136)
                  (Function.comp point7582836992 point7582574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7582312704 point7582050560)
                  (Function.comp point7581788416 point7581526272))
                (Function.comp (Function.comp point7581264128 point7581001984)
                  (Function.comp point7580739840 point7580477696)))
              (Function.comp
                (Function.comp (Function.comp point7580215552 point7579953408)
                  (Function.comp point7579691264 point7579429120))
                (Function.comp (Function.comp point7579166976 point7578904832)
                  (Function.comp point7578642688 point7578380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7578118400 point7577856256)
                  (Function.comp point7577594112 point7577331968))
                (Function.comp (Function.comp point7577069824 point7576807680)
                  (Function.comp point7576545536 point7576283392)))
              (Function.comp
                (Function.comp (Function.comp point7576021248 point7575759104)
                  (Function.comp point7575496960 point7575234816))
                (Function.comp (Function.comp point7574972672 point7574710528)
                  (Function.comp point7574448384 point7574186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7573924096 point7573661952)
                  (Function.comp point7573399808 point7573137664))
                (Function.comp (Function.comp point7572875520 point7572613376)
                  (Function.comp point7572351232 point7572089088)))
              (Function.comp
                (Function.comp (Function.comp point7571826944 point7571564800)
                  (Function.comp point7571302656 point7571040512))
                (Function.comp (Function.comp point7570778368 point7570516224)
                  (Function.comp point7570254080 point7569991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7569729792 point7569467648)
                  (Function.comp point7569205504 point7568943360))
                (Function.comp (Function.comp point7568681216 point7568419072)
                  (Function.comp point7568156928 point7567894784)))
              (Function.comp
                (Function.comp (Function.comp point7567632640 point7567370496)
                  (Function.comp point7567108352 point7566846208))
                (Function.comp (Function.comp point7566584064 point7566321920)
                  (Function.comp point7566059776 point7565797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7565535488 point7565273344)
                  (Function.comp point7565011200 point7564749056))
                (Function.comp (Function.comp point7564486912 point7564224768)
                  (Function.comp point7563962624 point7563700480)))
              (Function.comp (Function.comp point7563438336 point7563176192)
                (Function.comp point7562914048 point7562651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
