/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7530389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498651904
    (h : (((374845069562697 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498389760) :
    (((46857286601463 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7498651904 := by
  exact
    theta_restart_gain 7498389760 7498651904 15 11631 33 (374845069562697 / 50000)
      (46857286601463 / 6250) (1136897 / 50000) (2273797 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7498914048
    (h : (((46857286601463 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7498651904) :
    (((374871451274943 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498914048 := by
  exact
    theta_restart_gain 7498651904 7498914048 15 11574 33 (46857286601463 / 6250)
      (374871451274943 / 50000) (2273797 / 100000) (11369 / 500) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7499176192
    (h : (((374871451274943 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498914048) :
    (((374884539273499 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499176192 := by
  exact
    theta_restart_gain 7498914048 7499176192 15 11512 33 (374871451274943 / 50000)
      (374884539273499 / 50000) (2273801 / 100000) (568451 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7499438336
    (h : (((374884539273499 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499176192) :
    (((374897653438069 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499438336 := by
  exact
    theta_restart_gain 7499176192 7499438336 15 11535 33 (374884539273499 / 50000)
      (374897653438069 / 50000) (568451 / 25000) (2273807 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7499700480
    (h : (((374897653438069 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499438336) :
    (((374910688042429 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499700480 := by
  exact
    theta_restart_gain 7499438336 7499700480 15 11465 33 (374897653438069 / 50000)
      (374910688042429 / 50000) (142113 / 6250) (2273811 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7499962624
    (h : (((374910688042429 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499700480) :
    (((749847418042241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499962624 := by
  exact
    theta_restart_gain 7499700480 7499962624 15 11453 33 (374910688042429 / 50000)
      (749847418042241 / 100000) (2273811 / 100000) (1136907 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7500224768
    (h : (((749847418042241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7499962624) :
    (((374936791415723 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500224768 := by
  exact
    theta_restart_gain 7499962624 7500224768 15 11507 33 (749847418042241 / 100000)
      (374936791415723 / 50000) (454763 / 20000) (1136909 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7500486912
    (h : (((374936791415723 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500224768) :
    (((374949945452853 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500486912 := by
  exact
    theta_restart_gain 7500224768 7500486912 15 11570 33 (374936791415723 / 50000)
      (374949945452853 / 50000) (1136909 / 50000) (2273821 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7500749056
    (h : (((374949945452853 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500486912) :
    (((187481586706169 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500749056 := by
  exact
    theta_restart_gain 7500486912 7500749056 15 11635 33 (374949945452853 / 50000)
      (187481586706169 / 25000) (1136911 / 50000) (90953 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7501011200
    (h : (((187481586706169 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7500749056) :
    (((374976181965163 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501011200 := by
  exact
    theta_restart_gain 7500749056 7501011200 15 11442 33 (187481586706169 / 25000)
      (374976181965163 / 50000) (90953 / 4000) (568457 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7501273344
    (h : (((374976181965163 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501011200) :
    (((187494592996607 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501273344 := by
  exact
    theta_restart_gain 7501011200 7501273344 15 11438 33 (374976181965163 / 50000)
      (187494592996607 / 25000) (2273829 / 100000) (284229 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7501535488
    (h : (((187494592996607 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501273344) :
    (((187501151296553 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501535488 := by
  exact
    theta_restart_gain 7501273344 7501535488 15 11537 33 (187494592996607 / 25000)
      (187501151296553 / 25000) (284229 / 12500) (454767 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7501797632
    (h : (((187501151296553 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501535488) :
    (((187507711313413 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501797632 := by
  exact
    theta_restart_gain 7501535488 7501797632 15 11540 33 (187501151296553 / 25000)
      (187507711313413 / 25000) (568459 / 25000) (2273839 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7502059776
    (h : (((187507711313413 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7501797632) :
    (((150011420254517 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502059776 := by
  exact
    theta_restart_gain 7501797632 7502059776 15 11547 33 (187507711313413 / 25000)
      (150011420254517 / 20000) (2273839 / 100000) (1136921 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7502321920
    (h : (((150011420254517 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502059776) :
    (((750083004892041 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502321920 := by
  exact
    theta_restart_gain 7502059776 7502321920 15 11392 33 (150011420254517 / 20000)
      (750083004892041 / 100000) (2273843 / 100000) (1136923 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7502584064
    (h : (((750083004892041 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502321920) :
    (((150021859929437 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502584064 := by
  exact
    theta_restart_gain 7502321920 7502584064 15 11564 33 (750083004892041 / 100000)
      (150021859929437 / 20000) (1136923 / 50000) (2273849 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7502846208
    (h : (((150021859929437 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502584064) :
    (((150027097060757 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502846208 := by
  exact
    theta_restart_gain 7502584064 7502846208 15 11516 33 (150021859929437 / 20000)
      (150027097060757 / 20000) (45477 / 2000) (2273853 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7503108352
    (h : (((150027097060757 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7502846208) :
    (((37508094805319 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7503108352 := by
  exact
    theta_restart_gain 7502846208 7503108352 15 11615 33 (150027097060757 / 20000)
      (37508094805319 / 5000) (2273853 / 100000) (71058 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7503370496
    (h : (((37508094805319 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7503108352) :
    (((187546963614473 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7503370496 := by
  exact
    theta_restart_gain 7503108352 7503370496 15 11416 33 (37508094805319 / 5000)
      (187546963614473 / 25000) (2273857 / 100000) (113693 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7503632640
    (h : (((187546963614473 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7503370496) :
    (((23444187264956 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7503632640 := by
  exact
    theta_restart_gain 7503370496 7503632640 15 11495 33 (187546963614473 / 25000)
      (23444187264956 / 3125) (113693 / 5000) (2273863 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7503894784
    (h : (((23444187264956 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7503632640) :
    (((93780029961343 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7503894784 := by
  exact
    theta_restart_gain 7503632640 7503894784 15 11543 33 (23444187264956 / 3125)
      (93780029961343 / 12500) (284233 / 12500) (2273867 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7504156928
    (h : (((93780029961343 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7503894784) :
    (((750266659751417 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504156928 := by
  exact
    theta_restart_gain 7503894784 7504156928 15 11619 33 (93780029961343 / 12500)
      (750266659751417 / 100000) (2273867 / 100000) (227387 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7504419072
    (h : (((750266659751417 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504156928) :
    (((750293182182761 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504419072 := by
  exact
    theta_restart_gain 7504156928 7504419072 15 11664 33 (750266659751417 / 100000)
      (750293182182761 / 100000) (2273871 / 100000) (1136937 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7504681216
    (h : (((750293182182761 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504419072) :
    (((750319286256281 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504681216 := by
  exact
    theta_restart_gain 7504419072 7504681216 15 11480 33 (750293182182761 / 100000)
      (750319286256281 / 100000) (1136937 / 50000) (2273877 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7504943360
    (h : (((750319286256281 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504681216) :
    (((750345736005177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504943360 := by
  exact
    theta_restart_gain 7504681216 7504943360 15 11632 33 (750319286256281 / 100000)
      (750345736005177 / 100000) (1136939 / 50000) (2273881 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7505205504
    (h : (((750345736005177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7504943360) :
    (((187592989031747 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505205504 := by
  exact
    theta_restart_gain 7504943360 7505205504 15 11531 33 (750345736005177 / 100000)
      (187592989031747 / 25000) (2273881 / 100000) (568471 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7505467648
    (h : (((187592989031747 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505205504) :
    (((750398317275793 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505467648 := by
  exact
    theta_restart_gain 7505205504 7505467648 15 11593 33 (187592989031747 / 25000)
      (750398317275793 / 100000) (454777 / 20000) (71059 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7505729792
    (h : (((750398317275793 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505467648) :
    (((750424382853937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505729792 := by
  exact
    theta_restart_gain 7505467648 7505729792 15 11463 33 (750398317275793 / 100000)
      (750424382853937 / 100000) (71059 / 3125) (2273891 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7505991936
    (h : (((750424382853937 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505729792) :
    (((750450480312421 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505991936 := by
  exact
    theta_restart_gain 7505729792 7505991936 15 11477 33 (750424382853937 / 100000)
      (750450480312421 / 100000) (568473 / 25000) (454779 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7506254080
    (h : (((750450480312421 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7505991936) :
    (((750476711965141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7506254080 := by
  exact
    theta_restart_gain 7505991936 7506254080 15 11536 33 (750450480312421 / 100000)
      (750476711965141 / 100000) (454779 / 20000) (1136949 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7506516224
    (h : (((750476711965141 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7506254080) :
    (((187625729662779 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7506516224 := by
  exact
    theta_restart_gain 7506254080 7506516224 15 11525 33 (750476711965141 / 100000)
      (187625729662779 / 25000) (2273899 / 100000) (1136951 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7506778368
    (h : (((187625729662779 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7506516224) :
    (((23454035238924 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7506778368 := by
  exact
    theta_restart_gain 7506516224 7506778368 15 11526 33 (187625729662779 / 25000)
      (23454035238924 / 3125) (1136951 / 50000) (454781 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7507040512
    (h : (((23454035238924 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7506778368) :
    (((4690971223798 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7507040512 := by
  exact
    theta_restart_gain 7506778368 7507040512 15 11552 33 (23454035238924 / 3125)
      (4690971223798 / 625) (1136953 / 50000) (2273909 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7507302656
    (h : (((4690971223798 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7507040512) :
    (((187645359153387 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507302656 := by
  exact
    theta_restart_gain 7507040512 7507302656 15 11452 33 (4690971223798 / 625)
      (187645359153387 / 25000) (2273909 / 100000) (284239 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7507564800
    (h : (((187645359153387 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507302656) :
    (((750607643460873 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507564800 := by
  exact
    theta_restart_gain 7507302656 7507564800 15 11525 33 (187645359153387 / 25000)
      (750607643460873 / 100000) (2273913 / 100000) (568479 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7507826944
    (h : (((750607643460873 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507564800) :
    (((750634011790809 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507826944 := by
  exact
    theta_restart_gain 7507564800 7507826944 15 11596 33 (750607643460873 / 100000)
      (750634011790809 / 100000) (568479 / 25000) (2273919 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7508089088
    (h : (((750634011790809 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7507826944) :
    (((750660284662489 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508089088 := by
  exact
    theta_restart_gain 7507826944 7508089088 15 11554 33 (750634011790809 / 100000)
      (750660284662489 / 100000) (14212 / 625) (2273923 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7508351232
    (h : (((750660284662489 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508089088) :
    (((187671634275881 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508351232 := by
  exact
    theta_restart_gain 7508089088 7508351232 15 11545 33 (750660284662489 / 100000)
      (187671634275881 / 25000) (2273923 / 100000) (1136963 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7508613376
    (h : (((187671634275881 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508351232) :
    (((750712657702973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508613376 := by
  exact
    theta_restart_gain 7508351232 7508613376 15 11487 33 (187671634275881 / 25000)
      (750712657702973 / 100000) (2273927 / 100000) (227393 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7508875520
    (h : (((750712657702973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508613376) :
    (((750738892033383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508875520 := by
  exact
    theta_restart_gain 7508613376 7508875520 15 11537 33 (750712657702973 / 100000)
      (750738892033383 / 100000) (227393 / 10000) (2273933 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7509137664
    (h : (((750738892033383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7508875520) :
    (((750765069561591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509137664 := by
  exact
    theta_restart_gain 7508875520 7509137664 15 11512 33 (750738892033383 / 100000)
      (750765069561591 / 100000) (1136967 / 50000) (2273937 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7509399808
    (h : (((750765069561591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509137664) :
    (((750791251672209 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509399808 := by
  exact
    theta_restart_gain 7509137664 7509399808 15 11514 33 (750765069561591 / 100000)
      (750791251672209 / 100000) (2273937 / 100000) (113697 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7509661952
    (h : (((750791251672209 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509399808) :
    (((750817497499231 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509661952 := by
  exact
    theta_restart_gain 7509399808 7509661952 15 11542 33 (750791251672209 / 100000)
      (750817497499231 / 100000) (2273941 / 100000) (284243 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7509924096
    (h : (((750817497499231 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509661952) :
    (((150168784600491 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509924096 := by
  exact
    theta_restart_gain 7509661952 7509924096 15 11621 33 (750817497499231 / 100000)
      (150168784600491 / 20000) (284243 / 12500) (2273947 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7510186240
    (h : (((150168784600491 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7509924096) :
    (((750870009733911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510186240 := by
  exact
    theta_restart_gain 7509924096 7510186240 15 11472 33 (150168784600491 / 20000)
      (750870009733911 / 100000) (568487 / 25000) (2273951 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7510448384
    (h : (((750870009733911 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510186240) :
    (((187724044022017 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510448384 := by
  exact
    theta_restart_gain 7510186240 7510448384 15 11507 33 (750870009733911 / 100000)
      (187724044022017 / 25000) (2273951 / 100000) (1136977 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7510710528
    (h : (((187724044022017 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510448384) :
    (((750922415254813 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510710528 := by
  exact
    theta_restart_gain 7510448384 7510710528 15 11539 33 (187724044022017 / 25000)
      (750922415254813 / 100000) (454791 / 20000) (1136979 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7510972672
    (h : (((750922415254813 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510710528) :
    (((750948747688453 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510972672 := by
  exact
    theta_restart_gain 7510710528 7510972672 15 11580 33 (750922415254813 / 100000)
      (750948747688453 / 100000) (1136979 / 50000) (2273961 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7511234816
    (h : (((750948747688453 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7510972672) :
    (((150195030132247 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511234816 := by
  exact
    theta_restart_gain 7510972672 7511234816 15 11611 33 (750948747688453 / 100000)
      (150195030132247 / 20000) (1136981 / 50000) (454793 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7511496960
    (h : (((150195030132247 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511234816) :
    (((150200269347607 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511496960 := by
  exact
    theta_restart_gain 7511234816 7511496960 15 11520 33 (150195030132247 / 20000)
      (150200269347607 / 20000) (454793 / 20000) (142123 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7511759104
    (h : (((150200269347607 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511496960) :
    (((187756881735783 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511759104 := by
  exact
    theta_restart_gain 7511496960 7511759104 15 11513 33 (150200269347607 / 20000)
      (187756881735783 / 25000) (2273969 / 100000) (568493 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7512021248
    (h : (((187756881735783 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7511759104) :
    (((187763470569653 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512021248 := by
  exact
    theta_restart_gain 7511759104 7512021248 15 11590 33 (187756881735783 / 25000)
      (187763470569653 / 25000) (568493 / 25000) (90959 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7512283392
    (h : (((187763470569653 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512021248) :
    (((187770000291737 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512283392 := by
  exact
    theta_restart_gain 7512021248 7512283392 15 11486 33 (187763470569653 / 25000)
      (187770000291737 / 25000) (284247 / 12500) (2273979 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7512545536
    (h : (((187770000291737 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512283392) :
    (((375553010017333 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512545536 := by
  exact
    theta_restart_gain 7512283392 7512545536 15 11442 33 (187770000291737 / 25000)
      (375553010017333 / 50000) (2273979 / 100000) (1136991 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7512807680
    (h : (((375553010017333 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512545536) :
    (((187783062038647 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512807680 := by
  exact
    theta_restart_gain 7512545536 7512807680 15 11534 33 (375553010017333 / 50000)
      (187783062038647 / 25000) (2273983 / 100000) (1136993 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7513069824
    (h : (((187783062038647 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7512807680) :
    (((46947413296767 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7513069824 := by
  exact
    theta_restart_gain 7512807680 7513069824 15 11594 33 (187783062038647 / 25000)
      (46947413296767 / 6250) (1136993 / 50000) (2273989 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7513331968
    (h : (((46947413296767 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7513069824) :
    (((23474524147429 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7513331968 := by
  exact
    theta_restart_gain 7513069824 7513331968 15 11504 33 (46947413296767 / 6250)
      (23474524147429 / 3125) (2273989 / 100000) (284249 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7513594112
    (h : (((23474524147429 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7513331968) :
    (((23475338236923 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7513594112 := by
  exact
    theta_restart_gain 7513331968 7513594112 15 11456 33 (23474524147429 / 3125)
      (23475338236923 / 3125) (2273993 / 100000) (568499 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7513856256
    (h : (((23475338236923 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7513594112) :
    (((93904618974447 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7513856256 := by
  exact
    theta_restart_gain 7513594112 7513856256 15 11490 33 (23475338236923 / 3125)
      (93904618974447 / 12500) (568499 / 25000) (2273999 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7514118400
    (h : (((93904618974447 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7513856256) :
    (((93907890407697 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7514118400 := by
  exact
    theta_restart_gain 7513856256 7514118400 15 11509 33 (93904618974447 / 12500)
      (93907890407697 / 12500) (1137 / 50) (2274003 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7514380544
    (h : (((93907890407697 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7514118400) :
    (((187822423178157 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514380544 := by
  exact
    theta_restart_gain 7514118400 7514380544 15 11684 33 (93907890407697 / 12500)
      (187822423178157 / 25000) (2274003 / 100000) (1137003 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7514642688
    (h : (((187822423178157 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514380544) :
    (((187829035990513 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514642688 := by
  exact
    theta_restart_gain 7514380544 7514642688 15 11632 33 (187822423178157 / 25000)
      (187829035990513 / 25000) (2274007 / 100000) (227401 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7514904832
    (h : (((187829035990513 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514642688) :
    (((375671162319591 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514904832 := by
  exact
    theta_restart_gain 7514642688 7514904832 15 11513 33 (187829035990513 / 25000)
      (375671162319591 / 50000) (227401 / 10000) (2274013 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7515166976
    (h : (((375671162319591 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7514904832) :
    (((93921059190771 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7515166976 := by
  exact
    theta_restart_gain 7514904832 7515166976 15 11499 33 (375671162319591 / 50000)
      (93921059190771 / 12500) (1137007 / 50000) (2274017 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7515429120
    (h : (((93921059190771 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7515166976) :
    (((150278870822729 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515429120 := by
  exact
    theta_restart_gain 7515166976 7515429120 15 11381 33 (93921059190771 / 12500)
      (150278870822729 / 20000) (2274017 / 100000) (113701 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7515691264
    (h : (((150278870822729 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515429120) :
    (((751420609960111 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515691264 := by
  exact
    theta_restart_gain 7515429120 7515691264 15 11546 33 (150278870822729 / 20000)
      (751420609960111 / 100000) (2274021 / 100000) (284253 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7515953408
    (h : (((751420609960111 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515691264) :
    (((751446788524399 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515953408 := by
  exact
    theta_restart_gain 7515691264 7515953408 15 11512 33 (751420609960111 / 100000)
      (751446788524399 / 100000) (284253 / 12500) (2274027 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7516215552
    (h : (((751446788524399 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7515953408) :
    (((751473030807519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516215552 := by
  exact
    theta_restart_gain 7515953408 7516215552 15 11540 33 (751446788524399 / 100000)
      (751473030807519 / 100000) (568507 / 25000) (2274031 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7516477696
    (h : (((751473030807519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516215552) :
    (((150299807325207 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516477696 := by
  exact
    theta_restart_gain 7516215552 7516477696 15 11436 33 (751473030807519 / 100000)
      (150299807325207 / 20000) (2274031 / 100000) (1137017 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7516739840
    (h : (((150299807325207 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516477696) :
    (((37576279299233 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516739840 := by
  exact
    theta_restart_gain 7516477696 7516739840 15 11675 33 (150299807325207 / 20000)
      (37576279299233 / 5000) (454807 / 20000) (1137019 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7517001984
    (h : (((37576279299233 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7516739840) :
    (((4697198216758 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7517001984 := by
  exact
    theta_restart_gain 7516739840 7517001984 15 11490 33 (37576279299233 / 5000)
      (4697198216758 / 625) (1137019 / 50000) (2274041 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7517264128
    (h : (((4697198216758 / 625) : ℚ) : ℝ) ≤ Chebyshev.theta 7517001984) :
    (((187894576832107 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517264128 := by
  exact
    theta_restart_gain 7517001984 7517264128 15 11694 33 (4697198216758 / 625)
      (187894576832107 / 25000) (1137021 / 50000) (454809 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7517526272
    (h : (((187894576832107 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517264128) :
    (((751604533889413 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517526272 := by
  exact
    theta_restart_gain 7517264128 7517526272 15 11533 33 (187894576832107 / 25000)
      (751604533889413 / 100000) (454809 / 20000) (71064 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7517788416
    (h : (((751604533889413 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517526272) :
    (((751630585394757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517788416 := by
  exact
    theta_restart_gain 7517526272 7517788416 15 11456 33 (751604533889413 / 100000)
      (751630585394757 / 100000) (2274049 / 100000) (568513 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7518050560
    (h : (((751630585394757 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7517788416) :
    (((751656991686581 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518050560 := by
  exact
    theta_restart_gain 7517788416 7518050560 15 11612 33 (751630585394757 / 100000)
      (751656991686581 / 100000) (568513 / 25000) (454811 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7518312704
    (h : (((751656991686581 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518050560) :
    (((751683200181981 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518312704 := by
  exact
    theta_restart_gain 7518050560 7518312704 15 11525 33 (751656991686581 / 100000)
      (751683200181981 / 100000) (284257 / 12500) (2274059 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7518574848
    (h : (((751683200181981 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518312704) :
    (((751709438274723 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518574848 := by
  exact
    theta_restart_gain 7518312704 7518574848 15 11538 33 (751683200181981 / 100000)
      (751709438274723 / 100000) (2274059 / 100000) (1137031 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7518836992
    (h : (((751709438274723 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518574848) :
    (((75173533757823 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518836992 := by
  exact
    theta_restart_gain 7518574848 7518836992 15 11389 33 (751709438274723 / 100000)
      (75173533757823 / 10000) (2274063 / 100000) (1137033 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7519099136
    (h : (((75173533757823 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7518836992) :
    (((187940394506451 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519099136 := by
  exact
    theta_restart_gain 7518836992 7519099136 15 11539 33 (75173533757823 / 10000)
      (187940394506451 / 25000) (1137033 / 50000) (2274069 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7519361280
    (h : (((187940394506451 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519099136) :
    (((23493365562307 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7519361280 := by
  exact
    theta_restart_gain 7519099136 7519361280 15 11486 33 (187940394506451 / 25000)
      (23493365562307 / 3125) (227407 / 10000) (2274073 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7519623424
    (h : (((23493365562307 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7519361280) :
    (((375906913546297 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519623424 := by
  exact
    theta_restart_gain 7519361280 7519623424 15 11490 33 (23493365562307 / 3125)
      (375906913546297 / 50000) (2274073 / 100000) (568519 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7519885568
    (h : (((375906913546297 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519623424) :
    (((751840003992941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519885568 := by
  exact
    theta_restart_gain 7519623424 7519885568 15 11511 33 (375906913546297 / 50000)
      (751840003992941 / 100000) (2274077 / 100000) (14213 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7520147712
    (h : (((751840003992941 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7519885568) :
    (((751866324194861 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520147712 := by
  exact
    theta_restart_gain 7519885568 7520147712 15 11574 33 (751840003992941 / 100000)
      (751866324194861 / 100000) (14213 / 625) (2274083 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7520409856
    (h : (((751866324194861 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520147712) :
    (((751892339715821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520409856 := by
  exact
    theta_restart_gain 7520147712 7520409856 15 11440 33 (751866324194861 / 100000)
      (751892339715821 / 100000) (568521 / 25000) (2274087 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7520672000
    (h : (((751892339715821 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520409856) :
    (((18797958711221 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7520672000 := by
  exact
    theta_restart_gain 7520409856 7520672000 15 11437 33 (751892339715821 / 100000)
      (18797958711221 / 2500) (2274087 / 100000) (227409 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7520934144
    (h : (((18797958711221 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7520672000) :
    (((751944475480339 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520934144 := by
  exact
    theta_restart_gain 7520672000 7520934144 15 11489 33 (18797958711221 / 2500)
      (751944475480339 / 100000) (2274091 / 100000) (1137047 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7521196288
    (h : (((751944475480339 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7520934144) :
    (((751970661672749 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521196288 := by
  exact
    theta_restart_gain 7520934144 7521196288 15 11515 33 (751944475480339 / 100000)
      (751970661672749 / 100000) (1137047 / 50000) (2274097 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7521458432
    (h : (((751970661672749 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521196288) :
    (((751997129899371 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521458432 := by
  exact
    theta_restart_gain 7521196288 7521458432 15 11639 33 (751970661672749 / 100000)
      (751997129899371 / 100000) (1137049 / 50000) (2274101 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7521720576
    (h : (((751997129899371 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521458432) :
    (((376011621700577 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521720576 := by
  exact
    theta_restart_gain 7521458432 7521720576 15 11483 33 (751997129899371 / 100000)
      (376011621700577 / 50000) (2274101 / 100000) (284263 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7521982720
    (h : (((376011621700577 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521720576) :
    (((188012411440051 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521982720 := by
  exact
    theta_restart_gain 7521720576 7521982720 15 11610 33 (376011621700577 / 50000)
      (188012411440051 / 25000) (454821 / 20000) (568527 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7522244864
    (h : (((188012411440051 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7521982720) :
    (((188019032505493 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522244864 := by
  exact
    theta_restart_gain 7521982720 7522244864 15 11646 33 (188012411440051 / 25000)
      (188019032505493 / 25000) (568527 / 25000) (2274111 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7522507008
    (h : (((188019032505493 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522244864) :
    (((188025502922661 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522507008 := by
  exact
    theta_restart_gain 7522244864 7522507008 15 11381 33 (188019032505493 / 25000)
      (188025502922661 / 25000) (71066 / 3125) (454823 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7522769152
    (h : (((188025502922661 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522507008) :
    (((752128348216459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522769152 := by
  exact
    theta_restart_gain 7522507008 7522769152 15 11581 33 (188025502922661 / 25000)
      (752128348216459 / 100000) (454823 / 20000) (1137059 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7523031296
    (h : (((752128348216459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7522769152) :
    (((752154318655439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523031296 := by
  exact
    theta_restart_gain 7522769152 7523031296 15 11420 33 (752128348216459 / 100000)
      (752154318655439 / 100000) (2274119 / 100000) (1137061 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7523293440
    (h : (((752154318655439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523031296) :
    (((752180359626461 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523293440 := by
  exact
    theta_restart_gain 7523031296 7523293440 15 11451 33 (752154318655439 / 100000)
      (752180359626461 / 100000) (1137061 / 50000) (18193 / 800) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7523555584
    (h : (((752180359626461 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523293440) :
    (((752206666704461 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523555584 := by
  exact
    theta_restart_gain 7523293440 7523555584 15 11568 33 (752180359626461 / 100000)
      (752206666704461 / 100000) (18193 / 800) (142133 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7523817728
    (h : (((752206666704461 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523555584) :
    (((376116328862401 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523817728 := by
  exact
    theta_restart_gain 7523555584 7523817728 15 11429 33 (752206666704461 / 100000)
      (376116328862401 / 50000) (2274129 / 100000) (568533 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7524079872
    (h : (((376116328862401 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7523817728) :
    (((376129390339543 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524079872 := by
  exact
    theta_restart_gain 7523817728 7524079872 15 11487 33 (376116328862401 / 50000)
      (376129390339543 / 50000) (568533 / 25000) (454827 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7524342016
    (h : (((376129390339543 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524079872) :
    (((376142388163851 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524342016 := by
  exact
    theta_restart_gain 7524079872 7524342016 15 11431 33 (376129390339543 / 50000)
      (376142388163851 / 50000) (284267 / 12500) (2274139 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7524604160
    (h : (((376142388163851 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524342016) :
    (((752311213193577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524604160 := by
  exact
    theta_restart_gain 7524342016 7524604160 15 11625 33 (376142388163851 / 50000)
      (752311213193577 / 100000) (2274139 / 100000) (1137071 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7524866304
    (h : (((752311213193577 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524604160) :
    (((376168609009391 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524866304 := by
  exact
    theta_restart_gain 7524604160 7524866304 15 11435 33 (752311213193577 / 100000)
      (376168609009391 / 50000) (2274143 / 100000) (1137073 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7525128448
    (h : (((376168609009391 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7524866304) :
    (((376181905941053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525128448 := by
  exact
    theta_restart_gain 7524866304 7525128448 15 11694 33 (376168609009391 / 50000)
      (376181905941053 / 50000) (1137073 / 50000) (2274149 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7525390592
    (h : (((376181905941053 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525128448) :
    (((376195007319203 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525390592 := by
  exact
    theta_restart_gain 7525128448 7525390592 15 11522 33 (376181905941053 / 50000)
      (376195007319203 / 50000) (45483 / 2000) (2274153 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7525652736
    (h : (((376195007319203 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525390592) :
    (((752416246993261 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525652736 := by
  exact
    theta_restart_gain 7525390592 7525652736 15 11535 33 (376195007319203 / 50000)
      (752416246993261 / 100000) (2274153 / 100000) (568539 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7525914880
    (h : (((752416246993261 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525652736) :
    (((150488489966043 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525914880 := by
  exact
    theta_restart_gain 7525652736 7525914880 15 11522 33 (752416246993261 / 100000)
      (150488489966043 / 20000) (2274157 / 100000) (28427 / 1250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7526177024
    (h : (((150488489966043 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7525914880) :
    (((150493771475227 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526177024 := by
  exact
    theta_restart_gain 7525914880 7526177024 15 11612 33 (150488489966043 / 20000)
      (150493771475227 / 20000) (28427 / 1250) (2274163 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7526439168
    (h : (((150493771475227 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526177024) :
    (((752495251323519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526439168 := by
  exact
    theta_restart_gain 7526177024 7526439168 15 11606 33 (150493771475227 / 20000)
      (752495251323519 / 100000) (568541 / 25000) (2274167 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7526701312
    (h : (((752495251323519 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526439168) :
    (((376260639582417 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526701312 := by
  exact
    theta_restart_gain 7526439168 7526701312 15 11445 33 (752495251323519 / 100000)
      (376260639582417 / 50000) (2274167 / 100000) (227417 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7526963456
    (h : (((376260639582417 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526701312) :
    (((188136845524893 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526963456 := by
  exact
    theta_restart_gain 7526701312 7526963456 15 11478 33 (376260639582417 / 50000)
      (188136845524893 / 25000) (2274171 / 100000) (1137087 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7527225600
    (h : (((188136845524893 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7526963456) :
    (((75257377843719 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527225600 := by
  exact
    theta_restart_gain 7526963456 7527225600 15 11607 33 (188136845524893 / 25000)
      (75257377843719 / 10000) (1137087 / 50000) (2274177 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7527487744
    (h : (((75257377843719 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527225600) :
    (((376299972564629 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527487744 := by
  exact
    theta_restart_gain 7527225600 7527487744 15 11506 33 (75257377843719 / 10000)
      (376299972564629 / 50000) (1137089 / 50000) (2274181 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7527749888
    (h : (((376299972564629 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527487744) :
    (((15052523419691 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527749888 := by
  exact
    theta_restart_gain 7527487744 7527749888 15 11532 33 (376299972564629 / 50000)
      (15052523419691 / 2000) (2274181 / 100000) (284273 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7528012032
    (h : (((15052523419691 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7527749888) :
    (((75265239688597 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528012032 := by
  exact
    theta_restart_gain 7527749888 7528012032 15 11532 33 (15052523419691 / 2000)
      (75265239688597 / 10000) (454837 / 20000) (568547 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7528274176
    (h : (((75265239688597 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528012032) :
    (((376339239774071 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528274176 := by
  exact
    theta_restart_gain 7528012032 7528274176 15 11469 33 (75265239688597 / 10000)
      (376339239774071 / 50000) (568547 / 25000) (2274191 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7528536320
    (h : (((376339239774071 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528274176) :
    (((75270453951427 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528536320 := by
  exact
    theta_restart_gain 7528274176 7528536320 15 11459 33 (376339239774071 / 50000)
      (75270453951427 / 10000) (142137 / 6250) (454839 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7528798464
    (h : (((75270453951427 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528536320) :
    (((37636539868487 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528798464 := by
  exact
    theta_restart_gain 7528536320 7528798464 15 11546 33 (75270453951427 / 10000)
      (37636539868487 / 5000) (454839 / 20000) (1137099 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7529060608
    (h : (((37636539868487 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7528798464) :
    (((752757366836657 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529060608 := by
  exact
    theta_restart_gain 7528798464 7529060608 15 11683 33 (37636539868487 / 5000)
      (752757366836657 / 100000) (2274199 / 100000) (1137101 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7529322752
    (h : (((752757366836657 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529060608) :
    (((752783406449557 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529322752 := by
  exact
    theta_restart_gain 7529060608 7529322752 15 11450 33 (752757366836657 / 100000)
      (752783406449557 / 100000) (1137101 / 50000) (454841 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7529584896
    (h : (((752783406449557 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529322752) :
    (((150561917876647 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529584896 := by
  exact
    theta_restart_gain 7529322752 7529584896 15 11513 33 (752783406449557 / 100000)
      (150561917876647 / 20000) (1137103 / 50000) (2274209 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7529847040
    (h : (((150561917876647 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529584896) :
    (((188208947636281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529847040 := by
  exact
    theta_restart_gain 7529584896 7529847040 15 11521 33 (150561917876647 / 20000)
      (188208947636281 / 25000) (2274209 / 100000) (568553 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530109184
    (h : (((188208947636281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7529847040) :
    (((752862132754303 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530109184 := by
  exact
    theta_restart_gain 7529847040 7530109184 15 11583 33 (188208947636281 / 25000)
      (752862132754303 / 100000) (2274213 / 100000) (284277 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530371328
    (h : (((752862132754303 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530109184) :
    (((752888127043183 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530371328 := by
  exact
    theta_restart_gain 7530109184 7530371328 15 11430 33 (752862132754303 / 100000)
      (752888127043183 / 100000) (284277 / 12500) (2274219 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530387712
    (h : (((752888127043183 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530371328) :
    (((752889664415903 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530387712 := by
  exact
    theta_restart_gain 7530371328 7530387712 11 676 33 (752888127043183 / 100000)
      (752889664415903 / 100000) (113711 / 5000) (2274223 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530389760
    (h : (((752889664415903 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530387712) :
    (((752889887289463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530389760 := by
  exact
    theta_restart_gain 7530387712 7530389760 8 98 33 (752889664415903 / 100000)
      (752889887289463 / 100000) (113711 / 5000) (2274223 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7530389760
    (h : (((374845069562697 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7498389760) :
    (((752889887289463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7530389760 point7530387712)
                  (Function.comp point7530371328 point7530109184))
                (Function.comp (Function.comp point7529847040 point7529584896)
                  (Function.comp point7529322752 point7529060608)))
              (Function.comp
                (Function.comp (Function.comp point7528798464 point7528536320)
                  (Function.comp point7528274176 point7528012032))
                (Function.comp (Function.comp point7527749888 point7527487744)
                  (Function.comp point7527225600 point7526963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7526701312 point7526439168)
                  (Function.comp point7526177024 point7525914880))
                (Function.comp (Function.comp point7525652736 point7525390592)
                  (Function.comp point7525128448 point7524866304)))
              (Function.comp
                (Function.comp (Function.comp point7524604160 point7524342016)
                  (Function.comp point7524079872 point7523817728))
                (Function.comp (Function.comp point7523555584 point7523293440)
                  (Function.comp point7523031296 point7522769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7522507008 point7522244864)
                  (Function.comp point7521982720 point7521720576))
                (Function.comp (Function.comp point7521458432 point7521196288)
                  (Function.comp point7520934144 point7520672000)))
              (Function.comp
                (Function.comp (Function.comp point7520409856 point7520147712)
                  (Function.comp point7519885568 point7519623424))
                (Function.comp (Function.comp point7519361280 point7519099136)
                  (Function.comp point7518836992 point7518574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7518312704 point7518050560)
                  (Function.comp point7517788416 point7517526272))
                (Function.comp (Function.comp point7517264128 point7517001984)
                  (Function.comp point7516739840 point7516477696)))
              (Function.comp
                (Function.comp (Function.comp point7516215552 point7515953408)
                  (Function.comp point7515691264 point7515429120))
                (Function.comp (Function.comp point7515166976 point7514904832)
                  (Function.comp point7514642688 point7514380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7514118400 point7513856256)
                  (Function.comp point7513594112 point7513331968))
                (Function.comp (Function.comp point7513069824 point7512807680)
                  (Function.comp point7512545536 point7512283392)))
              (Function.comp
                (Function.comp (Function.comp point7512021248 point7511759104)
                  (Function.comp point7511496960 point7511234816))
                (Function.comp (Function.comp point7510972672 point7510710528)
                  (Function.comp point7510448384 point7510186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7509924096 point7509661952)
                  (Function.comp point7509399808 point7509137664))
                (Function.comp (Function.comp point7508875520 point7508613376)
                  (Function.comp point7508351232 point7508089088)))
              (Function.comp
                (Function.comp (Function.comp point7507826944 point7507564800)
                  (Function.comp point7507302656 point7507040512))
                (Function.comp (Function.comp point7506778368 point7506516224)
                  (Function.comp point7506254080 point7505991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7505729792 point7505467648)
                  (Function.comp point7505205504 point7504943360))
                (Function.comp (Function.comp point7504681216 point7504419072)
                  (Function.comp point7504156928 point7503894784)))
              (Function.comp
                (Function.comp (Function.comp point7503632640 point7503370496)
                  (Function.comp point7503108352 point7502846208))
                (Function.comp (Function.comp point7502584064 point7502321920)
                  (Function.comp point7502059776 point7501797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7501535488 point7501273344)
                  (Function.comp point7501011200 point7500749056))
                (Function.comp (Function.comp point7500486912 point7500224768)
                  (Function.comp point7499962624 point7499700480)))
              (Function.comp (Function.comp point7499438336 point7499176192)
                (Function.comp point7498914048 point7498651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
