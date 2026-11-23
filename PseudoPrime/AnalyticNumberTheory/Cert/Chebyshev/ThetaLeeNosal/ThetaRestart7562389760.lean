/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7562389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530651904
    (h : (((752889887289463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530389760) :
    (((752916074932763 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530651904 := by
  exact
    theta_restart_gain 7530389760 7530651904 15 11515 33 (752889887289463 / 100000)
      (752916074932763 / 100000) (113711 / 5000) (2274223 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7530914048
    (h : (((752916074932763 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530651904) :
    (((752942333111521 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530914048 := by
  exact
    theta_restart_gain 7530651904 7530914048 15 11546 33 (752916074932763 / 100000)
      (752942333111521 / 100000) (2274223 / 100000) (1137113 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7531176192
    (h : (((752942333111521 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530914048) :
    (((376484333192977 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531176192 := by
  exact
    theta_restart_gain 7530914048 7531176192 15 11579 33 (752942333111521 / 100000)
      (376484333192977 / 50000) (2274227 / 100000) (227423 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7531438336
    (h : (((376484333192977 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531176192) :
    (((376497507807367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531438336 := by
  exact
    theta_restart_gain 7531176192 7531438336 15 11586 33 (376484333192977 / 50000)
      (376497507807367 / 50000) (227423 / 10000) (2274233 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7531700480
    (h : (((376497507807367 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531438336) :
    (((94127633939209 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7531700480 := by
  exact
    theta_restart_gain 7531438336 7531700480 15 11457 33 (376497507807367 / 50000)
      (94127633939209 / 12500) (1137117 / 50000) (2274237 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7531962624
    (h : (((94127633939209 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7531700480) :
    (((188261879085377 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531962624 := by
  exact
    theta_restart_gain 7531700480 7531962624 15 11628 33 (94127633939209 / 12500)
      (188261879085377 / 25000) (2274237 / 100000) (14214 / 625) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7532224768
    (h : (((188261879085377 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7531962624) :
    (((753073740614479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532224768 := by
  exact
    theta_restart_gain 7531962624 7532224768 15 11531 33 (188261879085377 / 25000)
      (753073740614479 / 100000) (2274241 / 100000) (568561 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7532486912
    (h : (((753073740614479 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532224768) :
    (((753099905791699 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532486912 := by
  exact
    theta_restart_gain 7532224768 7532486912 15 11505 33 (753073740614479 / 100000)
      (753099905791699 / 100000) (568561 / 25000) (2274247 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7532749056
    (h : (((753099905791699 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532486912) :
    (((753126300713987 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532749056 := by
  exact
    theta_restart_gain 7532486912 7532749056 15 11606 33 (753099905791699 / 100000)
      (753126300713987 / 100000) (284281 / 12500) (2274251 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7533011200
    (h : (((753126300713987 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7532749056) :
    (((376576292116397 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533011200 := by
  exact
    theta_restart_gain 7532749056 7533011200 15 11557 33 (753126300713987 / 100000)
      (376576292116397 / 50000) (2274251 / 100000) (1137127 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7533273344
    (h : (((376576292116397 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533011200) :
    (((753178462980439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533273344 := by
  exact
    theta_restart_gain 7533011200 7533273344 15 11379 33 (376576292116397 / 50000)
      (753178462980439 / 100000) (454851 / 20000) (1137129 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7533535488
    (h : (((753178462980439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533273344) :
    (((150640937944739 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533535488 := by
  exact
    theta_restart_gain 7533273344 7533535488 15 11532 33 (753178462980439 / 100000)
      (150640937944739 / 20000) (1137129 / 50000) (2274261 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7533797632
    (h : (((150640937944739 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533535488) :
    (((753230748217691 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533797632 := by
  exact
    theta_restart_gain 7533535488 7533797632 15 11458 33 (150640937944739 / 20000)
      (753230748217691 / 100000) (1137131 / 50000) (454853 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7534059776
    (h : (((753230748217691 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7533797632) :
    (((753257015978441 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534059776 := by
  exact
    theta_restart_gain 7533797632 7534059776 15 11550 33 (753230748217691 / 100000)
      (753257015978441 / 100000) (454853 / 20000) (568567 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7534321920
    (h : (((753257015978441 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534059776) :
    (((753283208722997 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534321920 := by
  exact
    theta_restart_gain 7534059776 7534321920 15 11517 33 (753257015978441 / 100000)
      (753283208722997 / 100000) (568567 / 25000) (2274271 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7534584064
    (h : (((753283208722997 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534321920) :
    (((753309396965077 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534584064 := by
  exact
    theta_restart_gain 7534321920 7534584064 15 11515 33 (753283208722997 / 100000)
      (753309396965077 / 100000) (71071 / 3125) (90971 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7534846208
    (h : (((753309396965077 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534584064) :
    (((753335605710177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534846208 := by
  exact
    theta_restart_gain 7534584064 7534846208 15 11524 33 (753309396965077 / 100000)
      (753335605710177 / 100000) (90971 / 4000) (1137139 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7535108352
    (h : (((753335605710177 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7534846208) :
    (((753361841792721 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535108352 := by
  exact
    theta_restart_gain 7534846208 7535108352 15 11536 33 (753335605710177 / 100000)
      (753361841792721 / 100000) (2274279 / 100000) (1137141 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7535370496
    (h : (((753361841792721 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535108352) :
    (((6027103913703 / 800) : ℚ) : ℝ) ≤ Chebyshev.theta 7535370496 := by
  exact
    theta_restart_gain 7535108352 7535370496 15 11497 33 (753361841792721 / 100000)
      (6027103913703 / 800) (1137141 / 50000) (454857 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7535632640
    (h : (((6027103913703 / 800) : ℚ) : ℝ) ≤ Chebyshev.theta 7535370496) :
    (((753414129856159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535632640 := by
  exact
    theta_restart_gain 7535370496 7535632640 15 11494 33 (6027103913703 / 800)
      (753414129856159 / 100000) (1137143 / 50000) (2274289 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7535894784
    (h : (((753414129856159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535632640) :
    (((376720195535621 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535894784 := by
  exact
    theta_restart_gain 7535632640 7535894784 15 11547 33 (753414129856159 / 100000)
      (376720195535621 / 50000) (2274289 / 100000) (568573 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7536156928
    (h : (((376720195535621 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7535894784) :
    (((376733368240677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536156928 := by
  exact
    theta_restart_gain 7535894784 7536156928 15 11584 33 (376720195535621 / 50000)
      (376733368240677 / 50000) (2274293 / 100000) (284287 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7536419072
    (h : (((376733368240677 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536156928) :
    (((75349280218781 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536419072 := by
  exact
    theta_restart_gain 7536156928 7536419072 15 11461 33 (376733368240677 / 50000)
      (75349280218781 / 10000) (284287 / 12500) (2274299 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7536681216
    (h : (((75349280218781 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536419072) :
    (((75351881108261 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536681216 := by
  exact
    theta_restart_gain 7536419072 7536681216 15 11436 33 (75349280218781 / 10000)
      (75351881108261 / 10000) (22743 / 1000) (2274303 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7536943360
    (h : (((75351881108261 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536681216) :
    (((30141808174757 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536943360 := by
  exact
    theta_restart_gain 7536681216 7536943360 15 11605 33 (75351881108261 / 10000)
      (30141808174757 / 4000) (2274303 / 100000) (1137153 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7537205504
    (h : (((30141808174757 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7536943360) :
    (((753571408934179 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537205504 := by
  exact
    theta_restart_gain 7536943360 7537205504 15 11522 33 (30141808174757 / 4000)
      (753571408934179 / 100000) (2274307 / 100000) (227431 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7537467648
    (h : (((753571408934179 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537205504) :
    (((753597695409159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537467648 := by
  exact
    theta_restart_gain 7537205504 7537467648 15 11558 33 (753571408934179 / 100000)
      (753597695409159 / 100000) (227431 / 10000) (2274313 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7537729792
    (h : (((753597695409159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537467648) :
    (((753624031965279 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537729792 := by
  exact
    theta_restart_gain 7537467648 7537729792 15 11580 33 (753597695409159 / 100000)
      (753624031965279 / 100000) (1137157 / 50000) (2274317 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7537991936
    (h : (((753624031965279 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537729792) :
    (((376825192238179 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537991936 := by
  exact
    theta_restart_gain 7537729792 7537991936 15 11587 33 (753624031965279 / 100000)
      (376825192238179 / 50000) (2274317 / 100000) (28429 / 1250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7538254080
    (h : (((376825192238179 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7537991936) :
    (((188419208707397 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7538254080 := by
  exact
    theta_restart_gain 7537991936 7538254080 15 11630 33 (376825192238179 / 50000)
      (188419208707397 / 25000) (2274321 / 100000) (568581 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7538516224
    (h : (((188419208707397 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7538254080) :
    (((94212892173331 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7538516224 := by
  exact
    theta_restart_gain 7538254080 7538516224 15 11565 33 (188419208707397 / 25000)
      (94212892173331 / 12500) (568581 / 25000) (2274327 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7538778368
    (h : (((94212892173331 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7538516224) :
    (((1884322712987 / 250) : ℚ) : ℝ) ≤ Chebyshev.theta 7538778368 := by
  exact
    theta_restart_gain 7538516224 7538778368 15 11409 33 (94212892173331 / 12500)
      (1884322712987 / 250) (284291 / 12500) (2274331 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7539040512
    (h : (((1884322712987 / 250) : ℚ) : ℝ) ≤ Chebyshev.theta 7538778368) :
    (((94219403862997 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7539040512 := by
  exact
    theta_restart_gain 7538778368 7539040512 15 11496 33 (1884322712987 / 250)
      (94219403862997 / 12500) (2274331 / 100000) (1137167 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7539302656
    (h : (((94219403862997 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7539040512) :
    (((753781310703421 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539302656 := by
  exact
    theta_restart_gain 7539040512 7539302656 15 11467 33 (94219403862997 / 12500)
      (753781310703421 / 100000) (454867 / 20000) (1137169 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7539564800
    (h : (((753781310703421 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539302656) :
    (((753807360970873 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539564800 := by
  exact
    theta_restart_gain 7539302656 7539564800 15 11454 33 (753781310703421 / 100000)
      (753807360970873 / 100000) (1137169 / 50000) (2274341 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7539826944
    (h : (((753807360970873 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539564800) :
    (((753833554567687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539826944 := by
  exact
    theta_restart_gain 7539564800 7539826944 15 11517 33 (753807360970873 / 100000)
      (753833554567687 / 100000) (1137171 / 50000) (454869 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7540089088
    (h : (((753833554567687 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7539826944) :
    (((376929844533041 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540089088 := by
  exact
    theta_restart_gain 7539826944 7540089088 15 11491 33 (753833554567687 / 100000)
      (376929844533041 / 50000) (454869 / 20000) (568587 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7540351232
    (h : (((376929844533041 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540089088) :
    (((75388585771417 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540351232 := by
  exact
    theta_restart_gain 7540089088 7540351232 15 11506 33 (376929844533041 / 50000)
      (75388585771417 / 10000) (568587 / 25000) (2274351 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7540613376
    (h : (((75388585771417 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540351232) :
    (((376955957482517 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540613376 := by
  exact
    theta_restart_gain 7540351232 7540613376 15 11457 33 (75388585771417 / 10000)
      (376955957482517 / 50000) (142147 / 6250) (454871 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7540875520
    (h : (((376955957482517 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540613376) :
    (((753937881276069 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540875520 := by
  exact
    theta_restart_gain 7540613376 7540875520 15 11417 33 (376955957482517 / 50000)
      (753937881276069 / 100000) (454871 / 20000) (1137179 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7541137664
    (h : (((753937881276069 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7540875520) :
    (((753963936332773 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541137664 := by
  exact
    theta_restart_gain 7540875520 7541137664 15 11456 33 (753937881276069 / 100000)
      (753963936332773 / 100000) (2274359 / 100000) (1137181 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7541399808
    (h : (((753963936332773 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541137664) :
    (((753990398534643 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541399808 := by
  exact
    theta_restart_gain 7541137664 7541399808 15 11635 33 (753963936332773 / 100000)
      (753990398534643 / 100000) (1137181 / 50000) (454873 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7541661952
    (h : (((753990398534643 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541399808) :
    (((754016424104781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541661952 := by
  exact
    theta_restart_gain 7541399808 7541661952 15 11443 33 (753990398534643 / 100000)
      (754016424104781 / 100000) (1137183 / 50000) (2274369 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7541924096
    (h : (((754016424104781 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7541661952) :
    (((9425531985987 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7541924096 := by
  exact
    theta_restart_gain 7541661952 7541924096 15 11491 33 (754016424104781 / 100000)
      (9425531985987 / 1250) (2274369 / 100000) (568593 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7542186240
    (h : (((9425531985987 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7541924096) :
    (((754068821063991 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542186240 := by
  exact
    theta_restart_gain 7541924096 7542186240 15 11547 33 (9425531985987 / 1250)
      (754068821063991 / 100000) (2274373 / 100000) (284297 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7542448384
    (h : (((754068821063991 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542186240) :
    (((754094919528591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542448384 := by
  exact
    theta_restart_gain 7542186240 7542448384 15 11475 33 (754068821063991 / 100000)
      (754094919528591 / 100000) (284297 / 12500) (2274379 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7542710528
    (h : (((754094919528591 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542448384) :
    (((754121163599411 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542710528 := by
  exact
    theta_restart_gain 7542448384 7542710528 15 11539 33 (754094919528591 / 100000)
      (754121163599411 / 100000) (113719 / 5000) (2274383 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7542972672
    (h : (((754121163599411 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542710528) :
    (((754147209833527 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542972672 := by
  exact
    theta_restart_gain 7542710528 7542972672 15 11452 33 (754121163599411 / 100000)
      (754147209833527 / 100000) (2274383 / 100000) (1137193 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7543234816
    (h : (((754147209833527 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7542972672) :
    (((754173538137439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543234816 := by
  exact
    theta_restart_gain 7542972672 7543234816 15 11576 33 (754147209833527 / 100000)
      (754173538137439 / 100000) (2274387 / 100000) (227439 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7543496960
    (h : (((754173538137439 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543234816) :
    (((754199645860249 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543496960 := by
  exact
    theta_restart_gain 7543234816 7543496960 15 11479 33 (754173538137439 / 100000)
      (754199645860249 / 100000) (227439 / 10000) (2274393 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7543759104
    (h : (((754199645860249 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543496960) :
    (((754225739982611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543759104 := by
  exact
    theta_restart_gain 7543496960 7543759104 15 11473 33 (754199645860249 / 100000)
      (754225739982611 / 100000) (1137197 / 50000) (2274397 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7544021248
    (h : (((754225739982611 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7543759104) :
    (((754251931938463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544021248 := by
  exact
    theta_restart_gain 7543759104 7544021248 15 11516 33 (754225739982611 / 100000)
      (754251931938463 / 100000) (2274397 / 100000) (2843 / 125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7544283392
    (h : (((754251931938463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544021248) :
    (((150855595675743 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544283392 := by
  exact
    theta_restart_gain 7544021248 7544283392 15 11452 33 (754251931938463 / 100000)
      (150855595675743 / 20000) (2274401 / 100000) (568601 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7544545536
    (h : (((150855595675743 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544283392) :
    (((754304534319819 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544545536 := by
  exact
    theta_restart_gain 7544283392 7544545536 15 11676 33 (150855595675743 / 20000)
      (754304534319819 / 100000) (568601 / 25000) (2274407 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7544807680
    (h : (((754304534319819 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544545536) :
    (((754330699109451 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544807680 := by
  exact
    theta_restart_gain 7544545536 7544807680 15 11504 33 (754304534319819 / 100000)
      (754330699109451 / 100000) (284301 / 12500) (2274411 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7545069824
    (h : (((754330699109451 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7544807680) :
    (((754356895775349 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545069824 := by
  exact
    theta_restart_gain 7544807680 7545069824 15 11518 33 (754330699109451 / 100000)
      (754356895775349 / 100000) (2274411 / 100000) (1137207 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7545331968
    (h : (((754356895775349 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545069824) :
    (((377191620162147 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545331968 := by
  exact
    theta_restart_gain 7545069824 7545331968 15 11583 33 (754356895775349 / 100000)
      (377191620162147 / 50000) (454883 / 20000) (1137209 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7545594112
    (h : (((377191620162147 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545331968) :
    (((94301214603029 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7545594112 := by
  exact
    theta_restart_gain 7545331968 7545594112 15 11641 33 (377191620162147 / 50000)
      (94301214603029 / 12500) (1137209 / 50000) (2274421 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7545856256
    (h : (((94301214603029 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7545594112) :
    (((754436056893833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545856256 := by
  exact
    theta_restart_gain 7545594112 7545856256 15 11581 33 (94301214603029 / 12500)
      (754436056893833 / 100000) (2274421 / 100000) (284303 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7546118400
    (h : (((754436056893833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7545856256) :
    (((754462453870383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546118400 := by
  exact
    theta_restart_gain 7545856256 7546118400 15 11606 33 (754436056893833 / 100000)
      (754462453870383 / 100000) (90977 / 4000) (568607 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7546380544
    (h : (((754462453870383 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546118400) :
    (((754488509717551 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546380544 := by
  exact
    theta_restart_gain 7546118400 7546380544 15 11456 33 (754462453870383 / 100000)
      (754488509717551 / 100000) (568607 / 25000) (2274431 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7546642688
    (h : (((754488509717551 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546380544) :
    (((754514743016239 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546642688 := by
  exact
    theta_restart_gain 7546380544 7546642688 15 11534 33 (754488509717551 / 100000)
      (754514743016239 / 100000) (71076 / 3125) (454887 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7546904832
    (h : (((754514743016239 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7546642688) :
    (((23579410983782 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7546904832 := by
  exact
    theta_restart_gain 7546642688 7546904832 15 11611 33 (754514743016239 / 100000)
      (23579410983782 / 3125) (454887 / 20000) (1137219 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7547166976
    (h : (((23579410983782 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7546904832) :
    (((94320889559581 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547166976 := by
  exact
    theta_restart_gain 7546904832 7547166976 15 11416 33 (23579410983782 / 3125)
      (94320889559581 / 12500) (2274439 / 100000) (1137221 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7547429120
    (h : (((94320889559581 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547166976) :
    (((377296576007111 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7547429120 := by
  exact
    theta_restart_gain 7547166976 7547429120 15 11447 33 (94320889559581 / 12500)
      (377296576007111 / 50000) (1137221 / 50000) (454889 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7547691264
    (h : (((377296576007111 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7547429120) :
    (((94327395038029 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547691264 := by
  exact
    theta_restart_gain 7547429120 7547691264 15 11435 33 (377296576007111 / 50000)
      (94327395038029 / 12500) (1137223 / 50000) (2274449 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7547953408
    (h : (((94327395038029 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547691264) :
    (((94330665695691 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547953408 := by
  exact
    theta_restart_gain 7547691264 7547953408 15 11504 33 (94327395038029 / 12500)
      (94330665695691 / 12500) (2274449 / 100000) (568613 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7548215552
    (h : (((94330665695691 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7547953408) :
    (((188667865894851 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548215552 := by
  exact
    theta_restart_gain 7547953408 7548215552 15 11492 33 (94330665695691 / 12500)
      (188667865894851 / 25000) (2274453 / 100000) (284307 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7548477696
    (h : (((188667865894851 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548215552) :
    (((188674427700411 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548477696 := by
  exact
    theta_restart_gain 7548215552 7548477696 15 11540 33 (188667865894851 / 25000)
      (188674427700411 / 25000) (284307 / 12500) (2274459 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7548739840
    (h : (((188674427700411 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548477696) :
    (((188680989517511 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548739840 := by
  exact
    theta_restart_gain 7548477696 7548739840 15 11540 33 (188674427700411 / 25000)
      (188680989517511 / 25000) (113723 / 5000) (2274463 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7549001984
    (h : (((188680989517511 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7548739840) :
    (((754750257685713 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7549001984 := by
  exact
    theta_restart_gain 7548739840 7549001984 15 11563 33 (188680989517511 / 25000)
      (754750257685713 / 100000) (2274463 / 100000) (1137233 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7549264128
    (h : (((754750257685713 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7549001984) :
    (((188694081338 / 25) : ℚ) : ℝ) ≤ Chebyshev.theta 7549264128 := by
  exact
    theta_restart_gain 7549001984 7549264128 15 11461 33 (754750257685713 / 100000)
      (188694081338 / 25) (2274467 / 100000) (227447 / 10000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7549526272 (h : (((188694081338 / 25) : ℚ) : ℝ) ≤ Chebyshev.theta 7549264128) :
    (((18870062498819 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7549526272 := by
  exact
    theta_restart_gain 7549264128 7549526272 15 11508 33 (188694081338 / 25) (18870062498819 / 2500)
      (227447 / 10000) (2274473 / 100000) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7549788416
    (h : (((18870062498819 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7549526272) :
    (((188707213002131 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7549788416 := by
  exact
    theta_restart_gain 7549526272 7549788416 15 11586 33 (18870062498819 / 2500)
      (188707213002131 / 25000) (1137237 / 50000) (2274477 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7550050560
    (h : (((188707213002131 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7549788416) :
    (((75485514041369 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550050560 := by
  exact
    theta_restart_gain 7549788416 7550050560 15 11558 33 (188707213002131 / 25000)
      (75485514041369 / 10000) (2274477 / 100000) (28431 / 1250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7550312704
    (h : (((75485514041369 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550050560) :
    (((188720345843867 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550312704 := by
  exact
    theta_restart_gain 7550050560 7550312704 15 11538 33 (75485514041369 / 10000)
      (188720345843867 / 25000) (2274481 / 100000) (568621 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7550574848
    (h : (((188720345843867 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550312704) :
    (((188726797417733 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550574848 := by
  exact
    theta_restart_gain 7550312704 7550574848 15 11346 33 (188720345843867 / 25000)
      (188726797417733 / 25000) (568621 / 25000) (2274487 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7550836992
    (h : (((188726797417733 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7550574848) :
    (((94366668283929 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7550836992 := by
  exact
    theta_restart_gain 7550574848 7550836992 15 11500 33 (188726797417733 / 25000)
      (94366668283929 / 12500) (2274487 / 100000) (227449 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7551099136
    (h : (((94366668283929 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7550836992) :
    (((75495940738931 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551099136 := by
  exact
    theta_restart_gain 7550836992 7551099136 15 11458 33 (94366668283929 / 12500)
      (75495940738931 / 10000) (2274491 / 100000) (1137247 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7551361280
    (h : (((75495940738931 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551099136) :
    (((377492786584143 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551361280 := by
  exact
    theta_restart_gain 7551099136 7551361280 15 11504 33 (75495940738931 / 10000)
      (377492786584143 / 50000) (1137247 / 50000) (2274497 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7551623424
    (h : (((377492786584143 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551361280) :
    (((94376482442709 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7551623424 := by
  exact
    theta_restart_gain 7551361280 7551623424 15 11557 33 (377492786584143 / 50000)
      (94376482442709 / 12500) (1137249 / 50000) (2274501 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7551885568
    (h : (((94376482442709 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7551623424) :
    (((377518946740059 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551885568 := by
  exact
    theta_restart_gain 7551623424 7551885568 15 11446 33 (94376482442709 / 12500)
      (377518946740059 / 50000) (2274501 / 100000) (284313 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7552147712
    (h : (((377518946740059 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7551885568) :
    (((94383007991831 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7552147712 := by
  exact
    theta_restart_gain 7551885568 7552147712 15 11506 33 (377518946740059 / 50000)
      (94383007991831 / 12500) (454901 / 20000) (568627 / 25000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7552409856
    (h : (((94383007991831 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7552147712) :
    (((188772630821553 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552409856 := by
  exact
    theta_restart_gain 7552147712 7552409856 15 11633 33 (94383007991831 / 12500)
      (188772630821553 / 25000) (568627 / 25000) (2274511 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7552672000
    (h : (((188772630821553 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552409856) :
    (((37755829345961 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552672000 := by
  exact
    theta_restart_gain 7552409856 7552672000 15 11459 33 (188772630821553 / 25000)
      (37755829345961 / 5000) (142157 / 6250) (454903 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7552934144
    (h : (((37755829345961 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552672000) :
    (((75514317599957 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552934144 := by
  exact
    theta_restart_gain 7552672000 7552934144 15 11690 33 (37755829345961 / 5000)
      (75514317599957 / 10000) (454903 / 20000) (1137259 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7553196288
    (h : (((75514317599957 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7552934144) :
    (((30206777412857 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553196288 := by
  exact
    theta_restart_gain 7552934144 7553196288 15 11545 33 (75514317599957 / 10000)
      (30206777412857 / 4000) (2274519 / 100000) (1137261 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7553458432
    (h : (((30206777412857 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553196288) :
    (((755195442205973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553458432 := by
  exact
    theta_restart_gain 7553196288 7553458432 15 11434 33 (30206777412857 / 4000)
      (755195442205973 / 100000) (1137261 / 50000) (90981 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7553720576
    (h : (((755195442205973 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553458432) :
    (((755221747099163 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553720576 := by
  exact
    theta_restart_gain 7553458432 7553720576 15 11565 33 (755195442205973 / 100000)
      (755221747099163 / 100000) (1137263 / 50000) (2274529 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7553982720
    (h : (((755221747099163 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553720576) :
    (((188812056222813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553982720 := by
  exact
    theta_restart_gain 7553720576 7553982720 15 11641 33 (755221747099163 / 100000)
      (188812056222813 / 25000) (2274529 / 100000) (568633 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7554244864
    (h : (((188812056222813 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7553982720) :
    (((755274411589681 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554244864 := by
  exact
    theta_restart_gain 7553982720 7554244864 15 11513 33 (188812056222813 / 25000)
      (755274411589681 / 100000) (2274533 / 100000) (284317 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7554507008
    (h : (((755274411589681 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554244864) :
    (((755300477772241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554507008 := by
  exact
    theta_restart_gain 7554244864 7554507008 15 11460 33 (755274411589681 / 100000)
      (755300477772241 / 100000) (284317 / 12500) (2274539 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7554769152
    (h : (((755300477772241 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554507008) :
    (((755326707767521 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554769152 := by
  exact
    theta_restart_gain 7554507008 7554769152 15 11532 33 (755300477772241 / 100000)
      (755326707767521 / 100000) (113727 / 5000) (2274543 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7555031296
    (h : (((755326707767521 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7554769152) :
    (((755352887757451 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555031296 := by
  exact
    theta_restart_gain 7554769152 7555031296 15 11510 33 (755326707767521 / 100000)
      (755352887757451 / 100000) (2274543 / 100000) (1137273 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7555293440
    (h : (((755352887757451 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555031296) :
    (((755379436258363 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555293440 := by
  exact
    theta_restart_gain 7555031296 7555293440 15 11672 33 (755352887757451 / 100000)
      (755379436258363 / 100000) (1137273 / 50000) (2274549 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7555555584
    (h : (((755379436258363 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555293440) :
    (((755405609505213 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555555584 := by
  exact
    theta_restart_gain 7555293440 7555555584 15 11507 33 (755379436258363 / 100000)
      (755405609505213 / 100000) (45491 / 2000) (2274553 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7555817728
    (h : (((755405609505213 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555555584) :
    (((377715934609799 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555817728 := by
  exact
    theta_restart_gain 7555555584 7555817728 15 11545 33 (755405609505213 / 100000)
      (377715934609799 / 50000) (2274553 / 100000) (568639 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7556079872
    (h : (((377715934609799 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7555817728) :
    (((755458420123459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556079872 := by
  exact
    theta_restart_gain 7555817728 7556079872 15 11673 33 (377715934609799 / 50000)
      (755458420123459 / 100000) (2274557 / 100000) (14216 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7556342016
    (h : (((755458420123459 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556079872) :
    (((755484636702019 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556342016 := by
  exact
    theta_restart_gain 7556079872 7556342016 15 11526 33 (755458420123459 / 100000)
      (755484636702019 / 100000) (14216 / 625) (2274563 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7556604160
    (h : (((755484636702019 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556342016) :
    (((755510832855607 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556604160 := by
  exact
    theta_restart_gain 7556342016 7556604160 15 11517 33 (755484636702019 / 100000)
      (755510832855607 / 100000) (568641 / 25000) (2274567 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7556866304
    (h : (((755510832855607 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556604160) :
    (((151107395345741 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556866304 := by
  exact
    theta_restart_gain 7556604160 7556866304 15 11494 33 (755510832855607 / 100000)
      (151107395345741 / 20000) (2274567 / 100000) (227457 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7557128448
    (h : (((151107395345741 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7556866304) :
    (((75556298644809 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7557128448 := by
  exact
    theta_restart_gain 7556866304 7557128448 15 11435 33 (151107395345741 / 20000)
      (75556298644809 / 10000) (2274571 / 100000) (1137287 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7557390592
    (h : (((75556298644809 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7557128448) :
    (((188897315013091 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7557390592 := by
  exact
    theta_restart_gain 7557128448 7557390592 15 11551 33 (75556298644809 / 10000)
      (188897315013091 / 25000) (1137287 / 50000) (2274577 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7557652736
    (h : (((188897315013091 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7557390592) :
    (((23612990759256 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7557652736 := by
  exact
    theta_restart_gain 7557390592 7557652736 15 11626 33 (188897315013091 / 25000)
      (23612990759256 / 3125) (1137289 / 50000) (2274581 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7557914880
    (h : (((23612990759256 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7557652736) :
    (((23613809608416 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7557914880 := by
  exact
    theta_restart_gain 7557652736 7557914880 15 11520 33 (23612990759256 / 3125)
      (23613809608416 / 3125) (2274581 / 100000) (284323 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7558177024
    (h : (((23613809608416 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7557914880) :
    (((755668053823887 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558177024 := by
  exact
    theta_restart_gain 7557914880 7558177024 15 11495 33 (23613809608416 / 3125)
      (755668053823887 / 100000) (454917 / 20000) (568647 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7558439168
    (h : (((755668053823887 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558177024) :
    (((755694211585887 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558439168 := by
  exact
    theta_restart_gain 7558177024 7558439168 15 11500 33 (755668053823887 / 100000)
      (755694211585887 / 100000) (568647 / 25000) (2274591 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7558701312
    (h : (((755694211585887 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558439168) :
    (((151144123464883 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558701312 := by
  exact
    theta_restart_gain 7558439168 7558701312 15 11609 33 (755694211585887 / 100000)
      (151144123464883 / 20000) (71081 / 3125) (454919 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7558963456
    (h : (((151144123464883 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558701312) :
    (((30229878103413 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558963456 := by
  exact
    theta_restart_gain 7558701312 7558963456 15 11578 33 (151144123464883 / 20000)
      (30229878103413 / 4000) (454919 / 20000) (1137299 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7559225600
    (h : (((30229878103413 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7558963456) :
    (((755773130933707 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559225600 := by
  exact
    theta_restart_gain 7558963456 7559225600 15 11509 33 (30229878103413 / 4000)
      (755773130933707 / 100000) (1137299 / 50000) (2274601 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7559487744
    (h : (((755773130933707 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559225600) :
    (((755799068220313 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559487744 := by
  exact
    theta_restart_gain 7559225600 7559487744 15 11403 33 (755773130933707 / 100000)
      (755799068220313 / 100000) (1137301 / 50000) (454921 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7559749888
    (h : (((755799068220313 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559487744) :
    (((188956349193297 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559749888 := by
  exact
    theta_restart_gain 7559487744 7559749888 15 11575 33 (755799068220313 / 100000)
      (188956349193297 / 25000) (454921 / 20000) (142163 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7560012032
    (h : (((188956349193297 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7559749888) :
    (((188962872771909 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7560012032 := by
  exact
    theta_restart_gain 7559749888 7560012032 15 11472 33 (188956349193297 / 25000)
      (188962872771909 / 25000) (2274609 / 100000) (568653 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7560274176
    (h : (((188962872771909 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7560012032) :
    (((94484734857681 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7560274176 := by
  exact
    theta_restart_gain 7560012032 7560274176 15 11601 33 (188962872771909 / 25000)
      (94484734857681 / 12500) (568653 / 25000) (454923 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7560536320
    (h : (((94484734857681 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7560274176) :
    (((47243987381923 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7560536320 := by
  exact
    theta_restart_gain 7560274176 7560536320 15 11395 33 (94484734857681 / 12500)
      (47243987381923 / 6250) (284327 / 12500) (2274619 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7560798464
    (h : (((47243987381923 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7560536320) :
    (((30237207620601 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7560798464 := by
  exact
    theta_restart_gain 7560536320 7560798464 15 11603 33 (47243987381923 / 6250)
      (30237207620601 / 4000) (2274619 / 100000) (1137311 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7561060608
    (h : (((30237207620601 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7560798464) :
    (((755956239497621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561060608 := by
  exact
    theta_restart_gain 7560798464 7561060608 15 11452 33 (30237207620601 / 4000)
      (755956239497621 / 100000) (2274623 / 100000) (1137313 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7561322752
    (h : (((755956239497621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561060608) :
    (((755982311260833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561322752 := by
  exact
    theta_restart_gain 7561060608 7561322752 15 11462 33 (755956239497621 / 100000)
      (755982311260833 / 100000) (1137313 / 50000) (2274629 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7561584896
    (h : (((755982311260833 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561322752) :
    (((756008453583423 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561584896 := by
  exact
    theta_restart_gain 7561322752 7561584896 15 11493 33 (755982311260833 / 100000)
      (756008453583423 / 100000) (227463 / 10000) (2274633 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7561847040
    (h : (((756008453583423 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561584896) :
    (((189008694477783 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561847040 := by
  exact
    theta_restart_gain 7561584896 7561847040 15 11573 33 (756008453583423 / 100000)
      (189008694477783 / 25000) (2274633 / 100000) (568659 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562109184
    (h : (((189008694477783 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7561847040) :
    (((756061015848927 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562109184 := by
  exact
    theta_restart_gain 7561847040 7562109184 15 11535 33 (189008694477783 / 25000)
      (756061015848927 / 100000) (2274637 / 100000) (28433 / 1250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562371328
    (h : (((756061015848927 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562109184) :
    (((756087358454767 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562371328 := by
  exact
    theta_restart_gain 7562109184 7562371328 15 11581 33 (756061015848927 / 100000)
      (756087358454767 / 100000) (28433 / 1250) (2274643 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562387712
    (h : (((756087358454767 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562371328) :
    (((756088991649159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562387712 := by
  exact
    theta_restart_gain 7562371328 7562387712 11 718 33 (756087358454767 / 100000)
      (756088991649159 / 100000) (568661 / 25000) (2274647 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7562389760
    (h : (((756088991649159 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562387712) :
    (((756089196367119 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562389760 := by
  exact
    theta_restart_gain 7562387712 7562389760 8 90 33 (756088991649159 / 100000)
      (756089196367119 / 100000) (568661 / 25000) (2274647 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7562389760
    (h : (((752889887289463 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7530389760) :
    (((756089196367119 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7562389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7562389760 point7562387712)
                  (Function.comp point7562371328 point7562109184))
                (Function.comp (Function.comp point7561847040 point7561584896)
                  (Function.comp point7561322752 point7561060608)))
              (Function.comp
                (Function.comp (Function.comp point7560798464 point7560536320)
                  (Function.comp point7560274176 point7560012032))
                (Function.comp (Function.comp point7559749888 point7559487744)
                  (Function.comp point7559225600 point7558963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7558701312 point7558439168)
                  (Function.comp point7558177024 point7557914880))
                (Function.comp (Function.comp point7557652736 point7557390592)
                  (Function.comp point7557128448 point7556866304)))
              (Function.comp
                (Function.comp (Function.comp point7556604160 point7556342016)
                  (Function.comp point7556079872 point7555817728))
                (Function.comp (Function.comp point7555555584 point7555293440)
                  (Function.comp point7555031296 point7554769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7554507008 point7554244864)
                  (Function.comp point7553982720 point7553720576))
                (Function.comp (Function.comp point7553458432 point7553196288)
                  (Function.comp point7552934144 point7552672000)))
              (Function.comp
                (Function.comp (Function.comp point7552409856 point7552147712)
                  (Function.comp point7551885568 point7551623424))
                (Function.comp (Function.comp point7551361280 point7551099136)
                  (Function.comp point7550836992 point7550574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7550312704 point7550050560)
                  (Function.comp point7549788416 point7549526272))
                (Function.comp (Function.comp point7549264128 point7549001984)
                  (Function.comp point7548739840 point7548477696)))
              (Function.comp
                (Function.comp (Function.comp point7548215552 point7547953408)
                  (Function.comp point7547691264 point7547429120))
                (Function.comp (Function.comp point7547166976 point7546904832)
                  (Function.comp point7546642688 point7546380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7546118400 point7545856256)
                  (Function.comp point7545594112 point7545331968))
                (Function.comp (Function.comp point7545069824 point7544807680)
                  (Function.comp point7544545536 point7544283392)))
              (Function.comp
                (Function.comp (Function.comp point7544021248 point7543759104)
                  (Function.comp point7543496960 point7543234816))
                (Function.comp (Function.comp point7542972672 point7542710528)
                  (Function.comp point7542448384 point7542186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7541924096 point7541661952)
                  (Function.comp point7541399808 point7541137664))
                (Function.comp (Function.comp point7540875520 point7540613376)
                  (Function.comp point7540351232 point7540089088)))
              (Function.comp
                (Function.comp (Function.comp point7539826944 point7539564800)
                  (Function.comp point7539302656 point7539040512))
                (Function.comp (Function.comp point7538778368 point7538516224)
                  (Function.comp point7538254080 point7537991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7537729792 point7537467648)
                  (Function.comp point7537205504 point7536943360))
                (Function.comp (Function.comp point7536681216 point7536419072)
                  (Function.comp point7536156928 point7535894784)))
              (Function.comp
                (Function.comp (Function.comp point7535632640 point7535370496)
                  (Function.comp point7535108352 point7534846208))
                (Function.comp (Function.comp point7534584064 point7534321920)
                  (Function.comp point7534059776 point7533797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7533535488 point7533273344)
                  (Function.comp point7533011200 point7532749056))
                (Function.comp (Function.comp point7532486912 point7532224768)
                  (Function.comp point7531962624 point7531700480)))
              (Function.comp (Function.comp point7531438336 point7531176192)
                (Function.comp point7530914048 point7530651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
