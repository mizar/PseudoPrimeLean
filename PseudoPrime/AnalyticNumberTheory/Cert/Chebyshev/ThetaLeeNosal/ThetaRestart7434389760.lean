/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartGain
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Scalar restart transfer up to 7434389760 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7402651904 (h : ((7400892300 : ℚ) : ℝ) ≤ Chebyshev.theta 7402389760) :
    (((148023142300153 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7402651904 := by
  exact
    theta_restart_gain 7402389760 7402651904 15 11653 33 7400892300 (148023142300153 / 20000)
      (454501 / 20000) (568127 / 25000) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7402914048
    (h : (((148023142300153 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7402651904) :
    (((370070946538477 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7402914048 := by
  exact
    theta_restart_gain 7402651904 7402914048 15 11521 33 (148023142300153 / 20000)
      (370070946538477 / 50000) (2272509 / 100000) (71016 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7403176192
    (h : (((370070946538477 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7402914048) :
    (((370084021436269 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403176192 := by
  exact
    theta_restart_gain 7402914048 7403176192 15 11507 33 (370070946538477 / 50000)
      (370084021436269 / 50000) (71016 / 3125) (454503 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7403438336
    (h : (((370084021436269 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403176192) :
    (((370097027045337 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403438336 := by
  exact
    theta_restart_gain 7403176192 7403438336 15 11446 33 (370084021436269 / 50000)
      (370097027045337 / 50000) (568129 / 25000) (2272519 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7403700480
    (h : (((370097027045337 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403438336) :
    (((370110079263957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403700480 := by
  exact
    theta_restart_gain 7403438336 7403700480 15 11487 33 (370097027045337 / 50000)
      (370110079263957 / 50000) (56813 / 2500) (2272523 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7403962624
    (h : (((370110079263957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7403700480) :
    (((740246251637 / 100) : ℚ) : ℝ) ≤ Chebyshev.theta 7403962624 := by
  exact
    theta_restart_gain 7403700480 7403962624 15 11482 33 (370110079263957 / 50000)
      (740246251637 / 100) (2272523 / 100000) (1136263 / 50000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7404224768
    (h : (((740246251637 / 100) : ℚ) : ℝ) ≤ Chebyshev.theta 7403962624) :
    (((740272492506269 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404224768 := by
  exact
    theta_restart_gain 7403962624 7404224768 15 11547 33 (740246251637 / 100)
      (740272492506269 / 100000) (2272527 / 100000) (227253 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7404486912
    (h : (((740272492506269 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404224768) :
    (((740298587968259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404486912 := by
  exact
    theta_restart_gain 7404224768 7404486912 15 11483 33 (740272492506269 / 100000)
      (740298587968259 / 100000) (227253 / 10000) (2272533 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7404749056
    (h : (((740298587968259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404486912) :
    (((740324908457047 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404749056 := by
  exact
    theta_restart_gain 7404486912 7404749056 15 11582 33 (740298587968259 / 100000)
      (740324908457047 / 100000) (1136267 / 50000) (2272537 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7405011200
    (h : (((740324908457047 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7404749056) :
    (((148070246705131 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405011200 := by
  exact
    theta_restart_gain 7404749056 7405011200 15 11584 33 (740324908457047 / 100000)
      (148070246705131 / 20000) (2272537 / 100000) (113627 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7405273344
    (h : (((148070246705131 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405011200) :
    (((185094394773367 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405273344 := by
  exact
    theta_restart_gain 7405011200 7405273344 15 11593 33 (148070246705131 / 20000)
      (185094394773367 / 25000) (2272541 / 100000) (71017 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7405535488
    (h : (((185094394773367 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405273344) :
    (((185100922087871 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405535488 := by
  exact
    theta_restart_gain 7405273344 7405535488 15 11489 33 (185094394773367 / 25000)
      (185100922087871 / 25000) (71017 / 3125) (2272547 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7405797632
    (h : (((185100922087871 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405535488) :
    (((185107452254549 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405797632 := by
  exact
    theta_restart_gain 7405535488 7405797632 15 11494 33 (185100922087871 / 25000)
      (185107452254549 / 25000) (568137 / 25000) (2272551 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7406059776
    (h : (((185107452254549 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7405797632) :
    (((740455863815411 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406059776 := by
  exact
    theta_restart_gain 7405797632 7406059776 15 11465 33 (185107452254549 / 25000)
      (740455863815411 / 100000) (2272551 / 100000) (1136277 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7406321920
    (h : (((740455863815411 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406059776) :
    (((740482134551211 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406321920 := by
  exact
    theta_restart_gain 7406059776 7406321920 15 11560 33 (740455863815411 / 100000)
      (740482134551211 / 100000) (454511 / 20000) (1136279 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7406584064
    (h : (((740482134551211 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406321920) :
    (((740508598489121 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406584064 := by
  exact
    theta_restart_gain 7406321920 7406584064 15 11645 33 (740482134551211 / 100000)
      (740508598489121 / 100000) (1136279 / 50000) (2272561 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7406846208
    (h : (((740508598489121 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7406584064) :
    (((5924277718173 / 800) : ℚ) : ℝ) ≤ Chebyshev.theta 7406846208 := by
  exact
    theta_restart_gain 7406584064 7406846208 15 11492 33 (740508598489121 / 100000)
      (5924277718173 / 800) (1136281 / 50000) (454513 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7407108352
    (h : (((5924277718173 / 800) : ℚ) : ℝ) ≤ Chebyshev.theta 7406846208) :
    (((740560901549643 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7407108352 := by
  exact
    theta_restart_gain 7406846208 7407108352 15 11523 33 (5924277718173 / 800)
      (740560901549643 / 100000) (1136283 / 50000) (2272569 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7407370496
    (h : (((740560901549643 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7407108352) :
    (((92573372978007 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407370496 := by
  exact
    theta_restart_gain 7407108352 7407370496 15 11477 33 (740560901549643 / 100000)
      (92573372978007 / 12500) (2272569 / 100000) (568143 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7407632640
    (h : (((92573372978007 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407370496) :
    (((92576663663711 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407632640 := by
  exact
    theta_restart_gain 7407370496 7407632640 15 11584 33 (92573372978007 / 12500)
      (92576663663711 / 12500) (2272573 / 100000) (71018 / 3125) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7407894784
    (h : (((92576663663711 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407632640) :
    (((92579955490047 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407894784 := by
  exact
    theta_restart_gain 7407632640 7407894784 15 11588 33 (92576663663711 / 12500)
      (92579955490047 / 12500) (71018 / 3125) (2272579 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7408156928
    (h : (((92579955490047 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7407894784) :
    (((185166509984269 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408156928 := by
  exact
    theta_restart_gain 7407894784 7408156928 15 11615 33 (92579955490047 / 12500)
      (185166509984269 / 25000) (113629 / 5000) (2272583 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7408419072
    (h : (((185166509984269 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408156928) :
    (((74069244280637 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408419072 := by
  exact
    theta_restart_gain 7408156928 7408419072 15 11618 33 (185166509984269 / 25000)
      (74069244280637 / 10000) (2272583 / 100000) (1136293 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7408681216
    (h : (((74069244280637 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408419072) :
    (((740718707094329 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408681216 := by
  exact
    theta_restart_gain 7408419072 7408681216 15 11557 33 (74069244280637 / 10000)
      (740718707094329 / 100000) (2272587 / 100000) (227259 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7408943360
    (h : (((740718707094329 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408681216) :
    (((740744889603719 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408943360 := by
  exact
    theta_restart_gain 7408681216 7408943360 15 11521 33 (740718707094329 / 100000)
      (740744889603719 / 100000) (227259 / 10000) (2272593 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7409205504
    (h : (((740744889603719 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7408943360) :
    (((29630838613891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409205504 := by
  exact
    theta_restart_gain 7408943360 7409205504 15 11474 33 (740744889603719 / 100000)
      (29630838613891 / 4000) (1136297 / 50000) (2272597 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7409467648
    (h : (((29630838613891 / 4000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409205504) :
    (((740797341108057 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409467648 := by
  exact
    theta_restart_gain 7409205504 7409467648 15 11606 33 (29630838613891 / 4000)
      (740797341108057 / 100000) (2272597 / 100000) (11363 / 500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7409729792
    (h : (((740797341108057 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409467648) :
    (((740823735096071 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409729792 := by
  exact
    theta_restart_gain 7409467648 7409729792 15 11614 33 (740797341108057 / 100000)
      (740823735096071 / 100000) (2272601 / 100000) (568151 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7409991936
    (h : (((740823735096071 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409729792) :
    (((740850222295691 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409991936 := by
  exact
    theta_restart_gain 7409729792 7409991936 15 11655 33 (740823735096071 / 100000)
      (740850222295691 / 100000) (568151 / 25000) (2272607 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7410254080
    (h : (((740850222295691 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7409991936) :
    (((740876555004587 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410254080 := by
  exact
    theta_restart_gain 7409991936 7410254080 15 11587 33 (740850222295691 / 100000)
      (740876555004587 / 100000) (71019 / 3125) (2272611 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7410516224
    (h : (((740876555004587 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410254080) :
    (((740902705950871 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410516224 := by
  exact
    theta_restart_gain 7410254080 7410516224 15 11507 33 (740876555004587 / 100000)
      (740902705950871 / 100000) (568153 / 25000) (454523 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7410778368
    (h : (((740902705950871 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410516224) :
    (((740928727392621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410778368 := by
  exact
    theta_restart_gain 7410516224 7410778368 15 11450 33 (740902705950871 / 100000)
      (740928727392621 / 100000) (454523 / 20000) (1136309 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7411040512
    (h : (((740928727392621 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7410778368) :
    (((740954885237311 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411040512 := by
  exact
    theta_restart_gain 7410778368 7411040512 15 11510 33 (740928727392621 / 100000)
      (740954885237311 / 100000) (2272619 / 100000) (1136311 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7411302656
    (h : (((740954885237311 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411040512) :
    (((740981022662933 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411302656 := by
  exact
    theta_restart_gain 7411040512 7411302656 15 11501 33 (740954885237311 / 100000)
      (740981022662933 / 100000) (1136311 / 50000) (18181 / 800) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7411564800
    (h : (((740981022662933 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411302656) :
    (((148201425663559 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411564800 := by
  exact
    theta_restart_gain 7411302656 7411564800 15 11487 33 (740981022662933 / 100000)
      (148201425663559 / 20000) (1136313 / 50000) (2272629 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7411826944
    (h : (((148201425663559 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411564800) :
    (((741033522631001 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411826944 := by
  exact
    theta_restart_gain 7411564800 7411826944 15 11614 33 (148201425663559 / 20000)
      (741033522631001 / 100000) (2272629 / 100000) (284079 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7412089088
    (h : (((741033522631001 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7411826944) :
    (((74105973290739 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412089088 := by
  exact
    theta_restart_gain 7411826944 7412089088 15 11533 33 (741033522631001 / 100000)
      (74105973290739 / 10000) (2272633 / 100000) (568159 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7412351232
    (h : (((74105973290739 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412089088) :
    (((74108590231093 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412351232 := by
  exact
    theta_restart_gain 7412089088 7412351232 15 11515 33 (74105973290739 / 10000)
      (74108590231093 / 10000) (568159 / 25000) (2272639 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7412613376
    (h : (((74108590231093 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412351232) :
    (((74111225584437 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412613376 := by
  exact
    theta_restart_gain 7412351232 7412613376 15 11596 33 (74108590231093 / 10000)
      (74111225584437 / 10000) (14204 / 625) (2272643 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7412875520
    (h : (((74111225584437 / 10000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412613376) :
    (((741138529870093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412875520 := by
  exact
    theta_restart_gain 7412613376 7412875520 15 11561 33 (74111225584437 / 10000)
      (741138529870093 / 100000) (2272643 / 100000) (1136323 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7413137664
    (h : (((741138529870093 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7412875520) :
    (((741164651674711 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413137664 := by
  exact
    theta_restart_gain 7412875520 7413137664 15 11494 33 (741138529870093 / 100000)
      (741164651674711 / 100000) (2272647 / 100000) (45453 / 2000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7413399808
    (h : (((741164651674711 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413137664) :
    (((741191162136961 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413399808 := by
  exact
    theta_restart_gain 7413137664 7413399808 15 11665 33 (741164651674711 / 100000)
      (741191162136961 / 100000) (45453 / 2000) (2272653 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7413661952
    (h : (((741191162136961 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413399808) :
    (((741217386291467 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413661952 := by
  exact
    theta_restart_gain 7413399808 7413661952 15 11539 33 (741191162136961 / 100000)
      (741217386291467 / 100000) (1136327 / 50000) (2272657 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7413924096
    (h : (((741217386291467 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413661952) :
    (((741243576402259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413924096 := by
  exact
    theta_restart_gain 7413661952 7413924096 15 11524 33 (741217386291467 / 100000)
      (741243576402259 / 100000) (1136329 / 50000) (2272661 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7414186240
    (h : (((741243576402259 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7413924096) :
    (((741269689277149 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414186240 := by
  exact
    theta_restart_gain 7413924096 7414186240 15 11490 33 (741243576402259 / 100000)
      (741269689277149 / 100000) (2272661 / 100000) (284083 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7414448384
    (h : (((741269689277149 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414186240) :
    (((370647959051957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414448384 := by
  exact
    theta_restart_gain 7414186240 7414448384 15 11541 33 (741269689277149 / 100000)
      (370647959051957 / 50000) (454533 / 20000) (568167 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7414710528
    (h : (((370647959051957 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414448384) :
    (((370661024620289 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414710528 := by
  exact
    theta_restart_gain 7414448384 7414710528 15 11498 33 (370647959051957 / 50000)
      (370661024620289 / 50000) (568167 / 25000) (2272671 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7414972672
    (h : (((370661024620289 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414710528) :
    (((370674137937729 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414972672 := by
  exact
    theta_restart_gain 7414710528 7414972672 15 11540 33 (370661024620289 / 50000)
      (370674137937729 / 50000) (71021 / 3125) (90907 / 4000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7415234816
    (h : (((370674137937729 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7414972672) :
    (((741374700267683 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415234816 := by
  exact
    theta_restart_gain 7414972672 7415234816 15 11627 33 (370674137937729 / 50000)
      (741374700267683 / 100000) (90907 / 4000) (1136339 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7415496960
    (h : (((741374700267683 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415234816) :
    (((14828015494277 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415496960 := by
  exact
    theta_restart_gain 7415234816 7415496960 15 11473 33 (741374700267683 / 100000)
      (14828015494277 / 2000) (2272679 / 100000) (1136341 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7415759104
    (h : (((14828015494277 / 2000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415496960) :
    (((370713605275437 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415759104 := by
  exact
    theta_restart_gain 7415496960 7415759104 15 11632 33 (14828015494277 / 2000)
      (370713605275437 / 50000) (1136341 / 50000) (454537 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7416021248
    (h : (((370713605275437 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7415759104) :
    (((370726707310227 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7416021248 := by
  exact
    theta_restart_gain 7415759104 7416021248 15 11530 33 (370713605275437 / 50000)
      (370726707310227 / 50000) (1136343 / 50000) (2272689 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7416283392
    (h : (((370726707310227 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7416021248) :
    (((741479493726729 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7416283392 := by
  exact
    theta_restart_gain 7416021248 7416283392 15 11475 33 (370726707310227 / 50000)
      (741479493726729 / 100000) (2272689 / 100000) (568173 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7416545536
    (h : (((741479493726729 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7416283392) :
    (((92688219336793 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7416545536 := by
  exact
    theta_restart_gain 7416283392 7416545536 15 11555 33 (741479493726729 / 100000)
      (92688219336793 / 12500) (2272693 / 100000) (284087 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7416807680
    (h : (((92688219336793 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7416545536) :
    (((92691531791213 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7416807680 := by
  exact
    theta_restart_gain 7416545536 7416807680 15 11660 33 (92688219336793 / 12500)
      (92691531791213 / 12500) (284087 / 12500) (2272699 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7417069824
    (h : (((92691531791213 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7416807680) :
    (((46347404228219 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7417069824 := by
  exact
    theta_restart_gain 7416807680 7417069824 15 11534 33 (92691531791213 / 12500)
      (46347404228219 / 6250) (22727 / 1000) (2272703 / 100000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7417331968
    (h : (((46347404228219 / 6250) : ℚ) : ℝ) ≤ Chebyshev.theta 7417069824) :
    (((741584487828151 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417331968 := by
  exact
    theta_restart_gain 7417069824 7417331968 15 11449 33 (46347404228219 / 6250)
      (741584487828151 / 100000) (2272703 / 100000) (1136353 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7417594112
    (h : (((741584487828151 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417331968) :
    (((741610723957759 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417594112 := by
  exact
    theta_restart_gain 7417331968 7417594112 15 11544 33 (741584487828151 / 100000)
      (741610723957759 / 100000) (2272707 / 100000) (227271 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7417856256
    (h : (((741610723957759 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417594112) :
    (((741637105587047 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417856256 := by
  exact
    theta_restart_gain 7417594112 7417856256 15 11608 33 (741610723957759 / 100000)
      (741637105587047 / 100000) (2272711 / 100000) (1136357 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7418118400
    (h : (((741637105587047 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7417856256) :
    (((148332669723121 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418118400 := by
  exact
    theta_restart_gain 7417856256 7418118400 15 11547 33 (741637105587047 / 100000)
      (148332669723121 / 20000) (1136357 / 50000) (2272717 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7418380544
    (h : (((148332669723121 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418118400) :
    (((148337919701701 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418380544 := by
  exact
    theta_restart_gain 7418118400 7418380544 15 11550 33 (148332669723121 / 20000)
      (148337919701701 / 20000) (1136359 / 50000) (2272721 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7418642688
    (h : (((148337919701701 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418380544) :
    (((185429019495219 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418642688 := by
  exact
    theta_restart_gain 7418380544 7418642688 15 11651 33 (148337919701701 / 20000)
      (185429019495219 / 25000) (2272721 / 100000) (568181 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7418904832
    (h : (((185429019495219 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418642688) :
    (((370871086704663 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418904832 := by
  exact
    theta_restart_gain 7418642688 7418904832 15 11482 33 (185429019495219 / 25000)
      (370871086704663 / 50000) (90909 / 4000) (284091 / 12500) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7419166976
    (h : (((370871086704663 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7418904832) :
    (((370884310572531 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419166976 := by
  exact
    theta_restart_gain 7418904832 7419166976 15 11637 33 (370871086704663 / 50000)
      (370884310572531 / 50000) (284091 / 12500) (2272731 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7419429120
    (h : (((370884310572531 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419166976) :
    (((370897446963491 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419429120 := by
  exact
    theta_restart_gain 7419166976 7419429120 15 11560 33 (370884310572531 / 50000)
      (370897446963491 / 50000) (568183 / 25000) (454547 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7419691264
    (h : (((370897446963491 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419429120) :
    (((741821128107087 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419691264 := by
  exact
    theta_restart_gain 7419429120 7419691264 15 11543 33 (370897446963491 / 50000)
      (741821128107087 / 100000) (454547 / 20000) (1136369 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7419953408
    (h : (((741821128107087 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7419691264) :
    (((23182732629749 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7419953408 := by
  exact
    theta_restart_gain 7419691264 7419953408 15 11579 33 (741821128107087 / 100000)
      (23182732629749 / 3125) (2272739 / 100000) (1136371 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7420215552
    (h : (((23182732629749 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7419953408) :
    (((9273417372183 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7420215552 := by
  exact
    theta_restart_gain 7419953408 7420215552 15 11416 33 (23182732629749 / 3125)
      (9273417372183 / 1250) (1136371 / 50000) (454549 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7420477696
    (h : (((9273417372183 / 1250) : ℚ) : ℝ) ≤ Chebyshev.theta 7420215552) :
    (((370949630221179 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7420477696 := by
  exact
    theta_restart_gain 7420215552 7420477696 15 11383 33 (9273417372183 / 1250)
      (370949630221179 / 50000) (1136373 / 50000) (2272749 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7420739840
    (h : (((370949630221179 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7420477696) :
    (((370962743982909 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7420739840 := by
  exact
    theta_restart_gain 7420477696 7420739840 15 11540 33 (370949630221179 / 50000)
      (370962743982909 / 50000) (2272749 / 100000) (142047 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7421001984
    (h : (((370962743982909 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7420739840) :
    (((92743967282871 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7421001984 := by
  exact
    theta_restart_gain 7420739840 7421001984 15 11550 33 (370962743982909 / 50000)
      (92743967282871 / 12500) (2272753 / 100000) (568189 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7421264128
    (h : (((92743967282871 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7421001984) :
    (((185494486353101 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7421264128 := by
  exact
    theta_restart_gain 7421001984 7421264128 15 11531 33 (92743967282871 / 12500)
      (185494486353101 / 25000) (568189 / 25000) (2272759 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7421526272
    (h : (((185494486353101 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7421264128) :
    (((185500998946881 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7421526272 := by
  exact
    theta_restart_gain 7421264128 7421526272 15 11462 33 (185494486353101 / 25000)
      (185500998946881 / 25000) (56819 / 2500) (2272763 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7421788416
    (h : (((185500998946881 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7421526272) :
    (((23188448248143 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7421788416 := by
  exact
    theta_restart_gain 7421526272 7421788416 15 11593 33 (185500998946881 / 25000)
      (23188448248143 / 3125) (568191 / 25000) (2272767 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7422050560
    (h : (((23188448248143 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7421788416) :
    (((37102827674481 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422050560 := by
  exact
    theta_restart_gain 7421788416 7422050560 15 11532 33 (23188448248143 / 3125)
      (37102827674481 / 5000) (2272767 / 100000) (227277 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7422312704
    (h : (((37102827674481 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422050560) :
    (((742082569899257 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422312704 := by
  exact
    theta_restart_gain 7422050560 7422312704 15 11447 33 (37102827674481 / 5000)
      (742082569899257 / 100000) (2272771 / 100000) (1136387 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7422574848
    (h : (((742082569899257 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422312704) :
    (((148421753633031 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422574848 := by
  exact
    theta_restart_gain 7422312704 7422574848 15 11527 33 (742082569899257 / 100000)
      (148421753633031 / 20000) (1136387 / 50000) (2272777 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7422836992
    (h : (((148421753633031 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422574848) :
    (((148426992386321 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422836992 := by
  exact
    theta_restart_gain 7422574848 7422836992 15 11525 33 (148421753633031 / 20000)
      (148426992386321 / 20000) (1136389 / 50000) (2272781 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7423099136
    (h : (((148426992386321 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7422836992) :
    (((742160989819617 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423099136 := by
  exact
    theta_restart_gain 7422836992 7423099136 15 11452 33 (148426992386321 / 20000)
      (742160989819617 / 100000) (2272781 / 100000) (142049 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7423361280
    (h : (((742160989819617 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423099136) :
    (((742187149574967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423361280 := by
  exact
    theta_restart_gain 7423099136 7423361280 15 11510 33 (742160989819617 / 100000)
      (742187149574967 / 100000) (454557 / 20000) (568197 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7423623424
    (h : (((742187149574967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423361280) :
    (((148442703237711 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423623424 := by
  exact
    theta_restart_gain 7423361280 7423623424 15 11601 33 (742187149574967 / 100000)
      (148442703237711 / 20000) (568197 / 25000) (2272791 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7423885568
    (h : (((148442703237711 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423623424) :
    (((742239716934731 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423885568 := by
  exact
    theta_restart_gain 7423623424 7423885568 15 11528 33 (148442703237711 / 20000)
      (742239716934731 / 100000) (284099 / 12500) (454559 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7424147712
    (h : (((742239716934731 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7423885568) :
    (((742265917715491 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424147712 := by
  exact
    theta_restart_gain 7423885568 7424147712 15 11528 33 (742239716934731 / 100000)
      (742265917715491 / 100000) (454559 / 20000) (1136399 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7424409856
    (h : (((742265917715491 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424147712) :
    (((371146083135571 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424409856 := by
  exact
    theta_restart_gain 7424147712 7424409856 15 11549 33 (742265917715491 / 100000)
      (371146083135571 / 50000) (2272799 / 100000) (1136401 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7424672000
    (h : (((371146083135571 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424409856) :
    (((371159267659973 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424672000 := by
  exact
    theta_restart_gain 7424409856 7424672000 15 11602 33 (371146083135571 / 50000)
      (371159267659973 / 50000) (1136401 / 50000) (454561 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7424934144
    (h : (((371159267659973 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424672000) :
    (((185586174397453 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424934144 := by
  exact
    theta_restart_gain 7424672000 7424934144 15 11511 33 (371159267659973 / 50000)
      (185586174397453 / 25000) (1136403 / 50000) (2272809 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7425196288
    (h : (((185586174397453 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7424934144) :
    (((185592779180407 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425196288 := by
  exact
    theta_restart_gain 7424934144 7425196288 15 11624 33 (185586174397453 / 25000)
      (185592779180407 / 25000) (2272809 / 100000) (568203 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7425458432
    (h : (((185592779180407 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425196288) :
    (((742397288163323 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425458432 := by
  exact
    theta_restart_gain 7425196288 7425458432 15 11515 33 (185592779180407 / 25000)
      (742397288163323 / 100000) (2272813 / 100000) (142051 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7425720576
    (h : (((742397288163323 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425458432) :
    (((371211734371173 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425720576 := by
  exact
    theta_restart_gain 7425458432 7425720576 15 11519 33 (742397288163323 / 100000)
      (371211734371173 / 50000) (2272817 / 100000) (113641 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7425982720
    (h : (((371211734371173 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425720576) :
    (((371224756493363 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425982720 := by
  exact
    theta_restart_gain 7425720576 7425982720 15 11459 33 (371211734371173 / 50000)
      (371224756493363 / 50000) (113641 / 5000) (2272823 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7426244864
    (h : (((371224756493363 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7425982720) :
    (((371237885461199 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426244864 := by
  exact
    theta_restart_gain 7425982720 7426244864 15 11553 33 (371224756493363 / 50000)
      (371237885461199 / 50000) (284103 / 12500) (2272827 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7426507008
    (h : (((371237885461199 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426244864) :
    (((7425021948091 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426507008 := by
  exact
    theta_restart_gain 7426244864 7426507008 15 11626 33 (371237885461199 / 50000)
      (7425021948091 / 1000) (2272827 / 100000) (227283 / 10000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7426769152
    (h : (((7425021948091 / 1000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426507008) :
    (((742528325547107 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426769152 := by
  exact
    theta_restart_gain 7426507008 7426769152 15 11497 33 (7425021948091 / 1000)
      (742528325547107 / 100000) (2272831 / 100000) (1136417 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7427031296
    (h : (((742528325547107 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7426769152) :
    (((742554735878187 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427031296 := by
  exact
    theta_restart_gain 7426769152 7427031296 15 11620 33 (742528325547107 / 100000)
      (742554735878187 / 100000) (1136417 / 50000) (2272837 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7427293440
    (h : (((742554735878187 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427031296) :
    (((742580873515187 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427293440 := by
  exact
    theta_restart_gain 7427031296 7427293440 15 11500 33 (742554735878187 / 100000)
      (742580873515187 / 100000) (1136419 / 50000) (2272841 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7427555584
    (h : (((742580873515187 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427293440) :
    (((371303445363057 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427555584 := by
  exact
    theta_restart_gain 7427293440 7427555584 15 11447 33 (742580873515187 / 100000)
      (371303445363057 / 50000) (2272841 / 100000) (568211 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7427817728
    (h : (((371303445363057 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427555584) :
    (((185658274157241 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427817728 := by
  exact
    theta_restart_gain 7427555584 7427817728 15 11530 33 (371303445363057 / 50000)
      (185658274157241 / 25000) (454569 / 20000) (142053 / 6250) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7428079872
    (h : (((185658274157241 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7427817728) :
    (((185664814845573 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428079872 := by
  exact
    theta_restart_gain 7427817728 7428079872 15 11511 33 (185658274157241 / 25000)
      (185664814845573 / 25000) (142053 / 6250) (2272851 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7428342016
    (h : (((185664814845573 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428079872) :
    (((37134273722863 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428342016 := by
  exact
    theta_restart_gain 7428079872 7428342016 15 11534 33 (185664814845573 / 25000)
      (37134273722863 / 5000) (568213 / 25000) (454571 / 20000) (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7428604160
    (h : (((37134273722863 / 5000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428342016) :
    (((148542318366813 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428604160 := by
  exact
    theta_restart_gain 7428342016 7428604160 15 11491 33 (37134273722863 / 5000)
      (148542318366813 / 20000) (454571 / 20000) (1136429 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7428866304
    (h : (((148542318366813 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428604160) :
    (((742738088824287 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428866304 := by
  exact
    theta_restart_gain 7428604160 7428866304 15 11658 33 (148542318366813 / 20000)
      (742738088824287 / 100000) (2272859 / 100000) (1136431 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7429128448
    (h : (((742738088824287 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7428866304) :
    (((742764333561801 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429128448 := by
  exact
    theta_restart_gain 7428866304 7429128448 15 11547 33 (742738088824287 / 100000)
      (742764333561801 / 100000) (1136431 / 50000) (454573 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7429390592
    (h : (((742764333561801 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429128448) :
    (((148558107486783 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429390592 := by
  exact
    theta_restart_gain 7429128448 7429390592 15 11529 33 (742764333561801 / 100000)
      (148558107486783 / 20000) (1136433 / 50000) (2272869 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7429652736
    (h : (((148558107486783 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429390592) :
    (((371408300211369 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429652736 := by
  exact
    theta_restart_gain 7429390592 7429652736 15 11467 33 (148558107486783 / 20000)
      (371408300211369 / 50000) (2272869 / 100000) (284109 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7429914880
    (h : (((371408300211369 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429652736) :
    (((742842786192571 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429914880 := by
  exact
    theta_restart_gain 7429652736 7429914880 15 11521 33 (371408300211369 / 50000)
      (742842786192571 / 100000) (2272873 / 100000) (568219 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7430177024
    (h : (((742842786192571 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7429914880) :
    (((148573772127503 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430177024 := by
  exact
    theta_restart_gain 7429914880 7430177024 15 11472 33 (742842786192571 / 100000)
      (148573772127503 / 20000) (2272877 / 100000) (28411 / 1250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7430439168
    (h : (((148573772127503 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430177024) :
    (((148579062482991 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430439168 := by
  exact
    theta_restart_gain 7430177024 7430439168 15 11638 33 (148573772127503 / 20000)
      (148579062482991 / 20000) (28411 / 1250) (2272883 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7430701312
    (h : (((148579062482991 / 20000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430439168) :
    (((742921511948823 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430701312 := by
  exact
    theta_restart_gain 7430439168 7430701312 15 11527 33 (148579062482991 / 20000)
      (742921511948823 / 100000) (568221 / 25000) (2272887 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7430963456
    (h : (((742921511948823 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430701312) :
    (((742947377402883 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430963456 := by
  exact
    theta_restart_gain 7430701312 7430963456 15 11380 33 (742921511948823 / 100000)
      (742947377402883 / 100000) (2272887 / 100000) (227289 / 10000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7431225600
    (h : (((742947377402883 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7430963456) :
    (((742973756575829 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431225600 := by
  exact
    theta_restart_gain 7430963456 7431225600 15 11606 33 (742947377402883 / 100000)
      (742973756575829 / 100000) (2272891 / 100000) (1136447 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7431487744
    (h : (((742973756575829 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431225600) :
    (((742999956224967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431487744 := by
  exact
    theta_restart_gain 7431225600 7431487744 15 11527 33 (742973756575829 / 100000)
      (742999956224967 / 100000) (1136447 / 50000) (2272897 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7431749888
    (h : (((742999956224967 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431487744) :
    (((743026012727639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431749888 := by
  exact
    theta_restart_gain 7431487744 7431749888 15 11464 33 (742999956224967 / 100000)
      (743026012727639 / 100000) (1136449 / 50000) (2272901 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7432012032
    (h : (((743026012727639 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7431749888) :
    (((743052260188387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432012032 := by
  exact
    theta_restart_gain 7431749888 7432012032 15 11548 33 (743026012727639 / 100000)
      (743052260188387 / 100000) (2272901 / 100000) (284113 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7432274176
    (h : (((743052260188387 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432012032) :
    (((743078416779127 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432274176 := by
  exact
    theta_restart_gain 7432012032 7432274176 15 11508 33 (743052260188387 / 100000)
      (743078416779127 / 100000) (454581 / 20000) (568227 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7432536320
    (h : (((743078416779127 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432274176) :
    (((743104725689227 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432536320 := by
  exact
    theta_restart_gain 7432274176 7432536320 15 11575 33 (743078416779127 / 100000)
      (743104725689227 / 100000) (568227 / 25000) (2272911 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7432798464
    (h : (((743104725689227 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432536320) :
    (((743130766442011 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432798464 := by
  exact
    theta_restart_gain 7432536320 7432798464 15 11457 33 (743104725689227 / 100000)
      (743130766442011 / 100000) (142057 / 6250) (454583 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7433060608
    (h : (((743130766442011 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7432798464) :
    (((92894641247887 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7433060608 := by
  exact
    theta_restart_gain 7432798464 7433060608 15 11599 33 (743130766442011 / 100000)
      (92894641247887 / 12500) (454583 / 20000) (1136459 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7433322752
    (h : (((92894641247887 / 12500) : ℚ) : ℝ) ≤ Chebyshev.theta 7433060608) :
    (((743183416291331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433322752 := by
  exact
    theta_restart_gain 7433060608 7433322752 15 11565 33 (92894641247887 / 12500)
      (743183416291331 / 100000) (2272919 / 100000) (1136461 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7433584896
    (h : (((743183416291331 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433322752) :
    (((743209563986019 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433584896 := by
  exact
    theta_restart_gain 7433322752 7433584896 15 11504 33 (743183416291331 / 100000)
      (743209563986019 / 100000) (1136461 / 50000) (90917 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7433847040
    (h : (((743209563986019 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433584896) :
    (((743236064030253 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433847040 := by
  exact
    theta_restart_gain 7433584896 7433847040 15 11659 33 (743209563986019 / 100000)
      (743236064030253 / 100000) (1136463 / 50000) (2272929 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434109184
    (h : (((743236064030253 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7433847040) :
    (((743262384548073 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434109184 := by
  exact
    theta_restart_gain 7433847040 7434109184 15 11580 33 (743236064030253 / 100000)
      (743262384548073 / 100000) (2272929 / 100000) (568233 / 25000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434371328
    (h : (((743262384548073 / 100000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434109184) :
    (((23227764008462 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7434371328 := by
  exact
    theta_restart_gain 7434109184 7434371328 15 11467 33 (743262384548073 / 100000)
      (23227764008462 / 3125) (2272933 / 100000) (284117 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434387712
    (h : (((23227764008462 / 3125) : ℚ) : ℝ) ≤ Chebyshev.theta 7434371328) :
    (((18582251039973 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7434387712 := by
  exact
    theta_restart_gain 7434371328 7434387712 11 701 33 (23227764008462 / 3125)
      (18582251039973 / 2500) (284117 / 12500) (2272939 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Propagate the certified entrance bound to the right endpoint of the prime window. -/
private theorem point7434389760
    (h : (((18582251039973 / 2500) : ℚ) : ℝ) ≤ Chebyshev.theta 7434387712) :
    (((185822562677281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434389760 := by
  exact
    theta_restart_gain 7434387712 7434389760 8 92 33 (18582251039973 / 2500)
      (185822562677281 / 25000) (2272937 / 100000) (113647 / 5000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- Compose the scalar prime-window transfers across this interval. -/
public theorem restart_window_7434389760 (h : ((7400892300 : ℚ) : ℝ) ≤ Chebyshev.theta 7402389760) :
    (((185822562677281 / 25000) : ℚ) : ℝ) ≤ Chebyshev.theta 7434389760 := by
  exact
    (Function.comp
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7434389760 point7434387712)
                  (Function.comp point7434371328 point7434109184))
                (Function.comp (Function.comp point7433847040 point7433584896)
                  (Function.comp point7433322752 point7433060608)))
              (Function.comp
                (Function.comp (Function.comp point7432798464 point7432536320)
                  (Function.comp point7432274176 point7432012032))
                (Function.comp (Function.comp point7431749888 point7431487744)
                  (Function.comp point7431225600 point7430963456))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7430701312 point7430439168)
                  (Function.comp point7430177024 point7429914880))
                (Function.comp (Function.comp point7429652736 point7429390592)
                  (Function.comp point7429128448 point7428866304)))
              (Function.comp
                (Function.comp (Function.comp point7428604160 point7428342016)
                  (Function.comp point7428079872 point7427817728))
                (Function.comp (Function.comp point7427555584 point7427293440)
                  (Function.comp point7427031296 point7426769152)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7426507008 point7426244864)
                  (Function.comp point7425982720 point7425720576))
                (Function.comp (Function.comp point7425458432 point7425196288)
                  (Function.comp point7424934144 point7424672000)))
              (Function.comp
                (Function.comp (Function.comp point7424409856 point7424147712)
                  (Function.comp point7423885568 point7423623424))
                (Function.comp (Function.comp point7423361280 point7423099136)
                  (Function.comp point7422836992 point7422574848))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7422312704 point7422050560)
                  (Function.comp point7421788416 point7421526272))
                (Function.comp (Function.comp point7421264128 point7421001984)
                  (Function.comp point7420739840 point7420477696)))
              (Function.comp
                (Function.comp (Function.comp point7420215552 point7419953408)
                  (Function.comp point7419691264 point7419429120))
                (Function.comp (Function.comp point7419166976 point7418904832)
                  (Function.comp point7418642688 point7418380544))))))
        (Function.comp
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7418118400 point7417856256)
                  (Function.comp point7417594112 point7417331968))
                (Function.comp (Function.comp point7417069824 point7416807680)
                  (Function.comp point7416545536 point7416283392)))
              (Function.comp
                (Function.comp (Function.comp point7416021248 point7415759104)
                  (Function.comp point7415496960 point7415234816))
                (Function.comp (Function.comp point7414972672 point7414710528)
                  (Function.comp point7414448384 point7414186240))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7413924096 point7413661952)
                  (Function.comp point7413399808 point7413137664))
                (Function.comp (Function.comp point7412875520 point7412613376)
                  (Function.comp point7412351232 point7412089088)))
              (Function.comp
                (Function.comp (Function.comp point7411826944 point7411564800)
                  (Function.comp point7411302656 point7411040512))
                (Function.comp (Function.comp point7410778368 point7410516224)
                  (Function.comp point7410254080 point7409991936)))))
          (Function.comp
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7409729792 point7409467648)
                  (Function.comp point7409205504 point7408943360))
                (Function.comp (Function.comp point7408681216 point7408419072)
                  (Function.comp point7408156928 point7407894784)))
              (Function.comp
                (Function.comp (Function.comp point7407632640 point7407370496)
                  (Function.comp point7407108352 point7406846208))
                (Function.comp (Function.comp point7406584064 point7406321920)
                  (Function.comp point7406059776 point7405797632))))
            (Function.comp
              (Function.comp
                (Function.comp (Function.comp point7405535488 point7405273344)
                  (Function.comp point7405011200 point7404749056))
                (Function.comp (Function.comp point7404486912 point7404224768)
                  (Function.comp point7403962624 point7403700480)))
              (Function.comp (Function.comp point7403438336 point7403176192)
                (Function.comp point7402914048 point7402651904))))))
      h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
