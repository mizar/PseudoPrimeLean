/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 841341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell809341184 :
    ThetaLowerSegment 809341184 809406720 (80931183895441 / 100000) (80937889176709 / 100000) := by
  exact
    packedTile32768 809341184 809406720 13 3269 28448 30 _ _ (512793 / 25000) (82047 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809406720 :
    ThetaLowerSegment 809406720 809472256 (80937889176709 / 100000) (80944438594449 / 100000) := by
  exact
    packedTile32768 809406720 809472256 13 3193 28450 30 _ _ (102559 / 5000) (2051183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809472256 :
    ThetaLowerSegment 809472256 809537792 (80944438594449 / 100000) (80951094699509 / 100000) := by
  exact
    packedTile32768 809472256 809537792 13 3245 28451 30 _ _ (512797 / 25000) (2051191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809537792 :
    ThetaLowerSegment 809537792 809603328 (80951094699509 / 100000) (80957676987473 / 100000) := by
  exact
    packedTile32768 809537792 809603328 13 3209 28452 30 _ _ (512799 / 25000) (2051199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809603328 :
    ThetaLowerSegment 809603328 809668864 (80957676987473 / 100000) (80964089051177 / 100000) := by
  exact
    packedTile32768 809603328 809668864 13 3126 28453 30 _ _ (512801 / 25000) (2051207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809668864 :
    ThetaLowerSegment 809668864 809734400 (80964089051177 / 100000) (80970587290793 / 100000) := by
  exact
    packedTile32768 809668864 809734400 13 3168 28454 30 _ _ (512803 / 25000) (410243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809734400 :
    ThetaLowerSegment 809734400 809799936 (80970587290793 / 100000) (80977112221613 / 100000) := by
  exact
    packedTile32768 809734400 809799936 13 3181 28455 30 _ _ (102561 / 5000) (2051223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809799936 :
    ThetaLowerSegment 809799936 809865472 (80977112221613 / 100000) (16196738922453 / 20000) := by
  exact
    packedTile32768 809799936 809865472 13 3209 28456 30 _ _ (512807 / 25000) (2051231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809865472 :
    ThetaLowerSegment 809865472 809931008 (16196738922453 / 20000) (3239609111957 / 4000) := by
  exact
    packedTile32768 809865472 809931008 13 3185 28458 30 _ _ (512809 / 25000) (2051239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809931008 :
    ThetaLowerSegment 809931008 809996544 (3239609111957 / 4000) (16199354253457 / 20000) := by
  exact
    packedTile32768 809931008 809996544 13 3190 28459 30 _ _ (512811 / 25000) (2051247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell809996544 :
    ThetaLowerSegment 809996544 810062080 (16199354253457 / 20000) (81003154766621 / 100000) := by
  exact
    packedTile32768 809996544 810062080 13 3112 28460 30 _ _ (2051253 / 100000) (256407 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810062080 :
    ThetaLowerSegment 810062080 810127616 (81003154766621 / 100000) (16201953606417 / 20000) := by
  exact
    packedTile32768 810062080 810127616 13 3224 28461 30 _ _ (2051261 / 100000) (64102 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810127616 :
    ThetaLowerSegment 810127616 810193152 (16201953606417 / 20000) (81016483886791 / 100000) := by
  exact
    packedTile32768 810127616 810193152 13 3274 28462 30 _ _ (2051269 / 100000) (256409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810193152 :
    ThetaLowerSegment 810193152 810258688 (81016483886791 / 100000) (40511555781389 / 50000) := by
  exact
    packedTile32768 810193152 810258688 13 3231 28463 30 _ _ (2051277 / 100000) (25641 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810258688 :
    ThetaLowerSegment 810258688 810324224 (40511555781389 / 50000) (81029649008073 / 100000) := by
  exact
    packedTile32768 810258688 810324224 13 3187 28465 30 _ _ (410257 / 20000) (256411 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810324224 :
    ThetaLowerSegment 810324224 810389760 (81029649008073 / 100000) (81036229556017 / 100000) := by
  exact
    packedTile32768 810324224 810389760 13 3208 28466 30 _ _ (2051293 / 100000) (64103 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810389760 :
    ThetaLowerSegment 810389760 810455296 (81036229556017 / 100000) (81042842950441 / 100000) := by
  exact
    packedTile32768 810389760 810455296 13 3224 28467 30 _ _ (2051301 / 100000) (256413 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810455296 :
    ThetaLowerSegment 810455296 810520832 (81042842950441 / 100000) (2026231639973 / 2500) := by
  exact
    packedTile32768 810455296 810520832 13 3131 28468 30 _ _ (2051309 / 100000) (128207 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810520832 :
    ThetaLowerSegment 810520832 810586368 (2026231639973 / 2500) (16211155706079 / 20000) := by
  exact
    packedTile32768 810520832 810586368 13 3175 28469 30 _ _ (2051317 / 100000) (51283 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810586368 :
    ThetaLowerSegment 810586368 810651904 (16211155706079 / 20000) (8106231610317 / 10000) := by
  exact
    packedTile32768 810586368 810651904 13 3187 28470 30 _ _ (82053 / 4000) (64104 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810651904 :
    ThetaLowerSegment 810651904 810717440 (8106231610317 / 10000) (81068866009439 / 100000) := by
  exact
    packedTile32768 810651904 810717440 13 3193 28471 30 _ _ (2051333 / 100000) (256417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810717440 :
    ThetaLowerSegment 810717440 810782976 (81068866009439 / 100000) (81075495946783 / 100000) := by
  exact
    packedTile32768 810717440 810782976 13 3232 28473 30 _ _ (1025671 / 50000) (410269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810782976 :
    ThetaLowerSegment 810782976 810848512 (81075495946783 / 100000) (81082123858633 / 100000) := by
  exact
    packedTile32768 810782976 810848512 13 3231 28474 30 _ _ (41027 / 2000) (2051353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810848512 :
    ThetaLowerSegment 810848512 810914048 (81082123858633 / 100000) (16217741333291 / 20000) := by
  exact
    packedTile32768 810848512 810914048 13 3209 28475 30 _ _ (1025679 / 50000) (2051361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810914048 :
    ThetaLowerSegment 810914048 810979584 (16217741333291 / 20000) (16219066515727 / 20000) := by
  exact
    packedTile32768 810914048 810979584 13 3230 28476 30 _ _ (1025683 / 50000) (2051369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell810979584 :
    ThetaLowerSegment 810979584 811045120 (16219066515727 / 20000) (81101860050703 / 100000) := by
  exact
    packedTile32768 810979584 811045120 13 3182 28477 30 _ _ (1025687 / 50000) (2051377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811045120 :
    ThetaLowerSegment 811045120 811110656 (81101860050703 / 100000) (81108391650991 / 100000) := by
  exact
    packedTile32768 811045120 811110656 13 3184 28478 30 _ _ (1025691 / 50000) (410277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811110656 :
    ThetaLowerSegment 811110656 811176192 (81108391650991 / 100000) (81114960201771 / 100000) := by
  exact
    packedTile32768 811110656 811176192 13 3202 28480 30 _ _ (205139 / 10000) (2051393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811176192 :
    ThetaLowerSegment 811176192 811241728 (81114960201771 / 100000) (81121543137953 / 100000) := by
  exact
    packedTile32768 811176192 811241728 13 3209 28481 30 _ _ (1025699 / 50000) (2051401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811241728 :
    ThetaLowerSegment 811241728 811307264 (81121543137953 / 100000) (81128048146379 / 100000) := by
  exact
    packedTile32768 811241728 811307264 13 3171 28482 30 _ _ (1025703 / 50000) (2051409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811307264 :
    ThetaLowerSegment 811307264 811372800 (81128048146379 / 100000) (16226889301329 / 20000) := by
  exact
    packedTile32768 811307264 811372800 13 3119 28483 30 _ _ (1025707 / 50000) (2051417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811372800 :
    ThetaLowerSegment 811372800 811438336 (16226889301329 / 20000) (81141132090943 / 100000) := by
  exact
    packedTile32768 811372800 811438336 13 3259 28484 30 _ _ (1025711 / 50000) (82057 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811438336 :
    ThetaLowerSegment 811438336 811503872 (81141132090943 / 100000) (81147655638343 / 100000) := by
  exact
    packedTile32768 811438336 811503872 13 3180 28485 30 _ _ (205143 / 10000) (2051433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811503872 :
    ThetaLowerSegment 811503872 811569408 (81147655638343 / 100000) (81154093050787 / 100000) := by
  exact
    packedTile32768 811503872 811569408 13 3138 28486 30 _ _ (1025719 / 50000) (2051441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811569408 :
    ThetaLowerSegment 811569408 811634944 (81154093050787 / 100000) (10145070670759 / 12500) := by
  exact
    packedTile32768 811569408 811634944 13 3155 28488 30 _ _ (2051447 / 100000) (41029 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811634944 :
    ThetaLowerSegment 811634944 811700480 (10145070670759 / 12500) (81167107456067 / 100000) := by
  exact
    packedTile32768 811634944 811700480 13 3189 28489 30 _ _ (410291 / 20000) (1025729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811700480 :
    ThetaLowerSegment 811700480 811766016 (81167107456067 / 100000) (40586902741381 / 50000) := by
  exact
    packedTile32768 811700480 811766016 13 3265 28490 30 _ _ (2051463 / 100000) (1025733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811766016 :
    ThetaLowerSegment 811766016 811831552 (40586902741381 / 50000) (81180216329637 / 100000) := by
  exact
    packedTile32768 811766016 811831552 13 3125 28491 30 _ _ (2051471 / 100000) (1025737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811831552 :
    ThetaLowerSegment 811831552 811897088 (81180216329637 / 100000) (40593381299563 / 50000) := by
  exact
    packedTile32768 811831552 811897088 13 3191 28492 30 _ _ (2051479 / 100000) (1025741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811897088 :
    ThetaLowerSegment 811897088 811962624 (40593381299563 / 50000) (20298300041333 / 25000) := by
  exact
    packedTile32768 811897088 811962624 13 3138 28493 30 _ _ (2051487 / 100000) (205149 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell811962624 :
    ThetaLowerSegment 811962624 812028160 (20298300041333 / 25000) (20299949443313 / 25000) := by
  exact
    packedTile32768 811962624 812028160 13 3216 28494 30 _ _ (410299 / 20000) (1025749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812028160 :
    ThetaLowerSegment 812028160 812093696 (20299949443313 / 25000) (81206196411109 / 100000) := by
  exact
    packedTile32768 812028160 812093696 13 3119 28496 30 _ _ (2051503 / 100000) (1025753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812093696 :
    ThetaLowerSegment 812093696 812159232 (81206196411109 / 100000) (81212839203727 / 100000) := by
  exact
    packedTile32768 812093696 812159232 13 3238 28497 30 _ _ (2051511 / 100000) (1025757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812159232 :
    ThetaLowerSegment 812159232 812224768 (81212839203727 / 100000) (10152419097069 / 12500) := by
  exact
    packedTile32768 812159232 812224768 13 3175 28498 30 _ _ (2051519 / 100000) (1025761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812224768 :
    ThetaLowerSegment 812224768 812290304 (10152419097069 / 12500) (10153243810923 / 12500) := by
  exact
    packedTile32768 812224768 812290304 13 3216 28499 30 _ _ (2051527 / 100000) (205153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812290304 :
    ThetaLowerSegment 812290304 812355840 (10153243810923 / 12500) (81232570790829 / 100000) := by
  exact
    packedTile32768 812290304 812355840 13 3227 28500 30 _ _ (410307 / 20000) (1025769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812355840 :
    ThetaLowerSegment 812355840 812421376 (81232570790829 / 100000) (81239156243859 / 100000) := by
  exact
    packedTile32768 812355840 812421376 13 3210 28501 30 _ _ (2051543 / 100000) (1025773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812421376 :
    ThetaLowerSegment 812421376 812486912 (81239156243859 / 100000) (40622837010693 / 50000) := by
  exact
    packedTile32768 812421376 812486912 13 3177 28503 30 _ _ (2051551 / 100000) (1025777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812486912 :
    ThetaLowerSegment 812486912 812552448 (40622837010693 / 50000) (40626078475493 / 50000) := by
  exact
    packedTile32768 812486912 812552448 13 3160 28504 30 _ _ (51289 / 2500) (2051563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812552448 :
    ThetaLowerSegment 812552448 812617984 (40626078475493 / 50000) (40629318927149 / 50000) := by
  exact
    packedTile32768 812552448 812617984 13 3159 28505 30 _ _ (128223 / 6250) (2051571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812617984 :
    ThetaLowerSegment 812617984 812683520 (40629318927149 / 50000) (40632544004621 / 50000) := by
  exact
    packedTile32768 812617984 812683520 13 3144 28506 30 _ _ (256447 / 12500) (2051579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812683520 :
    ThetaLowerSegment 812683520 812749056 (40632544004621 / 50000) (1625431502357 / 2000) := by
  exact
    packedTile32768 812683520 812749056 13 3162 28507 30 _ _ (64112 / 3125) (2051587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812749056 :
    ThetaLowerSegment 812749056 812814592 (1625431502357 / 2000) (40639091647841 / 50000) := by
  exact
    packedTile32768 812749056 812814592 13 3221 28508 30 _ _ (256449 / 12500) (410319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812814592 :
    ThetaLowerSegment 812814592 812880128 (40639091647841 / 50000) (40642353691841 / 50000) := by
  exact
    packedTile32768 812814592 812880128 13 3180 28509 30 _ _ (5129 / 250) (2051603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812880128 :
    ThetaLowerSegment 812880128 812945664 (40642353691841 / 50000) (40645676270997 / 50000) := by
  exact
    packedTile32768 812880128 812945664 13 3239 28511 30 _ _ (256451 / 12500) (2051611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell812945664 :
    ThetaLowerSegment 812945664 813011200 (40645676270997 / 50000) (40648981424373 / 50000) := by
  exact
    packedTile32768 812945664 813011200 13 3222 28512 30 _ _ (64113 / 3125) (2051619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813011200 :
    ThetaLowerSegment 813011200 813076736 (40648981424373 / 50000) (8130455061341 / 10000) := by
  exact
    packedTile32768 813011200 813076736 13 3211 28513 30 _ _ (256453 / 12500) (2051627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813076736 :
    ThetaLowerSegment 813076736 813142272 (8130455061341 / 10000) (40655555866273 / 50000) := by
  exact
    packedTile32768 813076736 813142272 13 3198 28514 30 _ _ (128227 / 6250) (410327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813142272 :
    ThetaLowerSegment 813142272 813207808 (40655555866273 / 50000) (40658850800113 / 50000) := by
  exact
    packedTile32768 813142272 813207808 13 3212 28515 30 _ _ (51291 / 2500) (2051643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813207808 :
    ThetaLowerSegment 813207808 813273344 (40658850800113 / 50000) (1626484845081 / 2000) := by
  exact
    packedTile32768 813207808 813273344 13 3188 28516 30 _ _ (64114 / 3125) (2051651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813273344 :
    ThetaLowerSegment 813273344 813338880 (1626484845081 / 2000) (8133079729497 / 10000) := by
  exact
    packedTile32768 813273344 813338880 13 3195 28517 30 _ _ (256457 / 12500) (2051659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813338880 :
    ThetaLowerSegment 813338880 813404416 (8133079729497 / 10000) (40668642328269 / 50000) := by
  exact
    packedTile32768 813338880 813404416 13 3162 28519 30 _ _ (128229 / 6250) (2051667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813404416 :
    ThetaLowerSegment 813404416 813469952 (40668642328269 / 50000) (40671876789177 / 50000) := by
  exact
    packedTile32768 813404416 813469952 13 3153 28520 30 _ _ (256459 / 12500) (82067 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813469952 :
    ThetaLowerSegment 813469952 813535488 (40671876789177 / 50000) (40675076384137 / 50000) := by
  exact
    packedTile32768 813469952 813535488 13 3119 28521 30 _ _ (12823 / 625) (2051683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813535488 :
    ThetaLowerSegment 813535488 813601024 (40675076384137 / 50000) (40678359086537 / 50000) := by
  exact
    packedTile32768 813535488 813601024 13 3200 28522 30 _ _ (2051689 / 100000) (512923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813601024 :
    ThetaLowerSegment 813601024 813666560 (40678359086537 / 50000) (40681699249253 / 50000) := by
  exact
    packedTile32768 813601024 813666560 13 3256 28523 30 _ _ (2051697 / 100000) (20517 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813666560 :
    ThetaLowerSegment 813666560 813732096 (40681699249253 / 50000) (20342524841759 / 25000) := by
  exact
    packedTile32768 813666560 813732096 13 3266 28524 30 _ _ (410341 / 20000) (512927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813732096 :
    ThetaLowerSegment 813732096 813797632 (20342524841759 / 25000) (20344145695029 / 25000) := by
  exact
    packedTile32768 813732096 813797632 13 3160 28525 30 _ _ (2051713 / 100000) (512929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813797632 :
    ThetaLowerSegment 813797632 813863168 (20344145695029 / 25000) (81383060063313 / 100000) := by
  exact
    packedTile32768 813797632 813863168 13 3157 28527 30 _ _ (2051721 / 100000) (512931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813863168 :
    ThetaLowerSegment 813863168 813928704 (81383060063313 / 100000) (81389551733869 / 100000) := by
  exact
    packedTile32768 813863168 813928704 13 3164 28528 30 _ _ (2051729 / 100000) (512933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813928704 :
    ThetaLowerSegment 813928704 813994240 (81389551733869 / 100000) (16279214430811 / 20000) := by
  exact
    packedTile32768 813928704 813994240 13 3178 28529 30 _ _ (2051737 / 100000) (102587 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell813994240 :
    ThetaLowerSegment 813994240 814059776 (16279214430811 / 20000) (814025987549 / 1000) := by
  exact
    packedTile32768 813994240 814059776 13 3181 28530 30 _ _ (410349 / 20000) (512937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814059776 :
    ThetaLowerSegment 814059776 814125312 (814025987549 / 1000) (10176154778451 / 12500) := by
  exact
    packedTile32768 814059776 814125312 13 3236 28531 30 _ _ (2051753 / 100000) (512939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814125312 :
    ThetaLowerSegment 814125312 814190848 (10176154778451 / 12500) (81415707430041 / 100000) := by
  exact
    packedTile32768 814125312 814190848 13 3153 28532 30 _ _ (2051761 / 100000) (512941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814190848 :
    ThetaLowerSegment 814190848 814256384 (81415707430041 / 100000) (4071110679477 / 5000) := by
  exact
    packedTile32768 814190848 814256384 13 3171 28534 30 _ _ (2051769 / 100000) (512943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814256384 :
    ThetaLowerSegment 814256384 814321920 (4071110679477 / 5000) (81428838777473 / 100000) := by
  exact
    packedTile32768 814256384 814321920 13 3229 28535 30 _ _ (2051777 / 100000) (102589 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814321920 :
    ThetaLowerSegment 814321920 814387456 (81428838777473 / 100000) (81435322418073 / 100000) := by
  exact
    packedTile32768 814321920 814387456 13 3160 28536 30 _ _ (410357 / 20000) (512947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814387456 :
    ThetaLowerSegment 814387456 814452992 (81435322418073 / 100000) (40720998450351 / 50000) := by
  exact
    packedTile32768 814387456 814452992 13 3253 28537 30 _ _ (2051793 / 100000) (512949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814452992 :
    ThetaLowerSegment 814452992 814518528 (40720998450351 / 50000) (40724338782379 / 50000) := by
  exact
    packedTile32768 814452992 814518528 13 3256 28538 30 _ _ (2051801 / 100000) (512951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814518528 :
    ThetaLowerSegment 814518528 814584064 (40724338782379 / 50000) (81455175643861 / 100000) := by
  exact
    packedTile32768 814518528 814584064 13 3167 28539 30 _ _ (2051809 / 100000) (512953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814584064 :
    ThetaLowerSegment 814584064 814649600 (81455175643861 / 100000) (81461720940091 / 100000) := by
  exact
    packedTile32768 814584064 814649600 13 3190 28540 30 _ _ (2051817 / 100000) (102591 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814649600 :
    ThetaLowerSegment 814649600 814715136 (81461720940091 / 100000) (81468294987391 / 100000) := by
  exact
    packedTile32768 814649600 814715136 13 3204 28542 30 _ _ (82073 / 4000) (512957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814715136 :
    ThetaLowerSegment 814715136 814780672 (81468294987391 / 100000) (40737445815243 / 50000) := by
  exact
    packedTile32768 814715136 814780672 13 3215 28543 30 _ _ (2051833 / 100000) (512959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814780672 :
    ThetaLowerSegment 814780672 814846208 (40737445815243 / 50000) (81481369292523 / 100000) := by
  exact
    packedTile32768 814780672 814846208 13 3157 28544 30 _ _ (2051841 / 100000) (512961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814846208 :
    ThetaLowerSegment 814846208 814911744 (81481369292523 / 100000) (81487988557397 / 100000) := by
  exact
    packedTile32768 814846208 814911744 13 3226 28545 30 _ _ (2051849 / 100000) (512963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814911744 :
    ThetaLowerSegment 814911744 814977280 (81487988557397 / 100000) (81494589384583 / 100000) := by
  exact
    packedTile32768 814911744 814977280 13 3217 28546 30 _ _ (1025929 / 50000) (2051861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell814977280 :
    ThetaLowerSegment 814977280 815042816 (81494589384583 / 100000) (81501106110999 / 100000) := by
  exact
    packedTile32768 814977280 815042816 13 3176 28547 30 _ _ (1025933 / 50000) (2051869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815042816 :
    ThetaLowerSegment 815042816 815108352 (81501106110999 / 100000) (81507647485311 / 100000) := by
  exact
    packedTile32768 815042816 815108352 13 3188 28548 30 _ _ (1025937 / 50000) (2051877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815108352 :
    ThetaLowerSegment 815108352 815173888 (81507647485311 / 100000) (81514010371393 / 100000) := by
  exact
    packedTile32768 815108352 815173888 13 3101 28550 30 _ _ (1025941 / 50000) (410377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815173888 :
    ThetaLowerSegment 815173888 815239424 (81514010371393 / 100000) (81520518966473 / 100000) := by
  exact
    packedTile32768 815173888 815239424 13 3172 28551 30 _ _ (205189 / 10000) (2051893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815239424 :
    ThetaLowerSegment 815239424 815304960 (81520518966473 / 100000) (81527148648911 / 100000) := by
  exact
    packedTile32768 815239424 815304960 13 3231 28552 30 _ _ (1025949 / 50000) (2051901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815304960 :
    ThetaLowerSegment 815304960 815370496 (81527148648911 / 100000) (81533694229051 / 100000) := by
  exact
    packedTile32768 815304960 815370496 13 3190 28553 30 _ _ (1025953 / 50000) (2051909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815370496 :
    ThetaLowerSegment 815370496 815436032 (81533694229051 / 100000) (3261613779293 / 4000) := by
  exact
    packedTile32768 815370496 815436032 13 3241 28554 30 _ _ (1025957 / 50000) (2051917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815436032 :
    ThetaLowerSegment 815436032 815501568 (3261613779293 / 4000) (81546918840413 / 100000) := by
  exact
    packedTile32768 815436032 815501568 13 3204 28555 30 _ _ (1025961 / 50000) (82077 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815501568 :
    ThetaLowerSegment 815501568 815567104 (81546918840413 / 100000) (81553501431853 / 100000) := by
  exact
    packedTile32768 815501568 815567104 13 3208 28556 30 _ _ (205193 / 10000) (2051933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815567104 :
    ThetaLowerSegment 815567104 815632640 (81553501431853 / 100000) (81560180490043 / 100000) := by
  exact
    packedTile32768 815567104 815632640 13 3255 28558 30 _ _ (1025969 / 50000) (2051941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815632640 :
    ThetaLowerSegment 815632640 815698176 (81560180490043 / 100000) (3262671264013 / 4000) := by
  exact
    packedTile32768 815632640 815698176 13 3217 28559 30 _ _ (1025973 / 50000) (2051949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815698176 :
    ThetaLowerSegment 815698176 815763712 (3262671264013 / 4000) (81573339645309 / 100000) := by
  exact
    packedTile32768 815698176 815763712 13 3196 28560 30 _ _ (1025977 / 50000) (2051957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815763712 :
    ThetaLowerSegment 815763712 815829248 (81573339645309 / 100000) (81579996210037 / 100000) := by
  exact
    packedTile32768 815763712 815829248 13 3244 28561 30 _ _ (1025981 / 50000) (410393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815829248 :
    ThetaLowerSegment 815829248 815894784 (81579996210037 / 100000) (81586552254187 / 100000) := by
  exact
    packedTile32768 815829248 815894784 13 3195 28562 30 _ _ (205197 / 10000) (2051973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815894784 :
    ThetaLowerSegment 815894784 815960320 (81586552254187 / 100000) (81593112427853 / 100000) := by
  exact
    packedTile32768 815894784 815960320 13 3197 28563 30 _ _ (1025989 / 50000) (2051981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell815960320 :
    ThetaLowerSegment 815960320 816025856 (81593112427853 / 100000) (81599670575109 / 100000) := by
  exact
    packedTile32768 815960320 816025856 13 3196 28565 30 _ _ (1025993 / 50000) (2051989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816025856 :
    ThetaLowerSegment 816025856 816091392 (81599670575109 / 100000) (81606140512191 / 100000) := by
  exact
    packedTile32768 816025856 816091392 13 3153 28566 30 _ _ (1025997 / 50000) (2051997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816091392 :
    ThetaLowerSegment 816091392 816156928 (81606140512191 / 100000) (81612760270643 / 100000) := by
  exact
    packedTile32768 816091392 816156928 13 3226 28567 30 _ _ (1026001 / 50000) (410401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816156928 :
    ThetaLowerSegment 816156928 816222464 (81612760270643 / 100000) (81619353378773 / 100000) := by
  exact
    packedTile32768 816156928 816222464 13 3213 28568 30 _ _ (205201 / 10000) (2052013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816222464 :
    ThetaLowerSegment 816222464 816288000 (81619353378773 / 100000) (81625901368211 / 100000) := by
  exact
    packedTile32768 816222464 816288000 13 3191 28569 30 _ _ (1026009 / 50000) (2052021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816288000 :
    ThetaLowerSegment 816288000 816353536 (81625901368211 / 100000) (81632396030501 / 100000) := by
  exact
    packedTile32768 816288000 816353536 13 3165 28570 30 _ _ (1026013 / 50000) (2052029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816353536 :
    ThetaLowerSegment 816353536 816419072 (81632396030501 / 100000) (81638948175063 / 100000) := by
  exact
    packedTile32768 816353536 816419072 13 3193 28571 30 _ _ (1026017 / 50000) (2052037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816419072 :
    ThetaLowerSegment 816419072 816484608 (81638948175063 / 100000) (81645533177841 / 100000) := by
  exact
    packedTile32768 816419072 816484608 13 3209 28573 30 _ _ (1026021 / 50000) (410409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816484608 :
    ThetaLowerSegment 816484608 816550144 (81645533177841 / 100000) (81652165403441 / 100000) := by
  exact
    packedTile32768 816484608 816550144 13 3232 28574 30 _ _ (41041 / 2000) (2052053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816550144 :
    ThetaLowerSegment 816550144 816615680 (81652165403441 / 100000) (81658629386141 / 100000) := by
  exact
    packedTile32768 816550144 816615680 13 3150 28575 30 _ _ (1026029 / 50000) (2052061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816615680 :
    ThetaLowerSegment 816615680 816681216 (81658629386141 / 100000) (81665222674199 / 100000) := by
  exact
    packedTile32768 816615680 816681216 13 3213 28576 30 _ _ (1026033 / 50000) (2052069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816681216 :
    ThetaLowerSegment 816681216 816746752 (81665222674199 / 100000) (16334338983119 / 20000) := by
  exact
    packedTile32768 816681216 816746752 13 3154 28577 30 _ _ (1026037 / 50000) (2052077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816746752 :
    ThetaLowerSegment 816746752 816812288 (16334338983119 / 20000) (81678392911243 / 100000) := by
  exact
    packedTile32768 816746752 816812288 13 3264 28578 30 _ _ (1026041 / 50000) (410417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816812288 :
    ThetaLowerSegment 816812288 816877824 (81678392911243 / 100000) (81684902140723 / 100000) := by
  exact
    packedTile32768 816812288 816877824 13 3172 28579 30 _ _ (205209 / 10000) (2052093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816877824 :
    ThetaLowerSegment 816877824 816943360 (81684902140723 / 100000) (81691534524691 / 100000) := by
  exact
    packedTile32768 816877824 816943360 13 3232 28581 30 _ _ (2052099 / 100000) (1026051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell816943360 :
    ThetaLowerSegment 816943360 817008896 (81691534524691 / 100000) (20424535064281 / 25000) := by
  exact
    packedTile32768 816943360 817008896 13 3219 28582 30 _ _ (2052107 / 100000) (205211 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817008896 :
    ThetaLowerSegment 817008896 817074432 (20424535064281 / 25000) (40852400711207 / 50000) := by
  exact
    packedTile32768 817008896 817074432 13 3246 28583 30 _ _ (410423 / 20000) (1026059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817074432 :
    ThetaLowerSegment 817074432 817139968 (40852400711207 / 50000) (40855626648563 / 50000) := by
  exact
    packedTile32768 817074432 817139968 13 3144 28584 30 _ _ (2052123 / 100000) (1026063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817139968 :
    ThetaLowerSegment 817139968 817205504 (40855626648563 / 50000) (3268719289387 / 4000) := by
  exact
    packedTile32768 817139968 817205504 13 3279 28585 30 _ _ (2052131 / 100000) (1026067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817205504 :
    ThetaLowerSegment 817205504 817271040 (3268719289387 / 4000) (40862287878641 / 50000) := by
  exact
    packedTile32768 817205504 817271040 13 3213 28586 30 _ _ (2052139 / 100000) (1026071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817271040 :
    ThetaLowerSegment 817271040 817336576 (40862287878641 / 50000) (81731103636889 / 100000) := by
  exact
    packedTile32768 817271040 817336576 13 3181 28587 30 _ _ (2052147 / 100000) (41043 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817336576 :
    ThetaLowerSegment 817336576 817402112 (81731103636889 / 100000) (81737580238069 / 100000) := by
  exact
    packedTile32768 817336576 817402112 13 3156 28589 30 _ _ (410431 / 20000) (1026079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817402112 :
    ThetaLowerSegment 817402112 817467648 (81737580238069 / 100000) (408720089367 / 500) := by
  exact
    packedTile32768 817402112 817467648 13 3137 28590 30 _ _ (2052163 / 100000) (1026083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817467648 :
    ThetaLowerSegment 817467648 817533184 (408720089367 / 500) (81750590977113 / 100000) := by
  exact
    packedTile32768 817467648 817533184 13 3203 28591 30 _ _ (2052171 / 100000) (1026087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817533184 :
    ThetaLowerSegment 817533184 817598720 (81750590977113 / 100000) (4087857179233 / 5000) := by
  exact
    packedTile32768 817533184 817598720 13 3193 28592 30 _ _ (2052179 / 100000) (1026091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817598720 :
    ThetaLowerSegment 817598720 817664256 (4087857179233 / 5000) (40881840926221 / 50000) := by
  exact
    packedTile32768 817598720 817664256 13 3186 28593 30 _ _ (2052187 / 100000) (205219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817664256 :
    ThetaLowerSegment 817664256 817729792 (40881840926221 / 50000) (40885181899681 / 50000) := by
  exact
    packedTile32768 817664256 817729792 13 3256 28594 30 _ _ (410439 / 20000) (1026099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817729792 :
    ThetaLowerSegment 817729792 817795328 (40885181899681 / 50000) (16355378371421 / 20000) := by
  exact
    packedTile32768 817729792 817795328 13 3181 28595 30 _ _ (2052203 / 100000) (1026103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817795328 :
    ThetaLowerSegment 817795328 817860864 (16355378371421 / 20000) (81783380948287 / 100000) := by
  exact
    packedTile32768 817795328 817860864 13 3162 28597 30 _ _ (2052211 / 100000) (1026107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817860864 :
    ThetaLowerSegment 817860864 817926400 (81783380948287 / 100000) (81789894691393 / 100000) := by
  exact
    packedTile32768 817860864 817926400 13 3174 28598 30 _ _ (2052219 / 100000) (1026111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817926400 :
    ThetaLowerSegment 817926400 817991936 (81789894691393 / 100000) (5112275400479 / 6250) := by
  exact
    packedTile32768 817926400 817991936 13 3173 28599 30 _ _ (2052227 / 100000) (205223 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell817991936 :
    ThetaLowerSegment 817991936 818057472 (5112275400479 / 6250) (81803037178949 / 100000) := by
  exact
    packedTile32768 817991936 818057472 13 3231 28600 30 _ _ (410447 / 20000) (1026119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818057472 :
    ThetaLowerSegment 818057472 818123008 (81803037178949 / 100000) (5113101426671 / 6250) := by
  exact
    packedTile32768 818057472 818123008 13 3209 28601 30 _ _ (2052243 / 100000) (1026123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818123008 :
    ThetaLowerSegment 818123008 818188544 (5113101426671 / 6250) (81816089469637 / 100000) := by
  exact
    packedTile32768 818123008 818188544 13 3151 28602 30 _ _ (2052251 / 100000) (1026127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818188544 :
    ThetaLowerSegment 818188544 818254080 (81816089469637 / 100000) (5113906936753 / 6250) := by
  exact
    packedTile32768 818188544 818254080 13 3129 28603 30 _ _ (2052259 / 100000) (1026131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818254080 :
    ThetaLowerSegment 818254080 818319616 (5113906936753 / 6250) (81828969472297 / 100000) := by
  exact
    packedTile32768 818254080 818319616 13 3147 28605 30 _ _ (2052267 / 100000) (205227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818319616 :
    ThetaLowerSegment 818319616 818385152 (81828969472297 / 100000) (40917771454561 / 50000) := by
  exact
    packedTile32768 818319616 818385152 13 3203 28606 30 _ _ (82091 / 4000) (1026139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818385152 :
    ThetaLowerSegment 818385152 818450688 (40917771454561 / 50000) (20460522422973 / 25000) := by
  exact
    packedTile32768 818385152 818450688 13 3190 28607 30 _ _ (2052283 / 100000) (1026143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818450688 :
    ThetaLowerSegment 818450688 818516224 (20460522422973 / 25000) (40924379818821 / 50000) := by
  exact
    packedTile32768 818450688 818516224 13 3250 28608 30 _ _ (2052291 / 100000) (1026147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818516224 :
    ThetaLowerSegment 818516224 818581760 (40924379818821 / 50000) (20463818408667 / 25000) := by
  exact
    packedTile32768 818516224 818581760 13 3174 28609 30 _ _ (2052299 / 100000) (1026151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818581760 :
    ThetaLowerSegment 818581760 818647296 (20463818408667 / 25000) (81861806127849 / 100000) := by
  exact
    packedTile32768 818581760 818647296 13 3183 28610 30 _ _ (2052307 / 100000) (205231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818647296 :
    ThetaLowerSegment 818647296 818712832 (81861806127849 / 100000) (81868344803439 / 100000) := by
  exact
    packedTile32768 818647296 818712832 13 3186 28612 30 _ _ (410463 / 20000) (1026159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818712832 :
    ThetaLowerSegment 818712832 818778368 (81868344803439 / 100000) (16374987372983 / 20000) := by
  exact
    packedTile32768 818712832 818778368 13 3212 28613 30 _ _ (2052323 / 100000) (1026163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818778368 :
    ThetaLowerSegment 818778368 818843904 (16374987372983 / 20000) (81881520742763 / 100000) := by
  exact
    packedTile32768 818778368 818843904 13 3208 28614 30 _ _ (2052331 / 100000) (1026167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818843904 :
    ThetaLowerSegment 818843904 818909440 (81881520742763 / 100000) (81888178530479 / 100000) := by
  exact
    packedTile32768 818843904 818909440 13 3244 28615 30 _ _ (2052339 / 100000) (1026171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818909440 :
    ThetaLowerSegment 818909440 818974976 (81888178530479 / 100000) (16378931968461 / 20000) := by
  exact
    packedTile32768 818909440 818974976 13 3158 28616 30 _ _ (2052347 / 100000) (41047 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell818974976 :
    ThetaLowerSegment 818974976 819040512 (16378931968461 / 20000) (1638024506519 / 2000) := by
  exact
    packedTile32768 818974976 819040512 13 3199 28617 30 _ _ (410471 / 20000) (1026179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819040512 :
    ThetaLowerSegment 819040512 819106048 (1638024506519 / 2000) (40953871815419 / 50000) := by
  exact
    packedTile32768 819040512 819106048 13 3176 28618 30 _ _ (2052363 / 100000) (1026183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819106048 :
    ThetaLowerSegment 819106048 819171584 (40953871815419 / 50000) (16382848697959 / 20000) := by
  exact
    packedTile32768 819106048 819171584 13 3167 28620 30 _ _ (2052371 / 100000) (1026187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819171584 :
    ThetaLowerSegment 819171584 819237120 (16382848697959 / 20000) (40960361425149 / 50000) := by
  exact
    packedTile32768 819171584 819237120 13 3157 28621 30 _ _ (2052379 / 100000) (1026191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819237120 :
    ThetaLowerSegment 819237120 819302656 (40960361425149 / 50000) (40963678082541 / 50000) := by
  exact
    packedTile32768 819237120 819302656 13 3232 28622 30 _ _ (2052387 / 100000) (205239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819302656 :
    ThetaLowerSegment 819302656 819368192 (40963678082541 / 50000) (20483434778383 / 25000) := by
  exact
    packedTile32768 819302656 819368192 13 3110 28623 30 _ _ (410479 / 20000) (1026199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819368192 :
    ThetaLowerSegment 819368192 819433728 (20483434778383 / 25000) (10242539376593 / 12500) := by
  exact
    packedTile32768 819368192 819433728 13 3204 28624 30 _ _ (2052403 / 100000) (1026203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819433728 :
    ThetaLowerSegment 819433728 819499264 (10242539376593 / 12500) (40973463940493 / 50000) := by
  exact
    packedTile32768 819433728 819499264 13 3222 28625 30 _ _ (2052411 / 100000) (1026207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819499264 :
    ThetaLowerSegment 819499264 819564800 (40973463940493 / 50000) (2561048918876 / 3125) := by
  exact
    packedTile32768 819499264 819564800 13 3234 28626 30 _ _ (2052419 / 100000) (1026211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819564800 :
    ThetaLowerSegment 819564800 819630336 (2561048918876 / 3125) (81960057230633 / 100000) := by
  exact
    packedTile32768 819564800 819630336 13 3163 28628 30 _ _ (2052427 / 100000) (205243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819630336 :
    ThetaLowerSegment 819630336 819695872 (81960057230633 / 100000) (81966731749253 / 100000) := by
  exact
    packedTile32768 819630336 819695872 13 3252 28629 30 _ _ (410487 / 20000) (1026219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819695872 :
    ThetaLowerSegment 819695872 819761408 (81966731749253 / 100000) (5123329298763 / 6250) := by
  exact
    packedTile32768 819695872 819761408 13 3185 28630 30 _ _ (2052443 / 100000) (1026223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819761408 :
    ThetaLowerSegment 819761408 819826944 (5123329298763 / 6250) (81979715528799 / 100000) := by
  exact
    packedTile32768 819761408 819826944 13 3141 28631 30 _ _ (2052451 / 100000) (1026227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819826944 :
    ThetaLowerSegment 819826944 819892480 (81979715528799 / 100000) (81986242348419 / 100000) := by
  exact
    packedTile32768 819826944 819892480 13 3180 28632 30 _ _ (2052459 / 100000) (1026231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819892480 :
    ThetaLowerSegment 819892480 819958016 (81986242348419 / 100000) (8199287797423 / 10000) := by
  exact
    packedTile32768 819892480 819958016 13 3233 28633 30 _ _ (2052467 / 100000) (205247 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell819958016 :
    ThetaLowerSegment 819958016 820023552 (8199287797423 / 10000) (16399865780631 / 20000) := by
  exact
    packedTile32768 819958016 820023552 13 3143 28634 30 _ _ (82099 / 4000) (1026239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820023552 :
    ThetaLowerSegment 820023552 820089088 (16399865780631 / 20000) (20501475751551 / 25000) := by
  exact
    packedTile32768 820023552 820089088 13 3203 28636 30 _ _ (2052483 / 100000) (1026243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820089088 :
    ThetaLowerSegment 820089088 820154624 (20501475751551 / 25000) (20503101324423 / 25000) := by
  exact
    packedTile32768 820089088 820154624 13 3168 28637 30 _ _ (2052491 / 100000) (1026247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820154624 :
    ThetaLowerSegment 820154624 820220160 (20503101324423 / 25000) (82018999976979 / 100000) := by
  exact
    packedTile32768 820154624 820220160 13 3213 28638 30 _ _ (2052499 / 100000) (1026251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820220160 :
    ThetaLowerSegment 820220160 820285696 (82018999976979 / 100000) (41012813761041 / 50000) := by
  exact
    packedTile32768 820220160 820285696 13 3229 28639 30 _ _ (2052507 / 100000) (205251 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820285696 :
    ThetaLowerSegment 820285696 820351232 (41012813761041 / 50000) (41016077259891 / 50000) := by
  exact
    packedTile32768 820285696 820351232 13 3180 28640 30 _ _ (410503 / 20000) (1026259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820351232 :
    ThetaLowerSegment 820351232 820416768 (41016077259891 / 50000) (82038609704617 / 100000) := by
  exact
    packedTile32768 820351232 820416768 13 3145 28641 30 _ _ (2052523 / 100000) (1026263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820416768 :
    ThetaLowerSegment 820416768 820482304 (82038609704617 / 100000) (82045190119003 / 100000) := by
  exact
    packedTile32768 820416768 820482304 13 3206 28642 30 _ _ (2052531 / 100000) (1026267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820482304 :
    ThetaLowerSegment 820482304 820547840 (82045190119003 / 100000) (41025925304029 / 50000) := by
  exact
    packedTile32768 820482304 820547840 13 3245 28644 30 _ _ (2052539 / 100000) (1026271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820547840 :
    ThetaLowerSegment 820547840 820613376 (41025925304029 / 50000) (205145975057 / 250) := by
  exact
    packedTile32768 820547840 820613376 13 3186 28645 30 _ _ (2052547 / 100000) (41051 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820613376 :
    ThetaLowerSegment 820613376 820678912 (205145975057 / 250) (16413000260491 / 20000) := by
  exact
    packedTile32768 820613376 820678912 13 3221 28646 30 _ _ (410511 / 20000) (1026279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820678912 :
    ThetaLowerSegment 820678912 820744448 (16413000260491 / 20000) (8207157976687 / 10000) := by
  exact
    packedTile32768 820678912 820744448 13 3205 28647 30 _ _ (2052563 / 100000) (1026283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820744448 :
    ThetaLowerSegment 820744448 820809984 (8207157976687 / 10000) (2564937891387 / 3125) := by
  exact
    packedTile32768 820744448 820809984 13 3134 28648 30 _ _ (2052571 / 100000) (1026287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820809984 :
    ThetaLowerSegment 820809984 820875520 (2564937891387 / 3125) (20521155457191 / 25000) := by
  exact
    packedTile32768 820809984 820875520 13 3220 28649 30 _ _ (2052579 / 100000) (1026291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820875520 :
    ThetaLowerSegment 820875520 820941056 (20521155457191 / 25000) (3283651955771 / 4000) := by
  exact
    packedTile32768 820875520 820941056 13 3253 28650 30 _ _ (2052587 / 100000) (205259 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell820941056 :
    ThetaLowerSegment 820941056 821006592 (3283651955771 / 4000) (8209794314429 / 10000) := by
  exact
    packedTile32768 820941056 821006592 13 3237 28652 30 _ _ (410519 / 20000) (1026299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821006592 :
    ThetaLowerSegment 821006592 821072128 (8209794314429 / 10000) (41052284473387 / 50000) := by
  exact
    packedTile32768 821006592 821072128 13 3228 28653 30 _ _ (2052603 / 100000) (1026303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821072128 :
    ThetaLowerSegment 821072128 821137664 (41052284473387 / 50000) (4105555428271 / 5000) := by
  exact
    packedTile32768 821072128 821137664 13 3186 28654 30 _ _ (2052611 / 100000) (1026307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821137664 :
    ThetaLowerSegment 821137664 821203200 (4105555428271 / 5000) (82117494263129 / 100000) := by
  exact
    packedTile32768 821137664 821203200 13 3111 28655 30 _ _ (2052619 / 100000) (1026311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821203200 :
    ThetaLowerSegment 821203200 821268736 (82117494263129 / 100000) (41062005676927 / 50000) := by
  exact
    packedTile32768 821203200 821268736 13 3175 28656 30 _ _ (2052627 / 100000) (205263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821268736 :
    ThetaLowerSegment 821268736 821334272 (41062005676927 / 50000) (41065257050767 / 50000) := by
  exact
    packedTile32768 821268736 821334272 13 3168 28657 30 _ _ (410527 / 20000) (1026319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821334272 :
    ThetaLowerSegment 821334272 821399808 (41065257050767 / 50000) (41068528963709 / 50000) := by
  exact
    packedTile32768 821334272 821399808 13 3188 28658 30 _ _ (2052643 / 100000) (1026323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821399808 :
    ThetaLowerSegment 821399808 821465344 (41068528963709 / 50000) (82143583304947 / 100000) := by
  exact
    packedTile32768 821399808 821465344 13 3179 28660 30 _ _ (2052651 / 100000) (1026327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821465344 :
    ThetaLowerSegment 821465344 821530880 (82143583304947 / 100000) (82150160024383 / 100000) := by
  exact
    packedTile32768 821465344 821530880 13 3204 28661 30 _ _ (2052659 / 100000) (1026331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821530880 :
    ThetaLowerSegment 821530880 821596416 (82150160024383 / 100000) (82156650557437 / 100000) := by
  exact
    packedTile32768 821530880 821596416 13 3162 28662 30 _ _ (2052667 / 100000) (205267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821596416 :
    ThetaLowerSegment 821596416 821661952 (82156650557437 / 100000) (82163241693651 / 100000) := by
  exact
    packedTile32768 821596416 821661952 13 3211 28663 30 _ _ (1026337 / 50000) (2052677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821661952 :
    ThetaLowerSegment 821661952 821727488 (82163241693651 / 100000) (82169652219537 / 100000) := by
  exact
    packedTile32768 821661952 821727488 13 3123 28664 30 _ _ (1026341 / 50000) (410537 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821727488 :
    ThetaLowerSegment 821727488 821793024 (82169652219537 / 100000) (82176329620107 / 100000) := by
  exact
    packedTile32768 821727488 821793024 13 3253 28665 30 _ _ (205269 / 10000) (2052693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821793024 :
    ThetaLowerSegment 821793024 821858560 (82176329620107 / 100000) (82182896201009 / 100000) := by
  exact
    packedTile32768 821793024 821858560 13 3199 28666 30 _ _ (1026349 / 50000) (2052701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821858560 :
    ThetaLowerSegment 821858560 821924096 (82182896201009 / 100000) (82189401226323 / 100000) := by
  exact
    packedTile32768 821858560 821924096 13 3169 28668 30 _ _ (1026353 / 50000) (2052709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821924096 :
    ThetaLowerSegment 821924096 821989632 (82189401226323 / 100000) (82195988385549 / 100000) := by
  exact
    packedTile32768 821924096 821989632 13 3209 28669 30 _ _ (1026357 / 50000) (2052717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell821989632 :
    ThetaLowerSegment 821989632 822055168 (82195988385549 / 100000) (16440496229047 / 20000) := by
  exact
    packedTile32768 821989632 822055168 13 3163 28670 30 _ _ (1026361 / 50000) (82109 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822055168 :
    ThetaLowerSegment 822055168 822120704 (16440496229047 / 20000) (16441779185297 / 20000) := by
  exact
    packedTile32768 822055168 822120704 13 3125 28671 30 _ _ (205273 / 10000) (2052733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822120704 :
    ThetaLowerSegment 822120704 822186240 (16441779185297 / 20000) (3288616945333 / 4000) := by
  exact
    packedTile32768 822120704 822186240 13 3180 28672 30 _ _ (1026369 / 50000) (2052741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822186240 :
    ThetaLowerSegment 822186240 822251776 (3288616945333 / 4000) (82221914416177 / 100000) := by
  exact
    packedTile32768 822186240 822251776 13 3162 28673 30 _ _ (1026373 / 50000) (2052749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822251776 :
    ThetaLowerSegment 822251776 822317312 (82221914416177 / 100000) (82228444226651 / 100000) := by
  exact
    packedTile32768 822251776 822317312 13 3181 28674 30 _ _ (1026377 / 50000) (2052757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822317312 :
    ThetaLowerSegment 822317312 822382848 (82228444226651 / 100000) (16447032172783 / 20000) := by
  exact
    packedTile32768 822317312 822382848 13 3272 28676 30 _ _ (1026381 / 50000) (410553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822382848 :
    ThetaLowerSegment 822382848 822448384 (16447032172783 / 20000) (3289671898773 / 4000) := by
  exact
    packedTile32768 822382848 822448384 13 3233 28677 30 _ _ (205277 / 10000) (2052773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822448384 :
    ThetaLowerSegment 822448384 822513920 (3289671898773 / 4000) (82248565478391 / 100000) := by
  exact
    packedTile32768 822448384 822513920 13 3297 28678 30 _ _ (1026389 / 50000) (2052781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822513920 :
    ThetaLowerSegment 822513920 822579456 (82248565478391 / 100000) (82255109760159 / 100000) := by
  exact
    packedTile32768 822513920 822579456 13 3188 28679 30 _ _ (1026393 / 50000) (2052789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822579456 :
    ThetaLowerSegment 822579456 822644992 (82255109760159 / 100000) (82261654067431 / 100000) := by
  exact
    packedTile32768 822579456 822644992 13 3188 28680 30 _ _ (1026397 / 50000) (2052797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822644992 :
    ThetaLowerSegment 822644992 822710528 (82261654067431 / 100000) (82268192241801 / 100000) := by
  exact
    packedTile32768 822644992 822710528 13 3185 28681 30 _ _ (1026401 / 50000) (410561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822710528 :
    ThetaLowerSegment 822710528 822776064 (82268192241801 / 100000) (82274529266271 / 100000) := by
  exact
    packedTile32768 822710528 822776064 13 3087 28682 30 _ _ (205281 / 10000) (2052813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822776064 :
    ThetaLowerSegment 822776064 822841600 (82274529266271 / 100000) (82281122917687 / 100000) := by
  exact
    packedTile32768 822776064 822841600 13 3212 28684 30 _ _ (1026409 / 50000) (2052821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822841600 :
    ThetaLowerSegment 822841600 822907136 (82281122917687 / 100000) (82287679643931 / 100000) := by
  exact
    packedTile32768 822841600 822907136 13 3194 28685 30 _ _ (1026413 / 50000) (2052829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822907136 :
    ThetaLowerSegment 822907136 822972672 (82287679643931 / 100000) (82294254871233 / 100000) := by
  exact
    packedTile32768 822907136 822972672 13 3203 28686 30 _ _ (1026417 / 50000) (2052837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell822972672 :
    ThetaLowerSegment 822972672 823038208 (82294254871233 / 100000) (82300793173003 / 100000) := by
  exact
    packedTile32768 822972672 823038208 13 3185 28687 30 _ _ (1026421 / 50000) (410569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823038208 :
    ThetaLowerSegment 823038208 823103744 (82300793173003 / 100000) (82307280179003 / 100000) := by
  exact
    packedTile32768 823038208 823103744 13 3160 28688 30 _ _ (41057 / 2000) (2052853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823103744 :
    ThetaLowerSegment 823103744 823169280 (82307280179003 / 100000) (82313812373159 / 100000) := by
  exact
    packedTile32768 823103744 823169280 13 3182 28689 30 _ _ (1026429 / 50000) (2052861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823169280 :
    ThetaLowerSegment 823169280 823234816 (82313812373159 / 100000) (82320422601679 / 100000) := by
  exact
    packedTile32768 823169280 823234816 13 3220 28690 30 _ _ (1026433 / 50000) (2052869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823234816 :
    ThetaLowerSegment 823234816 823300352 (82320422601679 / 100000) (82326874784661 / 100000) := by
  exact
    packedTile32768 823234816 823300352 13 3143 28692 30 _ _ (1026437 / 50000) (2052877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823300352 :
    ThetaLowerSegment 823300352 823365888 (82326874784661 / 100000) (82333513805049 / 100000) := by
  exact
    packedTile32768 823300352 823365888 13 3234 28693 30 _ _ (1026441 / 50000) (410577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823365888 :
    ThetaLowerSegment 823365888 823431424 (82333513805049 / 100000) (82340122057959 / 100000) := by
  exact
    packedTile32768 823365888 823431424 13 3219 28694 30 _ _ (205289 / 10000) (2052893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823431424 :
    ThetaLowerSegment 823431424 823496960 (82340122057959 / 100000) (16469332928777 / 20000) := by
  exact
    packedTile32768 823431424 823496960 13 3187 28695 30 _ _ (1026449 / 50000) (2052901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823496960 :
    ThetaLowerSegment 823496960 823562496 (16469332928777 / 20000) (16470638576993 / 20000) := by
  exact
    packedTile32768 823496960 823562496 13 3180 28696 30 _ _ (1026453 / 50000) (2052909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823562496 :
    ThetaLowerSegment 823562496 823628032 (16470638576993 / 20000) (8235989564591 / 10000) := by
  exact
    packedTile32768 823562496 823628032 13 3265 28697 30 _ _ (2052913 / 100000) (513229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823628032 :
    ThetaLowerSegment 823628032 823693568 (8235989564591 / 10000) (2573951646112 / 3125) := by
  exact
    packedTile32768 823628032 823693568 13 3194 28698 30 _ _ (2052921 / 100000) (513231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823693568 :
    ThetaLowerSegment 823693568 823759104 (2573951646112 / 3125) (82372983042733 / 100000) := by
  exact
    packedTile32768 823693568 823759104 13 3181 28700 30 _ _ (2052929 / 100000) (513233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823759104 :
    ThetaLowerSegment 823759104 823824640 (82372983042733 / 100000) (82379593499873 / 100000) := by
  exact
    packedTile32768 823759104 823824640 13 3220 28701 30 _ _ (2052937 / 100000) (102647 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823824640 :
    ThetaLowerSegment 823824640 823890176 (82379593499873 / 100000) (82386142394423 / 100000) := by
  exact
    packedTile32768 823824640 823890176 13 3190 28702 30 _ _ (410589 / 20000) (513237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823890176 :
    ThetaLowerSegment 823890176 823955712 (82386142394423 / 100000) (82392633831809 / 100000) := by
  exact
    packedTile32768 823890176 823955712 13 3162 28703 30 _ _ (2052953 / 100000) (513239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell823955712 :
    ThetaLowerSegment 823955712 824021248 (82392633831809 / 100000) (82399293637293 / 100000) := by
  exact
    packedTile32768 823955712 824021248 13 3244 28704 30 _ _ (2052961 / 100000) (513241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824021248 :
    ThetaLowerSegment 824021248 824086784 (82399293637293 / 100000) (3296232718911 / 4000) := by
  exact
    packedTile32768 824021248 824086784 13 3178 28705 30 _ _ (2052969 / 100000) (513243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824086784 :
    ThetaLowerSegment 824086784 824152320 (3296232718911 / 4000) (82412247896739 / 100000) := by
  exact
    packedTile32768 824086784 824152320 13 3132 28706 30 _ _ (2052977 / 100000) (102649 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824152320 :
    ThetaLowerSegment 824152320 824217856 (82412247896739 / 100000) (20604696663491 / 25000) := by
  exact
    packedTile32768 824152320 824217856 13 3185 28708 30 _ _ (410597 / 20000) (513247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824217856 :
    ThetaLowerSegment 824217856 824283392 (20604696663491 / 25000) (10303156184491 / 12500) := by
  exact
    packedTile32768 824217856 824283392 13 3148 28709 30 _ _ (2052993 / 100000) (513249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824283392 :
    ThetaLowerSegment 824283392 824348928 (10303156184491 / 12500) (82431784178111 / 100000) := by
  exact
    packedTile32768 824283392 824348928 13 3183 28710 30 _ _ (2053001 / 100000) (513251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824348928 :
    ThetaLowerSegment 824348928 824414464 (82431784178111 / 100000) (41219138922789 / 50000) := by
  exact
    packedTile32768 824348928 824414464 13 3163 28711 30 _ _ (2053009 / 100000) (513253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824414464 :
    ThetaLowerSegment 824414464 824480000 (41219138922789 / 50000) (82444841340927 / 100000) := by
  exact
    packedTile32768 824414464 824480000 13 3197 28712 30 _ _ (2053017 / 100000) (102651 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824480000 :
    ThetaLowerSegment 824480000 824545536 (82444841340927 / 100000) (82451374066477 / 100000) := by
  exact
    packedTile32768 824480000 824545536 13 3182 28713 30 _ _ (82121 / 4000) (513257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824545536 :
    ThetaLowerSegment 824545536 824611072 (82451374066477 / 100000) (82457993044869 / 100000) := by
  exact
    packedTile32768 824545536 824611072 13 3224 28714 30 _ _ (2053033 / 100000) (513259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824611072 :
    ThetaLowerSegment 824611072 824676608 (82457993044869 / 100000) (82464521715249 / 100000) := by
  exact
    packedTile32768 824611072 824676608 13 3180 28716 30 _ _ (2053041 / 100000) (513261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824676608 :
    ThetaLowerSegment 824676608 824742144 (82464521715249 / 100000) (82470947758619 / 100000) := by
  exact
    packedTile32768 824676608 824742144 13 3130 28717 30 _ _ (2053049 / 100000) (513263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824742144 :
    ThetaLowerSegment 824742144 824807680 (82470947758619 / 100000) (82477357402573 / 100000) := by
  exact
    packedTile32768 824742144 824807680 13 3122 28718 30 _ _ (2053057 / 100000) (102653 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824807680 :
    ThetaLowerSegment 824807680 824873216 (82477357402573 / 100000) (82483947741223 / 100000) := by
  exact
    packedTile32768 824807680 824873216 13 3210 28719 30 _ _ (410613 / 20000) (513267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824873216 :
    ThetaLowerSegment 824873216 824938752 (82483947741223 / 100000) (82490447770341 / 100000) := by
  exact
    packedTile32768 824873216 824938752 13 3166 28720 30 _ _ (2053073 / 100000) (513269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell824938752 :
    ThetaLowerSegment 824938752 825004288 (82490447770341 / 100000) (82497142864221 / 100000) := by
  exact
    packedTile32768 824938752 825004288 13 3261 28721 30 _ _ (51327 / 2500) (2053083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825004288 :
    ThetaLowerSegment 825004288 825069824 (82497142864221 / 100000) (82503597772893 / 100000) := by
  exact
    packedTile32768 825004288 825069824 13 3144 28722 30 _ _ (64159 / 3125) (2053091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825069824 :
    ThetaLowerSegment 825069824 825135360 (82503597772893 / 100000) (82510097874829 / 100000) := by
  exact
    packedTile32768 825069824 825135360 13 3166 28724 30 _ _ (256637 / 12500) (2053099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825135360 :
    ThetaLowerSegment 825135360 825200896 (82510097874829 / 100000) (82516733506957 / 100000) := by
  exact
    packedTile32768 825135360 825200896 13 3232 28725 30 _ _ (128319 / 6250) (2053107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825200896 :
    ThetaLowerSegment 825200896 825266432 (82516733506957 / 100000) (82523432811413 / 100000) := by
  exact
    packedTile32768 825200896 825266432 13 3263 28726 30 _ _ (256639 / 12500) (410623 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825266432 :
    ThetaLowerSegment 825266432 825331968 (82523432811413 / 100000) (82529959679893 / 100000) := by
  exact
    packedTile32768 825266432 825331968 13 3179 28727 30 _ _ (12832 / 625) (2053123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825331968 :
    ThetaLowerSegment 825331968 825397504 (82529959679893 / 100000) (82536523530109 / 100000) := by
  exact
    packedTile32768 825331968 825397504 13 3197 28728 30 _ _ (256641 / 12500) (2053131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825397504 :
    ThetaLowerSegment 825397504 825463040 (82536523530109 / 100000) (16508627336233 / 20000) := by
  exact
    packedTile32768 825397504 825463040 13 3221 28729 30 _ _ (128321 / 6250) (2053139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825463040 :
    ThetaLowerSegment 825463040 825528576 (16508627336233 / 20000) (82549667732229 / 100000) := by
  exact
    packedTile32768 825463040 825528576 13 3181 28730 30 _ _ (256643 / 12500) (2053147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825528576 :
    ThetaLowerSegment 825528576 825594112 (82549667732229 / 100000) (82556207021349 / 100000) := by
  exact
    packedTile32768 825528576 825594112 13 3185 28732 30 _ _ (64161 / 3125) (410631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825594112 :
    ThetaLowerSegment 825594112 825659648 (82556207021349 / 100000) (82562756601749 / 100000) := by
  exact
    packedTile32768 825594112 825659648 13 3190 28733 30 _ _ (51329 / 2500) (2053163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825659648 :
    ThetaLowerSegment 825659648 825725184 (82562756601749 / 100000) (82569308260837 / 100000) := by
  exact
    packedTile32768 825659648 825725184 13 3191 28734 30 _ _ (128323 / 6250) (2053171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825725184 :
    ThetaLowerSegment 825725184 825790720 (82569308260837 / 100000) (82575913328029 / 100000) := by
  exact
    packedTile32768 825725184 825790720 13 3217 28735 30 _ _ (256647 / 12500) (2053179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825790720 :
    ThetaLowerSegment 825790720 825856256 (82575913328029 / 100000) (82582417814941 / 100000) := by
  exact
    packedTile32768 825790720 825856256 13 3168 28736 30 _ _ (64162 / 3125) (2053187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825856256 :
    ThetaLowerSegment 825856256 825921792 (82582417814941 / 100000) (82588914114429 / 100000) := by
  exact
    packedTile32768 825856256 825921792 13 3164 28737 30 _ _ (256649 / 12500) (410639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825921792 :
    ThetaLowerSegment 825921792 825987328 (82588914114429 / 100000) (82595521312029 / 100000) := by
  exact
    packedTile32768 825921792 825987328 13 3218 28738 30 _ _ (5133 / 250) (2053203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell825987328 :
    ThetaLowerSegment 825987328 826052864 (82595521312029 / 100000) (10325252464023 / 12500) := by
  exact
    packedTile32768 825987328 826052864 13 3165 28739 30 _ _ (2053207 / 100000) (205321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826052864 :
    ThetaLowerSegment 826052864 826118400 (10325252464023 / 12500) (41304305266167 / 50000) := by
  exact
    packedTile32768 826052864 826118400 13 3210 28741 30 _ _ (410643 / 20000) (1026609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826118400 :
    ThetaLowerSegment 826118400 826183936 (41304305266167 / 50000) (20653788025203 / 25000) := by
  exact
    packedTile32768 826118400 826183936 13 3186 28742 30 _ _ (2053223 / 100000) (1026613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826183936 :
    ThetaLowerSegment 826183936 826249472 (20653788025203 / 25000) (82621642364003 / 100000) := by
  exact
    packedTile32768 826183936 826249472 13 3161 28743 30 _ _ (2053231 / 100000) (1026617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826249472 :
    ThetaLowerSegment 826249472 826315008 (82621642364003 / 100000) (2582132353576 / 3125) := by
  exact
    packedTile32768 826249472 826315008 13 3211 28744 30 _ _ (2053239 / 100000) (1026621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826315008 :
    ThetaLowerSegment 826315008 826380544 (2582132353576 / 3125) (41317441864109 / 50000) := by
  exact
    packedTile32768 826315008 826380544 13 3238 28745 30 _ _ (2053247 / 100000) (8213 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826380544 :
    ThetaLowerSegment 826380544 826446080 (41317441864109 / 50000) (82641398706333 / 100000) := by
  exact
    packedTile32768 826380544 826446080 13 3173 28746 30 _ _ (410651 / 20000) (1026629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826446080 :
    ThetaLowerSegment 826446080 826511616 (82641398706333 / 100000) (82648043065401 / 100000) := by
  exact
    packedTile32768 826446080 826511616 13 3236 28747 30 _ _ (2053263 / 100000) (1026633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826511616 :
    ThetaLowerSegment 826511616 826577152 (82648043065401 / 100000) (2066365800301 / 2500) := by
  exact
    packedTile32768 826511616 826577152 13 3209 28749 30 _ _ (2053271 / 100000) (1026637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826577152 :
    ThetaLowerSegment 826577152 826642688 (2066365800301 / 2500) (16532213808341 / 20000) := by
  exact
    packedTile32768 826577152 826642688 13 3135 28750 30 _ _ (2053279 / 100000) (1026641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826642688 :
    ThetaLowerSegment 826642688 826708224 (16532213808341 / 20000) (5166727600837 / 6250) := by
  exact
    packedTile32768 826642688 826708224 13 3201 28751 30 _ _ (2053287 / 100000) (205329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826708224 :
    ThetaLowerSegment 826708224 826773760 (5166727600837 / 6250) (82674230637047 / 100000) := by
  exact
    packedTile32768 826708224 826773760 13 3209 28752 30 _ _ (410659 / 20000) (1026649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826773760 :
    ThetaLowerSegment 826773760 826839296 (82674230637047 / 100000) (82680698541497 / 100000) := by
  exact
    packedTile32768 826773760 826839296 13 3150 28753 30 _ _ (2053303 / 100000) (1026653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826839296 :
    ThetaLowerSegment 826839296 826904832 (82680698541497 / 100000) (20671807530947 / 25000) := by
  exact
    packedTile32768 826839296 826904832 13 3181 28754 30 _ _ (2053311 / 100000) (1026657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826904832 :
    ThetaLowerSegment 826904832 826970368 (20671807530947 / 25000) (10336726119733 / 12500) := by
  exact
    packedTile32768 826904832 826970368 13 3204 28755 30 _ _ (2053319 / 100000) (1026661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell826970368 :
    ThetaLowerSegment 826970368 827035904 (10336726119733 / 12500) (2584387119199 / 3125) := by
  exact
    packedTile32768 826970368 827035904 13 3204 28757 30 _ _ (1026663 / 50000) (2053329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827035904 :
    ThetaLowerSegment 827035904 827101440 (2584387119199 / 3125) (20676730380789 / 25000) := by
  exact
    packedTile32768 827035904 827101440 13 3182 28758 30 _ _ (1026667 / 50000) (2053337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827101440 :
    ThetaLowerSegment 827101440 827166976 (20676730380789 / 25000) (20678336094233 / 25000) := by
  exact
    packedTile32768 827101440 827166976 13 3128 28759 30 _ _ (1026671 / 50000) (410669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827166976 :
    ThetaLowerSegment 827166976 827232512 (20678336094233 / 25000) (20679999307733 / 25000) := by
  exact
    packedTile32768 827166976 827232512 13 3240 28760 30 _ _ (41067 / 2000) (2053353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827232512 :
    ThetaLowerSegment 827232512 827298048 (20679999307733 / 25000) (41363250107859 / 50000) := by
  exact
    packedTile32768 827232512 827298048 13 3167 28761 30 _ _ (1026679 / 50000) (2053361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827298048 :
    ThetaLowerSegment 827298048 827363584 (41363250107859 / 50000) (41366613521367 / 50000) := by
  exact
    packedTile32768 827298048 827363584 13 3276 28762 30 _ _ (1026683 / 50000) (2053369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827363584 :
    ThetaLowerSegment 827363584 827429120 (41366613521367 / 50000) (41369880439401 / 50000) := by
  exact
    packedTile32768 827363584 827429120 13 3182 28763 30 _ _ (1026687 / 50000) (2053377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827429120 :
    ThetaLowerSegment 827429120 827494656 (41369880439401 / 50000) (41373176117511 / 50000) := by
  exact
    packedTile32768 827429120 827494656 13 3210 28765 30 _ _ (1026691 / 50000) (410677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827494656 :
    ThetaLowerSegment 827494656 827560192 (41373176117511 / 50000) (41376393779641 / 50000) := by
  exact
    packedTile32768 827494656 827560192 13 3134 28766 30 _ _ (205339 / 10000) (2053393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827560192 :
    ThetaLowerSegment 827560192 827625728 (41376393779641 / 50000) (20689832934677 / 25000) := by
  exact
    packedTile32768 827560192 827625728 13 3187 28767 30 _ _ (1026699 / 50000) (2053401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827625728 :
    ThetaLowerSegment 827625728 827691264 (20689832934677 / 25000) (5172871224951 / 6250) := by
  exact
    packedTile32768 827625728 827691264 13 3218 28768 30 _ _ (1026703 / 50000) (2053409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827691264 :
    ThetaLowerSegment 827691264 827756800 (5172871224951 / 6250) (41386250128473 / 50000) := by
  exact
    packedTile32768 827691264 827756800 13 3195 28769 30 _ _ (1026707 / 50000) (2053417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827756800 :
    ThetaLowerSegment 827756800 827822336 (41386250128473 / 50000) (41389473999443 / 50000) := by
  exact
    packedTile32768 827756800 827822336 13 3140 28770 30 _ _ (2053421 / 100000) (128339 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827822336 :
    ThetaLowerSegment 827822336 827887872 (41389473999443 / 50000) (82785323895931 / 100000) := by
  exact
    packedTile32768 827822336 827887872 13 3105 28771 30 _ _ (2053429 / 100000) (256679 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827887872 :
    ThetaLowerSegment 827887872 827953408 (82785323895931 / 100000) (82791931856197 / 100000) := by
  exact
    packedTile32768 827887872 827953408 13 3218 28773 30 _ _ (2053437 / 100000) (12834 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell827953408 :
    ThetaLowerSegment 827953408 828018944 (82791931856197 / 100000) (20699639580803 / 25000) := by
  exact
    packedTile32768 827953408 828018944 13 3227 28774 30 _ _ (410689 / 20000) (256681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828018944 :
    ThetaLowerSegment 828018944 828084480 (20699639580803 / 25000) (41402546205329 / 50000) := by
  exact
    packedTile32768 828018944 828084480 13 3182 28775 30 _ _ (2053453 / 100000) (128341 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828084480 :
    ThetaLowerSegment 828084480 828150016 (41402546205329 / 50000) (82811587507801 / 100000) := by
  exact
    packedTile32768 828084480 828150016 13 3163 28776 30 _ _ (2053461 / 100000) (256683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828150016 :
    ThetaLowerSegment 828150016 828215552 (82811587507801 / 100000) (41409076224097 / 50000) := by
  exact
    packedTile32768 828150016 828215552 13 3197 28777 30 _ _ (2053469 / 100000) (64171 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828215552 :
    ThetaLowerSegment 828215552 828281088 (41409076224097 / 50000) (4141246240767 / 5000) := by
  exact
    packedTile32768 828215552 828281088 13 3298 28778 30 _ _ (2053477 / 100000) (51337 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828281088 :
    ThetaLowerSegment 828281088 828346624 (4141246240767 / 5000) (16566288104649 / 20000) := by
  exact
    packedTile32768 828281088 828346624 13 3173 28779 30 _ _ (410697 / 20000) (128343 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828346624 :
    ThetaLowerSegment 828346624 828412160 (16566288104649 / 20000) (82837987058929 / 100000) := by
  exact
    packedTile32768 828346624 828412160 13 3188 28781 30 _ _ (2053493 / 100000) (256687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828412160 :
    ThetaLowerSegment 828412160 828477696 (82837987058929 / 100000) (20711151373163 / 25000) := by
  exact
    packedTile32768 828412160 828477696 13 3223 28782 30 _ _ (2053501 / 100000) (64172 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828477696 :
    ThetaLowerSegment 828477696 828543232 (20711151373163 / 25000) (82851154132853 / 100000) := by
  exact
    packedTile32768 828477696 828543232 13 3189 28783 30 _ _ (2053509 / 100000) (256689 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828543232 :
    ThetaLowerSegment 828543232 828608768 (82851154132853 / 100000) (16571554112281 / 20000) := by
  exact
    packedTile32768 828543232 828608768 13 3222 28784 30 _ _ (513379 / 25000) (2053519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828608768 :
    ThetaLowerSegment 828608768 828674304 (16571554112281 / 20000) (82864272018389 / 100000) := by
  exact
    packedTile32768 828608768 828674304 13 3166 28785 30 _ _ (513381 / 25000) (2053527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828674304 :
    ThetaLowerSegment 828674304 828739840 (82864272018389 / 100000) (82870681091761 / 100000) := by
  exact
    packedTile32768 828674304 828739840 13 3121 28786 30 _ _ (513383 / 25000) (410707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828739840 :
    ThetaLowerSegment 828739840 828805376 (82870681091761 / 100000) (82877301704721 / 100000) := by
  exact
    packedTile32768 828739840 828805376 13 3224 28787 30 _ _ (102677 / 5000) (2053543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828805376 :
    ThetaLowerSegment 828805376 828870912 (82877301704721 / 100000) (82883842255101 / 100000) := by
  exact
    packedTile32768 828805376 828870912 13 3185 28788 30 _ _ (513387 / 25000) (2053551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828870912 :
    ThetaLowerSegment 828870912 828936448 (82883842255101 / 100000) (82890294528053 / 100000) := by
  exact
    packedTile32768 828870912 828936448 13 3142 28790 30 _ _ (513389 / 25000) (2053559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell828936448 :
    ThetaLowerSegment 828936448 829001984 (82890294528053 / 100000) (82896948075413 / 100000) := by
  exact
    packedTile32768 828936448 829001984 13 3240 28791 30 _ _ (513391 / 25000) (2053567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829001984 :
    ThetaLowerSegment 829001984 829067520 (82896948075413 / 100000) (82903537987961 / 100000) := by
  exact
    packedTile32768 829001984 829067520 13 3209 28792 30 _ _ (513393 / 25000) (82143 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829067520 :
    ThetaLowerSegment 829067520 829133056 (82903537987961 / 100000) (82910150515561 / 100000) := by
  exact
    packedTile32768 829067520 829133056 13 3220 28793 30 _ _ (102679 / 5000) (2053583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829133056 :
    ThetaLowerSegment 829133056 829198592 (82910150515561 / 100000) (16583343577997 / 20000) := by
  exact
    packedTile32768 829133056 829198592 13 3198 28794 30 _ _ (513397 / 25000) (2053591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829198592 :
    ThetaLowerSegment 829198592 829264128 (16583343577997 / 20000) (82923346897873 / 100000) := by
  exact
    packedTile32768 829198592 829264128 13 3228 28795 30 _ _ (513399 / 25000) (2053599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829264128 :
    ThetaLowerSegment 829264128 829329664 (82923346897873 / 100000) (41464892471639 / 50000) := by
  exact
    packedTile32768 829264128 829329664 13 3135 28796 30 _ _ (2053603 / 100000) (1026803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829329664 :
    ThetaLowerSegment 829329664 829395200 (41464892471639 / 50000) (82936444803751 / 100000) := by
  exact
    packedTile32768 829329664 829395200 13 3243 28798 30 _ _ (2053611 / 100000) (1026807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829395200 :
    ThetaLowerSegment 829395200 829460736 (82936444803751 / 100000) (4147154002337 / 5000) := by
  exact
    packedTile32768 829395200 829460736 13 3231 28799 30 _ _ (2053619 / 100000) (1026811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829460736 :
    ThetaLowerSegment 829460736 829526272 (4147154002337 / 5000) (4147478475403 / 5000) := by
  exact
    packedTile32768 829460736 829526272 13 3160 28800 30 _ _ (2053627 / 100000) (205363 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829526272 :
    ThetaLowerSegment 829526272 829591808 (4147478475403 / 5000) (16591200709303 / 20000) := by
  exact
    packedTile32768 829526272 829591808 13 3133 28801 30 _ _ (410727 / 20000) (1026819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829591808 :
    ThetaLowerSegment 829591808 829657344 (16591200709303 / 20000) (82962558774971 / 100000) := by
  exact
    packedTile32768 829591808 829657344 13 3192 28802 30 _ _ (2053643 / 100000) (1026823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829657344 :
    ThetaLowerSegment 829657344 829722880 (82962558774971 / 100000) (82969023668319 / 100000) := by
  exact
    packedTile32768 829657344 829722880 13 3148 28803 30 _ _ (2053651 / 100000) (1026827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829722880 :
    ThetaLowerSegment 829722880 829788416 (82969023668319 / 100000) (16595116611033 / 20000) := by
  exact
    packedTile32768 829722880 829788416 13 3194 28804 30 _ _ (2053659 / 100000) (1026831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829788416 :
    ThetaLowerSegment 829788416 829853952 (16595116611033 / 20000) (82982043891547 / 100000) := by
  exact
    packedTile32768 829788416 829853952 13 3146 28806 30 _ _ (2053667 / 100000) (205367 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829853952 :
    ThetaLowerSegment 829853952 829919488 (82982043891547 / 100000) (82988701905897 / 100000) := by
  exact
    packedTile32768 829853952 829919488 13 3242 28807 30 _ _ (82147 / 4000) (1026839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829919488 :
    ThetaLowerSegment 829919488 829985024 (82988701905897 / 100000) (82995173057879 / 100000) := by
  exact
    packedTile32768 829919488 829985024 13 3151 28808 30 _ _ (1026841 / 50000) (410737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell829985024 :
    ThetaLowerSegment 829985024 830050560 (82995173057879 / 100000) (83001753080639 / 100000) := by
  exact
    packedTile32768 829985024 830050560 13 3204 28809 30 _ _ (205369 / 10000) (2053693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830050560 :
    ThetaLowerSegment 830050560 830116096 (83001753080639 / 100000) (83008269464393 / 100000) := by
  exact
    packedTile32768 830050560 830116096 13 3173 28810 30 _ _ (1026849 / 50000) (2053701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830116096 :
    ThetaLowerSegment 830116096 830181632 (83008269464393 / 100000) (83014890612537 / 100000) := by
  exact
    packedTile32768 830116096 830181632 13 3224 28811 30 _ _ (1026853 / 50000) (2053709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830181632 :
    ThetaLowerSegment 830181632 830247168 (83014890612537 / 100000) (83021345435639 / 100000) := by
  exact
    packedTile32768 830181632 830247168 13 3143 28812 30 _ _ (1026857 / 50000) (2053717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830247168 :
    ThetaLowerSegment 830247168 830312704 (83021345435639 / 100000) (83027909131151 / 100000) := by
  exact
    packedTile32768 830247168 830312704 13 3196 28814 30 _ _ (1026861 / 50000) (82149 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830312704 :
    ThetaLowerSegment 830312704 830378240 (83027909131151 / 100000) (83034567323811 / 100000) := by
  exact
    packedTile32768 830312704 830378240 13 3242 28815 30 _ _ (205373 / 10000) (2053733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830378240 :
    ThetaLowerSegment 830378240 830443776 (83034567323811 / 100000) (83041241972311 / 100000) := by
  exact
    packedTile32768 830378240 830443776 13 3250 28816 30 _ _ (1026869 / 50000) (2053741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830443776 :
    ThetaLowerSegment 830443776 830509312 (83041241972311 / 100000) (83047746185893 / 100000) := by
  exact
    packedTile32768 830443776 830509312 13 3167 28817 30 _ _ (1026873 / 50000) (2053749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830509312 :
    ThetaLowerSegment 830509312 830574848 (83047746185893 / 100000) (10381792598347 / 12500) := by
  exact
    packedTile32768 830509312 830574848 13 3211 28818 30 _ _ (2053753 / 100000) (513439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830574848 :
    ThetaLowerSegment 830574848 830640384 (10381792598347 / 12500) (8306090049941 / 10000) := by
  exact
    packedTile32768 830574848 830640384 13 3194 28819 30 _ _ (2053761 / 100000) (513441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830640384 :
    ThetaLowerSegment 830640384 830705920 (8306090049941 / 10000) (83067507474283 / 100000) := by
  exact
    packedTile32768 830640384 830705920 13 3217 28820 30 _ _ (2053769 / 100000) (513443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830705920 :
    ThetaLowerSegment 830705920 830771456 (83067507474283 / 100000) (83074075453129 / 100000) := by
  exact
    packedTile32768 830705920 830771456 13 3198 28821 30 _ _ (2053777 / 100000) (102689 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830771456 :
    ThetaLowerSegment 830771456 830836992 (83074075453129 / 100000) (83080606489429 / 100000) := by
  exact
    packedTile32768 830771456 830836992 13 3180 28823 30 _ _ (410757 / 20000) (513447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830836992 :
    ThetaLowerSegment 830836992 830902528 (83080606489429 / 100000) (83086969140143 / 100000) := by
  exact
    packedTile32768 830836992 830902528 13 3098 28824 30 _ _ (2053793 / 100000) (513449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830902528 :
    ThetaLowerSegment 830902528 830968064 (83086969140143 / 100000) (83093528980537 / 100000) := by
  exact
    packedTile32768 830902528 830968064 13 3194 28825 30 _ _ (2053801 / 100000) (513451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell830968064 :
    ThetaLowerSegment 830968064 831033600 (83093528980537 / 100000) (83099998478887 / 100000) := by
  exact
    packedTile32768 830968064 831033600 13 3150 28826 30 _ _ (2053809 / 100000) (513453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831033600 :
    ThetaLowerSegment 831033600 831099136 (83099998478887 / 100000) (83106595339091 / 100000) := by
  exact
    packedTile32768 831033600 831099136 13 3212 28827 30 _ _ (2053817 / 100000) (102691 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831099136 :
    ThetaLowerSegment 831099136 831164672 (83106595339091 / 100000) (83113110068819 / 100000) := by
  exact
    packedTile32768 831099136 831164672 13 3172 28828 30 _ _ (64182 / 3125) (2053827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831164672 :
    ThetaLowerSegment 831164672 831230208 (83113110068819 / 100000) (83119826099459 / 100000) := by
  exact
    packedTile32768 831164672 831230208 13 3270 28829 30 _ _ (256729 / 12500) (410767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831230208 :
    ThetaLowerSegment 831230208 831295744 (83119826099459 / 100000) (83126579125379 / 100000) := by
  exact
    packedTile32768 831230208 831295744 13 3288 28831 30 _ _ (25673 / 1250) (2053843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831295744 :
    ThetaLowerSegment 831295744 831361280 (83126579125379 / 100000) (83132983023443 / 100000) := by
  exact
    packedTile32768 831295744 831361280 13 3118 28832 30 _ _ (256731 / 12500) (2053851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831361280 :
    ThetaLowerSegment 831361280 831426816 (83132983023443 / 100000) (83139504016243 / 100000) := by
  exact
    packedTile32768 831361280 831426816 13 3175 28833 30 _ _ (64183 / 3125) (2053859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831426816 :
    ThetaLowerSegment 831426816 831492352 (83139504016243 / 100000) (16629193916023 / 20000) := by
  exact
    packedTile32768 831426816 831492352 13 3148 28834 30 _ _ (256733 / 12500) (2053867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831492352 :
    ThetaLowerSegment 831492352 831557888 (16629193916023 / 20000) (83152441330787 / 100000) := by
  exact
    packedTile32768 831492352 831557888 13 3151 28835 30 _ _ (128367 / 6250) (16431 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831557888 :
    ThetaLowerSegment 831557888 831623424 (83152441330787 / 100000) (83159083578707 / 100000) := by
  exact
    packedTile32768 831557888 831623424 13 3234 28836 30 _ _ (51347 / 2500) (2053883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831623424 :
    ThetaLowerSegment 831623424 831688960 (83159083578707 / 100000) (83165520463699 / 100000) := by
  exact
    packedTile32768 831623424 831688960 13 3134 28837 30 _ _ (64184 / 3125) (2053891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831688960 :
    ThetaLowerSegment 831688960 831754496 (83165520463699 / 100000) (10396504170593 / 12500) := by
  exact
    packedTile32768 831688960 831754496 13 3171 28839 30 _ _ (410779 / 20000) (1026949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831754496 :
    ThetaLowerSegment 831754496 831820032 (10396504170593 / 12500) (83178542183351 / 100000) := by
  exact
    packedTile32768 831754496 831820032 13 3169 28840 30 _ _ (2053903 / 100000) (1026953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831820032 :
    ThetaLowerSegment 831820032 831885568 (83178542183351 / 100000) (83185172208059 / 100000) := by
  exact
    packedTile32768 831820032 831885568 13 3228 28841 30 _ _ (2053911 / 100000) (1026957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831885568 :
    ThetaLowerSegment 831885568 831951104 (83185172208059 / 100000) (16638342377231 / 20000) := by
  exact
    packedTile32768 831885568 831951104 13 3184 28842 30 _ _ (2053919 / 100000) (1026961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell831951104 :
    ThetaLowerSegment 831951104 832016640 (16638342377231 / 20000) (2599944527771 / 3125) := by
  exact
    packedTile32768 831951104 832016640 13 3171 28843 30 _ _ (2053927 / 100000) (205393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832016640 :
    ThetaLowerSegment 832016640 832082176 (2599944527771 / 3125) (10400614062629 / 12500) := by
  exact
    packedTile32768 832016640 832082176 13 3256 28844 30 _ _ (410787 / 20000) (1026969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832082176 :
    ThetaLowerSegment 832082176 832147712 (10400614062629 / 12500) (83211470741031 / 100000) := by
  exact
    packedTile32768 832082176 832147712 13 3193 28845 30 _ _ (2053943 / 100000) (1026973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832147712 :
    ThetaLowerSegment 832147712 832213248 (83211470741031 / 100000) (41608998071679 / 50000) := by
  exact
    packedTile32768 832147712 832213248 13 3177 28846 30 _ _ (2053951 / 100000) (1026977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832213248 :
    ThetaLowerSegment 832213248 832278784 (41608998071679 / 50000) (41612259756983 / 50000) := by
  exact
    packedTile32768 832213248 832278784 13 3176 28848 30 _ _ (1026979 / 50000) (2053961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832278784 :
    ThetaLowerSegment 832278784 832344320 (41612259756983 / 50000) (20807759187021 / 25000) := by
  exact
    packedTile32768 832278784 832344320 13 3173 28849 30 _ _ (1026983 / 50000) (2053969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832344320 :
    ThetaLowerSegment 832344320 832409856 (20807759187021 / 25000) (20809402366221 / 25000) := by
  exact
    packedTile32768 832344320 832409856 13 3200 28850 30 _ _ (1026987 / 50000) (2053977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832409856 :
    ThetaLowerSegment 832409856 832475392 (20809402366221 / 25000) (5202755482757 / 6250) := by
  exact
    packedTile32768 832409856 832475392 13 3154 28851 30 _ _ (1026991 / 50000) (410797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832475392 :
    ThetaLowerSegment 832475392 832540928 (5202755482757 / 6250) (20812678473963 / 25000) := by
  exact
    packedTile32768 832475392 832540928 13 3226 28852 30 _ _ (205399 / 10000) (2053993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832540928 :
    ThetaLowerSegment 832540928 832606464 (20812678473963 / 25000) (2601789567171 / 3125) := by
  exact
    packedTile32768 832540928 832606464 13 3190 28853 30 _ _ (1026999 / 50000) (2054001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832606464 :
    ThetaLowerSegment 832606464 832672000 (2601789567171 / 3125) (41631877377213 / 50000) := by
  exact
    packedTile32768 832606464 832672000 13 3159 28854 30 _ _ (1027003 / 50000) (2054009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832672000 :
    ThetaLowerSegment 832672000 832737536 (41631877377213 / 50000) (41635145313487 / 50000) := by
  exact
    packedTile32768 832672000 832737536 13 3182 28856 30 _ _ (1027007 / 50000) (2054017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832737536 :
    ThetaLowerSegment 832737536 832803072 (41635145313487 / 50000) (83277013437707 / 100000) := by
  exact
    packedTile32768 832737536 832803072 13 3273 28857 30 _ _ (2054021 / 100000) (256753 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832803072 :
    ThetaLowerSegment 832803072 832868608 (83277013437707 / 100000) (83283565790217 / 100000) := by
  exact
    packedTile32768 832803072 832868608 13 3190 28858 30 _ _ (2054029 / 100000) (128377 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832868608 :
    ThetaLowerSegment 832868608 832934144 (83283565790217 / 100000) (83290089411729 / 100000) := by
  exact
    packedTile32768 832868608 832934144 13 3176 28859 30 _ _ (2054037 / 100000) (51351 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832934144 :
    ThetaLowerSegment 832934144 832999680 (83290089411729 / 100000) (41648352745337 / 50000) := by
  exact
    packedTile32768 832934144 832999680 13 3221 28860 30 _ _ (410809 / 20000) (64189 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell832999680 :
    ThetaLowerSegment 832999680 833065216 (41648352745337 / 50000) (83303264081903 / 100000) := by
  exact
    packedTile32768 832999680 833065216 13 3193 28861 30 _ _ (2054053 / 100000) (256757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833065216 :
    ThetaLowerSegment 833065216 833130752 (83303264081903 / 100000) (20827463890913 / 25000) := by
  exact
    packedTile32768 833065216 833130752 13 3209 28862 30 _ _ (2054061 / 100000) (128379 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833130752 :
    ThetaLowerSegment 833130752 833196288 (20827463890913 / 25000) (83316373124589 / 100000) := by
  exact
    packedTile32768 833130752 833196288 13 3173 28864 30 _ _ (2054069 / 100000) (256759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833196288 :
    ThetaLowerSegment 833196288 833261824 (83316373124589 / 100000) (83322751030569 / 100000) := by
  exact
    packedTile32768 833196288 833261824 13 3105 28865 30 _ _ (513519 / 25000) (2054079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833261824 :
    ThetaLowerSegment 833261824 833327360 (83322751030569 / 100000) (83329319991201 / 100000) := by
  exact
    packedTile32768 833261824 833327360 13 3198 28866 30 _ _ (513521 / 25000) (2054087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833327360 :
    ThetaLowerSegment 833327360 833392896 (83329319991201 / 100000) (83335909518337 / 100000) := by
  exact
    packedTile32768 833327360 833392896 13 3208 28867 30 _ _ (513523 / 25000) (410819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833392896 :
    ThetaLowerSegment 833392896 833458432 (83335909518337 / 100000) (83342603830237 / 100000) := by
  exact
    packedTile32768 833392896 833458432 13 3259 28868 30 _ _ (20541 / 1000) (2054103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833458432 :
    ThetaLowerSegment 833458432 833523968 (83342603830237 / 100000) (83349133839569 / 100000) := by
  exact
    packedTile32768 833458432 833523968 13 3179 28869 30 _ _ (513527 / 25000) (2054111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833523968 :
    ThetaLowerSegment 833523968 833589504 (83349133839569 / 100000) (83355846690657 / 100000) := by
  exact
    packedTile32768 833523968 833589504 13 3268 28870 30 _ _ (513529 / 25000) (2054119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833589504 :
    ThetaLowerSegment 833589504 833655040 (83355846690657 / 100000) (83362553405517 / 100000) := by
  exact
    packedTile32768 833589504 833655040 13 3265 28871 30 _ _ (513531 / 25000) (2054127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833655040 :
    ThetaLowerSegment 833655040 833720576 (83362553405517 / 100000) (83369030083713 / 100000) := by
  exact
    packedTile32768 833655040 833720576 13 3153 28873 30 _ _ (513533 / 25000) (410827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833720576 :
    ThetaLowerSegment 833720576 833786112 (83369030083713 / 100000) (83375541704343 / 100000) := by
  exact
    packedTile32768 833720576 833786112 13 3170 28874 30 _ _ (2054139 / 100000) (1027071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833786112 :
    ThetaLowerSegment 833786112 833851648 (83375541704343 / 100000) (4169104824371 / 5000) := by
  exact
    packedTile32768 833786112 833851648 13 3191 28875 30 _ _ (2054147 / 100000) (41083 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833851648 :
    ThetaLowerSegment 833851648 833917184 (4169104824371 / 5000) (16677704787683 / 20000) := by
  exact
    packedTile32768 833851648 833917184 13 3129 28876 30 _ _ (410831 / 20000) (1027079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833917184 :
    ThetaLowerSegment 833917184 833982720 (16677704787683 / 20000) (83395113693319 / 100000) := by
  exact
    packedTile32768 833917184 833982720 13 3208 28877 30 _ _ (2054163 / 100000) (1027083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell833982720 :
    ThetaLowerSegment 833982720 834048256 (83395113693319 / 100000) (2606302399052 / 3125) := by
  exact
    packedTile32768 833982720 834048256 13 3195 28878 30 _ _ (2054171 / 100000) (1027087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834048256 :
    ThetaLowerSegment 834048256 834113792 (2606302399052 / 3125) (83408215221421 / 100000) := by
  exact
    packedTile32768 834048256 834113792 13 3183 28879 30 _ _ (2054179 / 100000) (1027091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834113792 :
    ThetaLowerSegment 834113792 834179328 (83408215221421 / 100000) (20853687397567 / 25000) := by
  exact
    packedTile32768 834113792 834179328 13 3181 28881 30 _ _ (2054187 / 100000) (205419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834179328 :
    ThetaLowerSegment 834179328 834244864 (20853687397567 / 25000) (4171060809649 / 5000) := by
  exact
    packedTile32768 834179328 834244864 13 3148 28882 30 _ _ (1027097 / 50000) (2054197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834244864 :
    ThetaLowerSegment 834244864 834310400 (4171060809649 / 5000) (2607118297843 / 3125) := by
  exact
    packedTile32768 834244864 834310400 13 3198 28883 30 _ _ (1027101 / 50000) (410841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834310400 :
    ThetaLowerSegment 834310400 834375936 (2607118297843 / 3125) (41717229829633 / 50000) := by
  exact
    packedTile32768 834310400 834375936 13 3249 28884 30 _ _ (205421 / 10000) (2054213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834375936 :
    ThetaLowerSegment 834375936 834441472 (41717229829633 / 50000) (2607531451626 / 3125) := by
  exact
    packedTile32768 834375936 834441472 13 3187 28885 30 _ _ (1027109 / 50000) (2054221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834441472 :
    ThetaLowerSegment 834441472 834507008 (2607531451626 / 3125) (10430956740921 / 12500) := by
  exact
    packedTile32768 834441472 834507008 13 3236 28886 30 _ _ (1027113 / 50000) (2054229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834507008 :
    ThetaLowerSegment 834507008 834572544 (10430956740921 / 12500) (8345423363887 / 10000) := by
  exact
    packedTile32768 834507008 834572544 13 3203 28887 30 _ _ (1027117 / 50000) (2054237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834572544 :
    ThetaLowerSegment 834572544 834638080 (8345423363887 / 10000) (20865191018547 / 25000) := by
  exact
    packedTile32768 834572544 834638080 13 3179 28888 30 _ _ (1027121 / 50000) (410849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834638080 :
    ThetaLowerSegment 834638080 834703616 (20865191018547 / 25000) (5216713226497 / 6250) := by
  exact
    packedTile32768 834638080 834703616 13 3236 28890 30 _ _ (2054249 / 100000) (513563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834703616 :
    ThetaLowerSegment 834703616 834769152 (5216713226497 / 6250) (41737011111489 / 50000) := by
  exact
    packedTile32768 834703616 834769152 13 3218 28891 30 _ _ (2054257 / 100000) (102713 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834769152 :
    ThetaLowerSegment 834769152 834834688 (41737011111489 / 50000) (10435067807511 / 12500) := by
  exact
    packedTile32768 834769152 834834688 13 3174 28892 30 _ _ (410853 / 20000) (513567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834834688 :
    ThetaLowerSegment 834834688 834900224 (10435067807511 / 12500) (83487060668317 / 100000) := by
  exact
    packedTile32768 834834688 834900224 13 3173 28893 30 _ _ (2054273 / 100000) (513569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834900224 :
    ThetaLowerSegment 834900224 834965760 (83487060668317 / 100000) (16698709617543 / 20000) := by
  exact
    packedTile32768 834900224 834965760 13 3158 28894 30 _ _ (2054281 / 100000) (513571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell834965760 :
    ThetaLowerSegment 834965760 835031296 (16698709617543 / 20000) (83500088943891 / 100000) := by
  exact
    packedTile32768 834965760 835031296 13 3184 28895 30 _ _ (2054289 / 100000) (513573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835031296 :
    ThetaLowerSegment 835031296 835096832 (83500088943891 / 100000) (83506562030587 / 100000) := by
  exact
    packedTile32768 835031296 835096832 13 3151 28896 30 _ _ (256787 / 12500) (2054299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835096832 :
    ThetaLowerSegment 835096832 835162368 (83506562030587 / 100000) (83513076228571 / 100000) := by
  exact
    packedTile32768 835096832 835162368 13 3171 28898 30 _ _ (64197 / 3125) (2054307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835162368 :
    ThetaLowerSegment 835162368 835227904 (83513076228571 / 100000) (83519721927891 / 100000) := by
  exact
    packedTile32768 835162368 835227904 13 3235 28899 30 _ _ (256789 / 12500) (410863 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835227904 :
    ThetaLowerSegment 835227904 835293440 (83519721927891 / 100000) (83526340946931 / 100000) := by
  exact
    packedTile32768 835227904 835293440 13 3222 28900 30 _ _ (25679 / 1250) (2054323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835293440 :
    ThetaLowerSegment 835293440 835358976 (83526340946931 / 100000) (16706573920263 / 20000) := by
  exact
    packedTile32768 835293440 835358976 13 3178 28901 30 _ _ (256791 / 12500) (2054331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835358976 :
    ThetaLowerSegment 835358976 835424512 (16706573920263 / 20000) (83539488671907 / 100000) := by
  exact
    packedTile32768 835358976 835424512 13 3222 28902 30 _ _ (64198 / 3125) (2054339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835424512 :
    ThetaLowerSegment 835424512 835490048 (83539488671907 / 100000) (83546000942387 / 100000) := by
  exact
    packedTile32768 835424512 835490048 13 3170 28903 30 _ _ (256793 / 12500) (2054347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835490048 :
    ThetaLowerSegment 835490048 835555584 (83546000942387 / 100000) (4177626997081 / 5000) := by
  exact
    packedTile32768 835490048 835555584 13 3183 28904 30 _ _ (2054351 / 100000) (1027177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835555584 :
    ThetaLowerSegment 835555584 835621120 (4177626997081 / 5000) (20889774363887 / 25000) := by
  exact
    packedTile32768 835555584 835621120 13 3192 28905 30 _ _ (2054359 / 100000) (1027181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835621120 :
    ThetaLowerSegment 835621120 835686656 (20889774363887 / 25000) (4178276997523 / 5000) := by
  exact
    packedTile32768 835621120 835686656 13 3136 28907 30 _ _ (2054367 / 100000) (205437 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835686656 :
    ThetaLowerSegment 835686656 835752192 (4178276997523 / 5000) (16714435527217 / 20000) := by
  exact
    packedTile32768 835686656 835752192 13 3231 28908 30 _ _ (3287 / 160) (1027189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835752192 :
    ThetaLowerSegment 835752192 835817728 (16714435527217 / 20000) (16715746223571 / 20000) := by
  exact
    packedTile32768 835752192 835817728 13 3190 28909 30 _ _ (2054383 / 100000) (1027193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835817728 :
    ThetaLowerSegment 835817728 835883264 (16715746223571 / 20000) (83585247646107 / 100000) := by
  exact
    packedTile32768 835817728 835883264 13 3172 28910 30 _ _ (2054391 / 100000) (1027197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835883264 :
    ThetaLowerSegment 835883264 835948800 (83585247646107 / 100000) (16718354482831 / 20000) := by
  exact
    packedTile32768 835883264 835948800 13 3176 28911 30 _ _ (1027199 / 50000) (2054401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell835948800 :
    ThetaLowerSegment 835948800 836014336 (16718354482831 / 20000) (16719640540987 / 20000) := by
  exact
    packedTile32768 835948800 836014336 13 3130 28912 30 _ _ (1027203 / 50000) (2054409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836014336 :
    ThetaLowerSegment 836014336 836079872 (16719640540987 / 20000) (83604852843053 / 100000) := by
  exact
    packedTile32768 836014336 836079872 13 3237 28913 30 _ _ (1027207 / 50000) (2054417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836079872 :
    ThetaLowerSegment 836079872 836145408 (83604852843053 / 100000) (83611494789379 / 100000) := by
  exact
    packedTile32768 836079872 836145408 13 3233 28915 30 _ _ (1027211 / 50000) (82177 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836145408 :
    ThetaLowerSegment 836145408 836210944 (83611494789379 / 100000) (83618019659059 / 100000) := by
  exact
    packedTile32768 836145408 836210944 13 3176 28916 30 _ _ (205443 / 10000) (2054433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836210944 :
    ThetaLowerSegment 836210944 836276480 (83618019659059 / 100000) (83624591806221 / 100000) := by
  exact
    packedTile32768 836210944 836276480 13 3199 28917 30 _ _ (1027219 / 50000) (2054441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836276480 :
    ThetaLowerSegment 836276480 836342016 (83624591806221 / 100000) (83630960585721 / 100000) := by
  exact
    packedTile32768 836276480 836342016 13 3100 28918 30 _ _ (410889 / 20000) (128403 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836342016 :
    ThetaLowerSegment 836342016 836407552 (83630960585721 / 100000) (83637501964073 / 100000) := by
  exact
    packedTile32768 836342016 836407552 13 3184 28919 30 _ _ (2054453 / 100000) (256807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836407552 :
    ThetaLowerSegment 836407552 836473088 (83637501964073 / 100000) (41822030929023 / 50000) := by
  exact
    packedTile32768 836407552 836473088 13 3193 28920 30 _ _ (2054461 / 100000) (64202 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836473088 :
    ThetaLowerSegment 836473088 836538624 (41822030929023 / 50000) (16730139969477 / 20000) := by
  exact
    packedTile32768 836473088 836538624 13 3231 28921 30 _ _ (2054469 / 100000) (256809 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836538624 :
    ThetaLowerSegment 836538624 836604160 (16730139969477 / 20000) (2614290010538 / 3125) := by
  exact
    packedTile32768 836538624 836604160 13 3203 28922 30 _ _ (2054477 / 100000) (25681 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836604160 :
    ThetaLowerSegment 836604160 836669696 (2614290010538 / 3125) (83663938923101 / 100000) := by
  exact
    packedTile32768 836604160 836669696 13 3241 28924 30 _ _ (410897 / 20000) (256811 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836669696 :
    ThetaLowerSegment 836669696 836735232 (83663938923101 / 100000) (83670581095737 / 100000) := by
  exact
    packedTile32768 836669696 836735232 13 3233 28925 30 _ _ (513623 / 25000) (410899 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836735232 :
    ThetaLowerSegment 836735232 836800768 (83670581095737 / 100000) (83677065097737 / 100000) := by
  exact
    packedTile32768 836735232 836800768 13 3156 28926 30 _ _ (4109 / 200) (2054503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836800768 :
    ThetaLowerSegment 836800768 836866304 (83677065097737 / 100000) (83683468999173 / 100000) := by
  exact
    packedTile32768 836800768 836866304 13 3117 28927 30 _ _ (513627 / 25000) (2054511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836866304 :
    ThetaLowerSegment 836866304 836931840 (83683468999173 / 100000) (16738009511881 / 20000) := by
  exact
    packedTile32768 836866304 836931840 13 3202 28928 30 _ _ (513629 / 25000) (2054519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836931840 :
    ThetaLowerSegment 836931840 836997376 (16738009511881 / 20000) (83696502873813 / 100000) := by
  exact
    packedTile32768 836931840 836997376 13 3142 28929 30 _ _ (513631 / 25000) (2054527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell836997376 :
    ThetaLowerSegment 836997376 837062912 (83696502873813 / 100000) (83703036285573 / 100000) := by
  exact
    packedTile32768 836997376 837062912 13 3180 28930 30 _ _ (513633 / 25000) (410907 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837062912 :
    ThetaLowerSegment 837062912 837128448 (83703036285573 / 100000) (20927405270767 / 25000) := by
  exact
    packedTile32768 837062912 837128448 13 3205 28932 30 _ _ (2054539 / 100000) (1027271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837128448 :
    ThetaLowerSegment 837128448 837193984 (20927405270767 / 25000) (41858091653093 / 50000) := by
  exact
    packedTile32768 837128448 837193984 13 3194 28933 30 _ _ (2054547 / 100000) (41091 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837193984 :
    ThetaLowerSegment 837193984 837259520 (41858091653093 / 50000) (83722636663441 / 100000) := by
  exact
    packedTile32768 837193984 837259520 13 3141 28934 30 _ _ (410911 / 20000) (1027279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837259520 :
    ThetaLowerSegment 837259520 837325056 (83722636663441 / 100000) (5233074291553 / 6250) := by
  exact
    packedTile32768 837259520 837325056 13 3189 28935 30 _ _ (2054563 / 100000) (1027283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837325056 :
    ThetaLowerSegment 837325056 837390592 (5233074291553 / 6250) (83735753019193 / 100000) := by
  exact
    packedTile32768 837325056 837390592 13 3195 28936 30 _ _ (2054571 / 100000) (1027287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837390592 :
    ThetaLowerSegment 837390592 837456128 (83735753019193 / 100000) (41871158699549 / 50000) := by
  exact
    packedTile32768 837390592 837456128 13 3195 28937 30 _ _ (2054579 / 100000) (1027291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837456128 :
    ThetaLowerSegment 837456128 837521664 (41871158699549 / 50000) (41874439873391 / 50000) := by
  exact
    packedTile32768 837456128 837521664 13 3194 28938 30 _ _ (1027293 / 50000) (2054589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837521664 :
    ThetaLowerSegment 837521664 837587200 (41874439873391 / 50000) (8375552019459 / 10000) := by
  exact
    packedTile32768 837521664 837587200 13 3232 28939 30 _ _ (1027297 / 50000) (2054597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837587200 :
    ThetaLowerSegment 837587200 837652736 (8375552019459 / 10000) (41881014586863 / 50000) := by
  exact
    packedTile32768 837587200 837652736 13 3168 28941 30 _ _ (1027301 / 50000) (410921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837652736 :
    ThetaLowerSegment 837652736 837718272 (41881014586863 / 50000) (20942160740829 / 25000) := by
  exact
    packedTile32768 837652736 837718272 13 3219 28942 30 _ _ (205461 / 10000) (2054613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837718272 :
    ThetaLowerSegment 837718272 837783808 (20942160740829 / 25000) (41887624280093 / 50000) := by
  exact
    packedTile32768 837718272 837783808 13 3215 28943 30 _ _ (1027309 / 50000) (2054621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837783808 :
    ThetaLowerSegment 837783808 837849344 (41887624280093 / 50000) (20945441972121 / 25000) := by
  exact
    packedTile32768 837783808 837849344 13 3173 28944 30 _ _ (1027313 / 50000) (2054629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837849344 :
    ThetaLowerSegment 837849344 837914880 (20945441972121 / 25000) (20947073350723 / 25000) := by
  exact
    packedTile32768 837849344 837914880 13 3176 28945 30 _ _ (2054633 / 100000) (513659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837914880 :
    ThetaLowerSegment 837914880 837980416 (20947073350723 / 25000) (4189748343843 / 5000) := by
  exact
    packedTile32768 837914880 837980416 13 3248 28946 30 _ _ (2054641 / 100000) (513661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell837980416 :
    ThetaLowerSegment 837980416 838045952 (4189748343843 / 5000) (41900752384989 / 50000) := by
  exact
    packedTile32768 837980416 838045952 13 3182 28947 30 _ _ (2054649 / 100000) (513663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838045952 :
    ThetaLowerSegment 838045952 838111488 (41900752384989 / 50000) (41904142569039 / 50000) := by
  exact
    packedTile32768 838045952 838111488 13 3300 28949 30 _ _ (2054657 / 100000) (102733 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838111488 :
    ThetaLowerSegment 838111488 838177024 (41904142569039 / 50000) (83814800480793 / 100000) := by
  exact
    packedTile32768 838111488 838177024 13 3171 28950 30 _ _ (410933 / 20000) (513667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838177024 :
    ThetaLowerSegment 838177024 838242560 (83814800480793 / 100000) (83821545968969 / 100000) := by
  exact
    packedTile32768 838177024 838242560 13 3283 28951 30 _ _ (128417 / 6250) (82187 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838242560 :
    ThetaLowerSegment 838242560 838308096 (83821545968969 / 100000) (83828063413929 / 100000) := by
  exact
    packedTile32768 838242560 838308096 13 3172 28952 30 _ _ (51367 / 2500) (2054683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838308096 :
    ThetaLowerSegment 838308096 838373632 (83828063413929 / 100000) (83834548009257 / 100000) := by
  exact
    packedTile32768 838308096 838373632 13 3156 28953 30 _ _ (64209 / 3125) (2054691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838373632 :
    ThetaLowerSegment 838373632 838439168 (83834548009257 / 100000) (83841075778449 / 100000) := by
  exact
    packedTile32768 838373632 838439168 13 3177 28954 30 _ _ (256837 / 12500) (2054699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838439168 :
    ThetaLowerSegment 838439168 838504704 (83841075778449 / 100000) (83847856301649 / 100000) := by
  exact
    packedTile32768 838439168 838504704 13 3300 28955 30 _ _ (128419 / 6250) (2054707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838504704 :
    ThetaLowerSegment 838504704 838570240 (83847856301649 / 100000) (83854297823769 / 100000) := by
  exact
    packedTile32768 838504704 838570240 13 3135 28956 30 _ _ (256839 / 12500) (410943 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838570240 :
    ThetaLowerSegment 838570240 838635776 (83854297823769 / 100000) (8386078868109 / 10000) := by
  exact
    packedTile32768 838570240 838635776 13 3159 28958 30 _ _ (2054719 / 100000) (1027361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838635776 :
    ThetaLowerSegment 838635776 838701312 (8386078868109 / 10000) (83867361752763 / 100000) := by
  exact
    packedTile32768 838635776 838701312 13 3199 28959 30 _ _ (2054727 / 100000) (205473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838701312 :
    ThetaLowerSegment 838701312 838766848 (83867361752763 / 100000) (41936891399819 / 50000) := by
  exact
    packedTile32768 838701312 838766848 13 3125 28960 30 _ _ (410947 / 20000) (1027369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838766848 :
    ThetaLowerSegment 838766848 838832384 (41936891399819 / 50000) (83880388798383 / 100000) := by
  exact
    packedTile32768 838766848 838832384 13 3215 28961 30 _ _ (2054743 / 100000) (1027373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838832384 :
    ThetaLowerSegment 838832384 838897920 (83880388798383 / 100000) (16777364855703 / 20000) := by
  exact
    packedTile32768 838832384 838897920 13 3132 28962 30 _ _ (2054751 / 100000) (1027377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838897920 :
    ThetaLowerSegment 838897920 838963456 (16777364855703 / 20000) (83893364573229 / 100000) := by
  exact
    packedTile32768 838897920 838963456 13 3183 28963 30 _ _ (1027379 / 50000) (2054761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell838963456 :
    ThetaLowerSegment 838963456 839028992 (83893364573229 / 100000) (83899824757533 / 100000) := by
  exact
    packedTile32768 838963456 839028992 13 3144 28964 30 _ _ (1027383 / 50000) (2054769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839028992 :
    ThetaLowerSegment 839028992 839094528 (83899824757533 / 100000) (83906338391113 / 100000) := by
  exact
    packedTile32768 839028992 839094528 13 3170 28965 30 _ _ (1027387 / 50000) (2054777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839094528 :
    ThetaLowerSegment 839094528 839160064 (83906338391113 / 100000) (16782585204441 / 20000) := by
  exact
    packedTile32768 839094528 839160064 13 3206 28967 30 _ _ (1027391 / 50000) (410957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839160064 :
    ThetaLowerSegment 839160064 839225600 (16782585204441 / 20000) (16783900270041 / 20000) := by
  exact
    packedTile32768 839160064 839225600 13 3200 28968 30 _ _ (205479 / 10000) (2054793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839225600 :
    ThetaLowerSegment 839225600 839291136 (16783900270041 / 20000) (83925990402289 / 100000) := by
  exact
    packedTile32768 839225600 839291136 13 3158 28969 30 _ _ (1027399 / 50000) (2054801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839291136 :
    ThetaLowerSegment 839291136 839356672 (83925990402289 / 100000) (83932500024529 / 100000) := by
  exact
    packedTile32768 839291136 839356672 13 3168 28970 30 _ _ (410961 / 20000) (256851 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839356672 :
    ThetaLowerSegment 839356672 839422208 (83932500024529 / 100000) (16787815907151 / 20000) := by
  exact
    packedTile32768 839356672 839422208 13 3202 28971 30 _ _ (2054813 / 100000) (64213 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839422208 :
    ThetaLowerSegment 839422208 839487744 (16787815907151 / 20000) (20986432747833 / 25000) := by
  exact
    packedTile32768 839422208 839487744 13 3237 28972 30 _ _ (2054821 / 100000) (256853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839487744 :
    ThetaLowerSegment 839487744 839553280 (20986432747833 / 25000) (83952324937593 / 100000) := by
  exact
    packedTile32768 839487744 839553280 13 3209 28973 30 _ _ (2054829 / 100000) (128427 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839553280 :
    ThetaLowerSegment 839553280 839618816 (83952324937593 / 100000) (83958793564469 / 100000) := by
  exact
    packedTile32768 839553280 839618816 13 3148 28975 30 _ _ (2054837 / 100000) (51371 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839618816 :
    ThetaLowerSegment 839618816 839684352 (83958793564469 / 100000) (83965475917157 / 100000) := by
  exact
    packedTile32768 839618816 839684352 13 3252 28976 30 _ _ (513711 / 25000) (2054847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839684352 :
    ThetaLowerSegment 839684352 839749888 (83965475917157 / 100000) (83972158295861 / 100000) := by
  exact
    packedTile32768 839684352 839749888 13 3252 28977 30 _ _ (513713 / 25000) (410971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839749888 :
    ThetaLowerSegment 839749888 839815424 (83972158295861 / 100000) (83978639324301 / 100000) := by
  exact
    packedTile32768 839749888 839815424 13 3154 28978 30 _ _ (102743 / 5000) (2054863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839815424 :
    ThetaLowerSegment 839815424 839880960 (83978639324301 / 100000) (16797021609753 / 20000) := by
  exact
    packedTile32768 839815424 839880960 13 3148 28979 30 _ _ (513717 / 25000) (2054871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839880960 :
    ThetaLowerSegment 839880960 839946496 (16797021609753 / 20000) (83991712420229 / 100000) := by
  exact
    packedTile32768 839880960 839946496 13 3214 28980 30 _ _ (513719 / 25000) (2054879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell839946496 :
    ThetaLowerSegment 839946496 840012032 (83991712420229 / 100000) (167996728153 / 200) := by
  exact
    packedTile32768 839946496 840012032 13 3237 28981 30 _ _ (2054883 / 100000) (1027443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840012032 :
    ThetaLowerSegment 840012032 840077568 (167996728153 / 200) (42002443150267 / 50000) := by
  exact
    packedTile32768 840012032 840077568 13 3174 28982 30 _ _ (2054891 / 100000) (1027447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840077568 :
    ThetaLowerSegment 840077568 840143104 (42002443150267 / 50000) (84011381836273 / 100000) := by
  exact
    packedTile32768 840077568 840143104 13 3161 28984 30 _ _ (2054899 / 100000) (1027451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840143104 :
    ThetaLowerSegment 840143104 840208640 (84011381836273 / 100000) (84017986307371 / 100000) := by
  exact
    packedTile32768 840143104 840208640 13 3214 28985 30 _ _ (2054907 / 100000) (205491 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840208640 :
    ThetaLowerSegment 840208640 840274176 (84017986307371 / 100000) (42012232727183 / 50000) := by
  exact
    packedTile32768 840208640 840274176 13 3153 28986 30 _ _ (410983 / 20000) (1027459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840274176 :
    ThetaLowerSegment 840274176 840339712 (42012232727183 / 50000) (21007761842383 / 25000) := by
  exact
    packedTile32768 840274176 840339712 13 3203 28987 30 _ _ (1027461 / 50000) (82197 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840339712 :
    ThetaLowerSegment 840339712 840405248 (21007761842383 / 25000) (21009411951173 / 25000) := by
  exact
    packedTile32768 840339712 840405248 13 3212 28988 30 _ _ (205493 / 10000) (2054933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840405248 :
    ThetaLowerSegment 840405248 840470784 (21009411951173 / 25000) (21011055901573 / 25000) := by
  exact
    packedTile32768 840405248 840470784 13 3200 28989 30 _ _ (1027469 / 50000) (2054941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840470784 :
    ThetaLowerSegment 840470784 840536320 (21011055901573 / 25000) (42025439788193 / 50000) := by
  exact
    packedTile32768 840470784 840536320 13 3239 28990 30 _ _ (1027473 / 50000) (2054949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840536320 :
    ThetaLowerSegment 840536320 840601856 (42025439788193 / 50000) (10507173451963 / 12500) := by
  exact
    packedTile32768 840536320 840601856 13 3167 28992 30 _ _ (1027477 / 50000) (2054957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840601856 :
    ThetaLowerSegment 840601856 840667392 (10507173451963 / 12500) (84063879237503 / 100000) := by
  exact
    packedTile32768 840601856 840667392 13 3159 28993 30 _ _ (2054961 / 100000) (513741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840667392 :
    ThetaLowerSegment 840667392 840732928 (84063879237503 / 100000) (84070377049481 / 100000) := by
  exact
    packedTile32768 840667392 840732928 13 3162 28994 30 _ _ (2054969 / 100000) (513743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840732928 :
    ThetaLowerSegment 840732928 840798464 (84070377049481 / 100000) (84076924206203 / 100000) := by
  exact
    packedTile32768 840732928 840798464 13 3186 28995 30 _ _ (2054977 / 100000) (102749 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840798464 :
    ThetaLowerSegment 840798464 840864000 (84076924206203 / 100000) (42041777821399 / 50000) := by
  exact
    packedTile32768 840798464 840864000 13 3227 28996 30 _ _ (410997 / 20000) (513747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840864000 :
    ThetaLowerSegment 840864000 840929536 (42041777821399 / 50000) (84090084355559 / 100000) := by
  exact
    packedTile32768 840864000 840929536 13 3177 28997 30 _ _ (2054993 / 100000) (513749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840929536 :
    ThetaLowerSegment 840929536 840995072 (84090084355559 / 100000) (84096621310559 / 100000) := by
  exact
    packedTile32768 840929536 840995072 13 3181 28998 30 _ _ (411 / 20) (2055003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell840995072 :
    ThetaLowerSegment 840995072 841060608 (84096621310559 / 100000) (84103213776223 / 100000) := by
  exact
    packedTile32768 840995072 841060608 13 3208 28999 30 _ _ (64219 / 3125) (2055011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841060608 :
    ThetaLowerSegment 841060608 841126144 (84103213776223 / 100000) (84109728176943 / 100000) := by
  exact
    packedTile32768 841060608 841126144 13 3170 29001 30 _ _ (256877 / 12500) (2055019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841126144 :
    ThetaLowerSegment 841126144 841191680 (84109728176943 / 100000) (84116285758527 / 100000) := by
  exact
    packedTile32768 841126144 841191680 13 3191 29002 30 _ _ (128439 / 6250) (2055027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841191680 :
    ThetaLowerSegment 841191680 841257216 (84116285758527 / 100000) (84122820760287 / 100000) := by
  exact
    packedTile32768 841191680 841257216 13 3180 29003 30 _ _ (256879 / 12500) (411007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841257216 :
    ThetaLowerSegment 841257216 841322752 (84122820760287 / 100000) (42064547397177 / 50000) := by
  exact
    packedTile32768 841257216 841322752 13 3053 29004 30 _ _ (2055039 / 100000) (1027521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841322752 :
    ThetaLowerSegment 841322752 841339136 (42064547397177 / 50000) (84130740887001 / 100000) := by
  exact
    packedTile32768 841322752 841339136 11 801 29005 30 _ _ (2055047 / 100000) (41101 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841339136 :
    ThetaLowerSegment 841339136 841341184 (84130740887001 / 100000) (42065498884063 / 50000) := by
  exact
    packedTile32768 841339136 841341184 8 125 29005 30 _ _ (2055049 / 100000) (513763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_809341184_841341184 :
    ThetaLowerSegment 809341184 841341184 (80931183895441 / 100000) (42065498884063 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell809341184 cell809406720)
                    (ThetaLowerSegment.join cell809472256 cell809537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell809603328 cell809668864)
                    (ThetaLowerSegment.join cell809734400 cell809799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell809865472 cell809931008)
                    (ThetaLowerSegment.join cell809996544 cell810062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell810127616 cell810193152)
                    (ThetaLowerSegment.join cell810258688 cell810324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell810389760 cell810455296)
                    (ThetaLowerSegment.join cell810520832 cell810586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell810651904 cell810717440)
                    (ThetaLowerSegment.join cell810782976 cell810848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell810914048 cell810979584)
                    (ThetaLowerSegment.join cell811045120 cell811110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell811176192 cell811241728)
                    (ThetaLowerSegment.join cell811307264 cell811372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell811438336 cell811503872)
                    (ThetaLowerSegment.join cell811569408 cell811634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell811700480 cell811766016)
                    (ThetaLowerSegment.join cell811831552 cell811897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell811962624 cell812028160)
                    (ThetaLowerSegment.join cell812093696 cell812159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell812224768 cell812290304)
                    (ThetaLowerSegment.join cell812355840 cell812421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell812486912 cell812552448)
                    (ThetaLowerSegment.join cell812617984 cell812683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell812749056 cell812814592)
                    (ThetaLowerSegment.join cell812880128 cell812945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell813011200 cell813076736)
                    (ThetaLowerSegment.join cell813142272 cell813207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell813273344 cell813338880)
                    (ThetaLowerSegment.join cell813404416 cell813469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell813535488 cell813601024)
                    (ThetaLowerSegment.join cell813666560 cell813732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell813797632 cell813863168)
                    (ThetaLowerSegment.join cell813928704 cell813994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell814059776 cell814125312)
                    (ThetaLowerSegment.join cell814190848 cell814256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell814321920 cell814387456)
                    (ThetaLowerSegment.join cell814452992 cell814518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell814584064 cell814649600)
                    (ThetaLowerSegment.join cell814715136 cell814780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell814846208 cell814911744)
                    (ThetaLowerSegment.join cell814977280 cell815042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell815108352 cell815173888)
                    (ThetaLowerSegment.join cell815239424 cell815304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell815370496 cell815436032)
                    (ThetaLowerSegment.join cell815501568 cell815567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell815632640 cell815698176)
                    (ThetaLowerSegment.join cell815763712 cell815829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell815894784 cell815960320)
                    (ThetaLowerSegment.join cell816025856 cell816091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell816156928 cell816222464)
                    (ThetaLowerSegment.join cell816288000 cell816353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell816419072 cell816484608)
                    (ThetaLowerSegment.join cell816550144 cell816615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell816681216 cell816746752)
                    (ThetaLowerSegment.join cell816812288 cell816877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell816943360 cell817008896)
                    (ThetaLowerSegment.join cell817074432 cell817139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell817205504 cell817271040)
                    (ThetaLowerSegment.join cell817336576 cell817402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell817467648 cell817533184)
                    (ThetaLowerSegment.join cell817598720 cell817664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell817729792 cell817795328)
                    (ThetaLowerSegment.join cell817860864 cell817926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell817991936 cell818057472)
                    (ThetaLowerSegment.join cell818123008 cell818188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell818254080 cell818319616)
                    (ThetaLowerSegment.join cell818385152 cell818450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell818516224 cell818581760)
                    (ThetaLowerSegment.join cell818647296 cell818712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell818778368 cell818843904)
                    (ThetaLowerSegment.join cell818909440 cell818974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell819040512 cell819106048)
                    (ThetaLowerSegment.join cell819171584 cell819237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell819302656 cell819368192)
                    (ThetaLowerSegment.join cell819433728 cell819499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell819564800 cell819630336)
                    (ThetaLowerSegment.join cell819695872 cell819761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell819826944 cell819892480)
                    (ThetaLowerSegment.join cell819958016 cell820023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell820089088 cell820154624)
                    (ThetaLowerSegment.join cell820220160 cell820285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell820351232 cell820416768)
                    (ThetaLowerSegment.join cell820482304 cell820547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell820613376 cell820678912)
                    (ThetaLowerSegment.join cell820744448 cell820809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell820875520 cell820941056)
                    (ThetaLowerSegment.join cell821006592 cell821072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell821137664 cell821203200)
                    (ThetaLowerSegment.join cell821268736 cell821334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell821399808 cell821465344)
                    (ThetaLowerSegment.join cell821530880 cell821596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell821661952 cell821727488)
                    (ThetaLowerSegment.join cell821793024 cell821858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell821924096 cell821989632)
                    (ThetaLowerSegment.join cell822055168 cell822120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell822186240 cell822251776)
                    (ThetaLowerSegment.join cell822317312 cell822382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell822448384 cell822513920)
                    (ThetaLowerSegment.join cell822579456 cell822644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell822710528 cell822776064)
                    (ThetaLowerSegment.join cell822841600 cell822907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell822972672 cell823038208)
                    (ThetaLowerSegment.join cell823103744 cell823169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell823234816 cell823300352)
                    (ThetaLowerSegment.join cell823365888 cell823431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell823496960 cell823562496)
                    (ThetaLowerSegment.join cell823628032 cell823693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell823759104 cell823824640)
                    (ThetaLowerSegment.join cell823890176 cell823955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell824021248 cell824086784)
                    (ThetaLowerSegment.join cell824152320 cell824217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell824283392 cell824348928)
                    (ThetaLowerSegment.join cell824414464 cell824480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell824545536 cell824611072)
                    (ThetaLowerSegment.join cell824676608 cell824742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell824807680 cell824873216)
                    (ThetaLowerSegment.join cell824938752 cell825004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell825069824 cell825135360)
                    (ThetaLowerSegment.join cell825200896 cell825266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell825331968 cell825397504)
                    (ThetaLowerSegment.join cell825463040 cell825528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell825594112 cell825659648)
                    (ThetaLowerSegment.join cell825725184 cell825790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell825856256 cell825921792)
                    (ThetaLowerSegment.join cell825987328 cell826052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell826118400 cell826183936)
                    (ThetaLowerSegment.join cell826249472 cell826315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell826380544 cell826446080)
                    (ThetaLowerSegment.join cell826511616 cell826577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell826642688 cell826708224)
                    (ThetaLowerSegment.join cell826773760 cell826839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell826904832 cell826970368)
                    (ThetaLowerSegment.join cell827035904 cell827101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell827166976 cell827232512)
                    (ThetaLowerSegment.join cell827298048 cell827363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell827429120 cell827494656)
                    (ThetaLowerSegment.join cell827560192 cell827625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell827691264 cell827756800)
                    (ThetaLowerSegment.join cell827822336 cell827887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell827953408 cell828018944)
                    (ThetaLowerSegment.join cell828084480 cell828150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell828215552 cell828281088)
                    (ThetaLowerSegment.join cell828346624 cell828412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell828477696 cell828543232)
                    (ThetaLowerSegment.join cell828608768 cell828674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell828739840 cell828805376)
                    (ThetaLowerSegment.join cell828870912 cell828936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell829001984 cell829067520)
                    (ThetaLowerSegment.join cell829133056 cell829198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell829264128 cell829329664)
                    (ThetaLowerSegment.join cell829395200 cell829460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell829526272 cell829591808)
                    (ThetaLowerSegment.join cell829657344 cell829722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell829788416 cell829853952)
                    (ThetaLowerSegment.join cell829919488 cell829985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell830050560 cell830116096)
                    (ThetaLowerSegment.join cell830181632 cell830247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell830312704 cell830378240)
                    (ThetaLowerSegment.join cell830443776 cell830509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell830574848 cell830640384)
                    (ThetaLowerSegment.join cell830705920 cell830771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell830836992 cell830902528)
                    (ThetaLowerSegment.join cell830968064 cell831033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell831099136 cell831164672)
                    (ThetaLowerSegment.join cell831230208 cell831295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell831361280 cell831426816)
                    (ThetaLowerSegment.join cell831492352 cell831557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell831623424 cell831688960)
                    (ThetaLowerSegment.join cell831754496 cell831820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell831885568 cell831951104)
                    (ThetaLowerSegment.join cell832016640 cell832082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell832147712 cell832213248)
                    (ThetaLowerSegment.join cell832278784 cell832344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell832409856 cell832475392)
                    (ThetaLowerSegment.join cell832540928 cell832606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell832672000 cell832737536)
                    (ThetaLowerSegment.join cell832803072 cell832868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell832934144 cell832999680)
                    (ThetaLowerSegment.join cell833065216 cell833130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell833196288 cell833261824)
                    (ThetaLowerSegment.join cell833327360 cell833392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell833458432 cell833523968)
                    (ThetaLowerSegment.join cell833589504 cell833655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell833720576 cell833786112)
                    (ThetaLowerSegment.join cell833851648 cell833917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell833982720 cell834048256)
                    (ThetaLowerSegment.join cell834113792 cell834179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell834244864 cell834310400)
                    (ThetaLowerSegment.join cell834375936 cell834441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell834507008 cell834572544)
                    (ThetaLowerSegment.join cell834638080 cell834703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell834769152 cell834834688)
                    (ThetaLowerSegment.join cell834900224 cell834965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell835031296 cell835096832)
                    (ThetaLowerSegment.join cell835162368 cell835227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell835293440 cell835358976)
                    (ThetaLowerSegment.join cell835424512 cell835490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell835555584 cell835621120)
                    (ThetaLowerSegment.join cell835686656 cell835752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell835817728 cell835883264)
                    (ThetaLowerSegment.join cell835948800 cell836014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell836079872 cell836145408)
                    (ThetaLowerSegment.join cell836210944 cell836276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell836342016 cell836407552)
                    (ThetaLowerSegment.join cell836473088 cell836538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell836604160 cell836669696)
                    (ThetaLowerSegment.join cell836735232 cell836800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell836866304 cell836931840)
                    (ThetaLowerSegment.join cell836997376 cell837062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell837128448 cell837193984)
                    (ThetaLowerSegment.join cell837259520 cell837325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell837390592 cell837456128)
                    (ThetaLowerSegment.join cell837521664 cell837587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell837652736 cell837718272)
                    (ThetaLowerSegment.join cell837783808 cell837849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell837914880 cell837980416)
                    (ThetaLowerSegment.join cell838045952 cell838111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell838177024 cell838242560)
                    (ThetaLowerSegment.join cell838308096 cell838373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell838439168 cell838504704)
                    (ThetaLowerSegment.join cell838570240 cell838635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell838701312 cell838766848)
                    (ThetaLowerSegment.join cell838832384 cell838897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell838963456 cell839028992)
                    (ThetaLowerSegment.join cell839094528 cell839160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell839225600 cell839291136)
                    (ThetaLowerSegment.join cell839356672 cell839422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell839487744 cell839553280)
                    (ThetaLowerSegment.join cell839618816 cell839684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell839749888 cell839815424)
                    (ThetaLowerSegment.join cell839880960 cell839946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell840012032 cell840077568)
                    (ThetaLowerSegment.join cell840143104 cell840208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell840274176 cell840339712)
                    (ThetaLowerSegment.join cell840405248 cell840470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell840536320 cell840601856)
                    (ThetaLowerSegment.join cell840667392 cell840732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell840798464 cell840864000)
                  (ThetaLowerSegment.join cell840929536 cell840995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell841060608 cell841126144)
                  (ThetaLowerSegment.join cell841191680 cell841257216)))
              (ThetaLowerSegment.join cell841322752 cell841339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
