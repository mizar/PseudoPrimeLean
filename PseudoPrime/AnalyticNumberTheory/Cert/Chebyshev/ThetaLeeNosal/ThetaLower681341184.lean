/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 681341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell649341184 :
    ThetaLowerSegment 649341184 649406720 (12986227721673 / 20000) (12987532867737 / 20000) := by
  exact
    packedTile32768 649341184 649406720 13 3216 25482 29 _ _ (405829 / 20000) (507287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649406720 :
    ThetaLowerSegment 649406720 649472256 (12987532867737 / 20000) (1298883274443 / 2000) := by
  exact
    packedTile32768 649406720 649472256 13 3203 25483 29 _ _ (405831 / 20000) (1014579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649472256 :
    ThetaLowerSegment 649472256 649537792 (1298883274443 / 2000) (32475415780813 / 50000) := by
  exact
    packedTile32768 649472256 649537792 13 3286 25484 29 _ _ (1014583 / 50000) (2029169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649537792 :
    ThetaLowerSegment 649537792 649603328 (32475415780813 / 50000) (32478726381457 / 50000) := by
  exact
    packedTile32768 649537792 649603328 13 3263 25486 29 _ _ (253647 / 12500) (2029179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649603328 :
    ThetaLowerSegment 649603328 649668864 (32478726381457 / 50000) (32481975108243 / 50000) := by
  exact
    packedTile32768 649603328 649668864 13 3202 25487 29 _ _ (1014593 / 50000) (2029189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649668864 :
    ThetaLowerSegment 649668864 649734400 (32481975108243 / 50000) (32485269507949 / 50000) := by
  exact
    packedTile32768 649668864 649734400 13 3247 25488 29 _ _ (507299 / 25000) (2029199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649734400 :
    ThetaLowerSegment 649734400 649799936 (32485269507949 / 50000) (32488500003901 / 50000) := by
  exact
    packedTile32768 649734400 649799936 13 3184 25489 29 _ _ (1014603 / 50000) (2029209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649799936 :
    ThetaLowerSegment 649799936 649865472 (32488500003901 / 50000) (32491798494509 / 50000) := by
  exact
    packedTile32768 649799936 649865472 13 3251 25491 29 _ _ (63413 / 3125) (2029219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649865472 :
    ThetaLowerSegment 649865472 649931008 (32491798494509 / 50000) (32495083811403 / 50000) := by
  exact
    packedTile32768 649865472 649931008 13 3238 25492 29 _ _ (1014613 / 50000) (2029229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649931008 :
    ThetaLowerSegment 649931008 649996544 (32495083811403 / 50000) (32498333632857 / 50000) := by
  exact
    packedTile32768 649931008 649996544 13 3203 25493 29 _ _ (507309 / 25000) (2029239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell649996544 :
    ThetaLowerSegment 649996544 650062080 (32498333632857 / 50000) (1300065895663 / 2000) := by
  exact
    packedTile32768 649996544 650062080 13 3266 25495 29 _ _ (1014623 / 50000) (2029249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650062080 :
    ThetaLowerSegment 650062080 650127616 (1300065895663 / 2000) (6500993045027 / 10000) := by
  exact
    packedTile32768 650062080 650127616 13 3270 25496 29 _ _ (253657 / 12500) (2029259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650127616 :
    ThetaLowerSegment 650127616 650193152 (6500993045027 / 10000) (16254107547317 / 25000) := by
  exact
    packedTile32768 650127616 650193152 13 3203 25497 29 _ _ (1014633 / 50000) (2029269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650193152 :
    ThetaLowerSegment 650193152 650258688 (16254107547317 / 25000) (6502309839349 / 10000) := by
  exact
    packedTile32768 650193152 650258688 13 3286 25498 29 _ _ (2029277 / 100000) (12683 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650258688 :
    ThetaLowerSegment 650258688 650324224 (6502309839349 / 10000) (65029707781249 / 100000) := by
  exact
    packedTile32768 650258688 650324224 13 3257 25500 29 _ _ (2029287 / 100000) (202929 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650324224 :
    ThetaLowerSegment 650324224 650389760 (65029707781249 / 100000) (6503622791251 / 10000) := by
  exact
    packedTile32768 650324224 650389760 13 3213 25501 29 _ _ (2029297 / 100000) (20293 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650389760 :
    ThetaLowerSegment 650389760 650455296 (6503622791251 / 10000) (13008550426903 / 20000) := by
  exact
    packedTile32768 650389760 650455296 13 3215 25502 29 _ _ (2029307 / 100000) (202931 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650455296 :
    ThetaLowerSegment 650455296 650520832 (13008550426903 / 20000) (65049396118373 / 100000) := by
  exact
    packedTile32768 650455296 650520832 13 3274 25504 29 _ _ (2029317 / 100000) (50733 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650520832 :
    ThetaLowerSegment 650520832 650586368 (65049396118373 / 100000) (65055954903237 / 100000) := by
  exact
    packedTile32768 650520832 650586368 13 3232 25505 29 _ _ (2029327 / 100000) (202933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650586368 :
    ThetaLowerSegment 650586368 650651904 (65055954903237 / 100000) (65062420370919 / 100000) := by
  exact
    packedTile32768 650586368 650651904 13 3186 25506 29 _ _ (2029337 / 100000) (101467 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650651904 :
    ThetaLowerSegment 650651904 650717440 (65062420370919 / 100000) (32534539329213 / 50000) := by
  exact
    packedTile32768 650651904 650717440 13 3281 25507 29 _ _ (2029347 / 100000) (40587 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650717440 :
    ThetaLowerSegment 650717440 650782976 (32534539329213 / 50000) (8134460273263 / 12500) := by
  exact
    packedTile32768 650717440 650782976 13 3254 25509 29 _ _ (2029357 / 100000) (25367 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650782976 :
    ThetaLowerSegment 650782976 650848512 (8134460273263 / 12500) (65082198483541 / 100000) := by
  exact
    packedTile32768 650782976 650848512 13 3211 25510 29 _ _ (2029367 / 100000) (202937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650848512 :
    ThetaLowerSegment 650848512 650914048 (65082198483541 / 100000) (1627216652701 / 2500) := by
  exact
    packedTile32768 650848512 650914048 13 3187 25511 29 _ _ (2029377 / 100000) (101469 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650914048 :
    ThetaLowerSegment 650914048 650979584 (1627216652701 / 2500) (65095243351307 / 100000) := by
  exact
    packedTile32768 650914048 650979584 13 3241 25513 29 _ _ (2029387 / 100000) (202939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell650979584 :
    ThetaLowerSegment 650979584 651045120 (65095243351307 / 100000) (65101802362411 / 100000) := by
  exact
    packedTile32768 650979584 651045120 13 3232 25514 29 _ _ (2029397 / 100000) (10147 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651045120 :
    ThetaLowerSegment 651045120 651110656 (65101802362411 / 100000) (32554173599993 / 50000) := by
  exact
    packedTile32768 651045120 651110656 13 3225 25515 29 _ _ (2029407 / 100000) (202941 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651110656 :
    ThetaLowerSegment 651110656 651176192 (32554173599993 / 50000) (6511489816129 / 10000) := by
  exact
    packedTile32768 651110656 651176192 13 3228 25516 29 _ _ (1014709 / 50000) (2029421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651176192 :
    ThetaLowerSegment 651176192 651241728 (6511489816129 / 10000) (32560733709863 / 50000) := by
  exact
    packedTile32768 651176192 651241728 13 3237 25518 29 _ _ (507357 / 25000) (2029431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651241728 :
    ThetaLowerSegment 651241728 651307264 (32560733709863 / 50000) (32564061988183 / 50000) := by
  exact
    packedTile32768 651241728 651307264 13 3280 25519 29 _ _ (1014719 / 50000) (2029441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651307264 :
    ThetaLowerSegment 651307264 651372800 (32564061988183 / 50000) (32567348679219 / 50000) := by
  exact
    packedTile32768 651307264 651372800 13 3239 25520 29 _ _ (253681 / 12500) (2029451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651372800 :
    ThetaLowerSegment 651372800 651438336 (32567348679219 / 50000) (2035664584812 / 3125) := by
  exact
    packedTile32768 651372800 651438336 13 3237 25522 29 _ _ (1014729 / 50000) (2029461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651438336 :
    ThetaLowerSegment 651438336 651503872 (2035664584812 / 3125) (1628693112029 / 2500) := by
  exact
    packedTile32768 651438336 651503872 13 3182 25523 29 _ _ (507367 / 25000) (2029471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651503872 :
    ThetaLowerSegment 651503872 651569408 (1628693112029 / 2500) (1628853440791 / 2500) := by
  exact
    packedTile32768 651503872 651569408 13 3160 25524 29 _ _ (1014739 / 50000) (2029481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651569408 :
    ThetaLowerSegment 651569408 651634944 (1628853440791 / 2500) (8145090922397 / 12500) := by
  exact
    packedTile32768 651569408 651634944 13 3247 25525 29 _ _ (126843 / 6250) (2029491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651634944 :
    ThetaLowerSegment 651634944 651700480 (8145090922397 / 12500) (16291810516939 / 25000) := by
  exact
    packedTile32768 651634944 651700480 13 3210 25527 29 _ _ (1014749 / 50000) (2029501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651700480 :
    ThetaLowerSegment 651700480 651766016 (16291810516939 / 25000) (8146726955521 / 12500) := by
  exact
    packedTile32768 651700480 651766016 13 3239 25528 29 _ _ (507377 / 25000) (2029511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651766016 :
    ThetaLowerSegment 651766016 651831552 (8146726955521 / 12500) (6518028777707 / 10000) := by
  exact
    packedTile32768 651766016 651831552 13 3189 25529 29 _ _ (1014759 / 50000) (2029521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651831552 :
    ThetaLowerSegment 651831552 651897088 (6518028777707 / 10000) (32593419546727 / 50000) := by
  exact
    packedTile32768 651831552 651897088 13 3228 25530 29 _ _ (253691 / 12500) (2029531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651897088 :
    ThetaLowerSegment 651897088 651962624 (32593419546727 / 50000) (32596687102907 / 50000) := by
  exact
    packedTile32768 651897088 651962624 13 3220 25532 29 _ _ (1014769 / 50000) (2029541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell651962624 :
    ThetaLowerSegment 651962624 652028160 (32596687102907 / 50000) (32599974970667 / 50000) := by
  exact
    packedTile32768 651962624 652028160 13 3240 25533 29 _ _ (507387 / 25000) (2029551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652028160 :
    ThetaLowerSegment 652028160 652093696 (32599974970667 / 50000) (407540874476 / 625) := by
  exact
    packedTile32768 652028160 652093696 13 3247 25534 29 _ _ (1014779 / 50000) (2029561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652093696 :
    ThetaLowerSegment 652093696 652159232 (407540874476 / 625) (81516369276 / 125) := by
  exact
    packedTile32768 652093696 652159232 13 3230 25536 29 _ _ (63424 / 3125) (2029571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652159232 :
    ThetaLowerSegment 652159232 652224768 (81516369276 / 125) (6521957992251 / 10000) := by
  exact
    packedTile32768 652159232 652224768 13 3195 25537 29 _ _ (1014789 / 50000) (2029581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652224768 :
    ThetaLowerSegment 652224768 652290304 (6521957992251 / 10000) (32613045420407 / 50000) := by
  exact
    packedTile32768 652224768 652290304 13 3208 25538 29 _ _ (507397 / 25000) (2029591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652290304 :
    ThetaLowerSegment 652290304 652355840 (32613045420407 / 50000) (32616272482817 / 50000) := by
  exact
    packedTile32768 652290304 652355840 13 3180 25539 29 _ _ (2029599 / 100000) (1014801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652355840 :
    ThetaLowerSegment 652355840 652421376 (32616272482817 / 50000) (407744175806 / 625) := by
  exact
    packedTile32768 652355840 652421376 13 3214 25541 29 _ _ (2029609 / 100000) (507403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652421376 :
    ThetaLowerSegment 652421376 652486912 (407744175806 / 625) (65245625827949 / 100000) := by
  exact
    packedTile32768 652421376 652486912 13 3231 25542 29 _ _ (2029619 / 100000) (1014811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652486912 :
    ThetaLowerSegment 652486912 652552448 (65245625827949 / 100000) (16313056037957 / 25000) := by
  exact
    packedTile32768 652486912 652552448 13 3251 25543 29 _ _ (2029629 / 100000) (63426 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652552448 :
    ThetaLowerSegment 652552448 652617984 (16313056037957 / 25000) (8157351037593 / 12500) := by
  exact
    packedTile32768 652552448 652617984 13 3244 25545 29 _ _ (2029639 / 100000) (1014821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652617984 :
    ThetaLowerSegment 652617984 652683520 (8157351037593 / 12500) (32632710448593 / 50000) := by
  exact
    packedTile32768 652617984 652683520 13 3258 25546 29 _ _ (2029649 / 100000) (507413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652683520 :
    ThetaLowerSegment 652683520 652749056 (32632710448593 / 50000) (16318010411211 / 25000) := by
  exact
    packedTile32768 652683520 652749056 13 3262 25547 29 _ _ (2029659 / 100000) (1014831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652749056 :
    ThetaLowerSegment 652749056 652814592 (16318010411211 / 25000) (65278664454791 / 100000) := by
  exact
    packedTile32768 652749056 652814592 13 3263 25548 29 _ _ (2029669 / 100000) (253709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652814592 :
    ThetaLowerSegment 652814592 652880128 (65278664454791 / 100000) (32642564491203 / 50000) := by
  exact
    packedTile32768 652814592 652880128 13 3185 25550 29 _ _ (2029679 / 100000) (1014841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652880128 :
    ThetaLowerSegment 652880128 652945664 (32642564491203 / 50000) (8161465683957 / 12500) := by
  exact
    packedTile32768 652880128 652945664 13 3250 25551 29 _ _ (2029689 / 100000) (507423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell652945664 :
    ThetaLowerSegment 652945664 653011200 (8161465683957 / 12500) (16324577453803 / 25000) := by
  exact
    packedTile32768 652945664 653011200 13 3244 25552 29 _ _ (2029699 / 100000) (1014851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653011200 :
    ThetaLowerSegment 653011200 653076736 (16324577453803 / 25000) (65304689190599 / 100000) := by
  exact
    packedTile32768 653011200 653076736 13 3143 25554 29 _ _ (2029709 / 100000) (126857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653076736 :
    ThetaLowerSegment 653076736 653142272 (65304689190599 / 100000) (6531120255887 / 10000) := by
  exact
    packedTile32768 653076736 653142272 13 3209 25555 29 _ _ (2029719 / 100000) (1014861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653142272 :
    ThetaLowerSegment 653142272 653207808 (6531120255887 / 10000) (65317918932131 / 100000) := by
  exact
    packedTile32768 653142272 653207808 13 3309 25556 29 _ _ (2029729 / 100000) (507433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653207808 :
    ThetaLowerSegment 653207808 653273344 (65317918932131 / 100000) (2612976239119 / 4000) := by
  exact
    packedTile32768 653207808 653273344 13 3196 25557 29 _ _ (2029739 / 100000) (1014871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653273344 :
    ThetaLowerSegment 653273344 653338880 (2612976239119 / 4000) (4083183987469 / 6250) := by
  exact
    packedTile32768 653273344 653338880 13 3221 25559 29 _ _ (2029749 / 100000) (253719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653338880 :
    ThetaLowerSegment 653338880 653404416 (4083183987469 / 6250) (4083593998787 / 6250) := by
  exact
    packedTile32768 653338880 653404416 13 3232 25560 29 _ _ (2029759 / 100000) (1014881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653404416 :
    ThetaLowerSegment 653404416 653469952 (4083593998787 / 6250) (32672050364921 / 50000) := by
  exact
    packedTile32768 653404416 653469952 13 3250 25561 29 _ _ (2029769 / 100000) (507443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653469952 :
    ThetaLowerSegment 653469952 653535488 (32672050364921 / 50000) (32675306130437 / 50000) := by
  exact
    packedTile32768 653469952 653535488 13 3208 25563 29 _ _ (2029779 / 100000) (1014891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653535488 :
    ThetaLowerSegment 653535488 653601024 (32675306130437 / 50000) (65357174568711 / 100000) := by
  exact
    packedTile32768 653535488 653601024 13 3233 25564 29 _ _ (2029789 / 100000) (63431 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653601024 :
    ThetaLowerSegment 653601024 653666560 (65357174568711 / 100000) (65363698342697 / 100000) := by
  exact
    packedTile32768 653601024 653666560 13 3214 25565 29 _ _ (2029799 / 100000) (1014901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653666560 :
    ThetaLowerSegment 653666560 653732096 (65363698342697 / 100000) (32685166894159 / 50000) := by
  exact
    packedTile32768 653666560 653732096 13 3269 25566 29 _ _ (2029809 / 100000) (507453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653732096 :
    ThetaLowerSegment 653732096 653797632 (32685166894159 / 50000) (32688459260577 / 50000) := by
  exact
    packedTile32768 653732096 653797632 13 3244 25568 29 _ _ (2029819 / 100000) (1014911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653797632 :
    ThetaLowerSegment 653797632 653863168 (32688459260577 / 50000) (32691780060821 / 50000) := by
  exact
    packedTile32768 653797632 653863168 13 3272 25569 29 _ _ (2029829 / 100000) (253729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653863168 :
    ThetaLowerSegment 653863168 653928704 (32691780060821 / 50000) (13078013963063 / 20000) := by
  exact
    packedTile32768 653863168 653928704 13 3207 25570 29 _ _ (2029839 / 100000) (1014921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653928704 :
    ThetaLowerSegment 653928704 653994240 (13078013963063 / 20000) (13079333364913 / 20000) := by
  exact
    packedTile32768 653928704 653994240 13 3250 25572 29 _ _ (2029849 / 100000) (507463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell653994240 :
    ThetaLowerSegment 653994240 654059776 (13079333364913 / 20000) (65403373478701 / 100000) := by
  exact
    packedTile32768 653994240 654059776 13 3304 25573 29 _ _ (2029859 / 100000) (1014931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654059776 :
    ThetaLowerSegment 654059776 654125312 (65403373478701 / 100000) (16352505324919 / 25000) := by
  exact
    packedTile32768 654059776 654125312 13 3275 25574 29 _ _ (2029869 / 100000) (126867 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654125312 :
    ThetaLowerSegment 654125312 654190848 (16352505324919 / 25000) (65416555480177 / 100000) := by
  exact
    packedTile32768 654125312 654190848 13 3219 25575 29 _ _ (2029879 / 100000) (1014941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654190848 :
    ThetaLowerSegment 654190848 654256384 (65416555480177 / 100000) (65423022706531 / 100000) := by
  exact
    packedTile32768 654190848 654256384 13 3186 25577 29 _ _ (2029889 / 100000) (507473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654256384 :
    ThetaLowerSegment 654256384 654321920 (65423022706531 / 100000) (65429640177271 / 100000) := by
  exact
    packedTile32768 654256384 654321920 13 3260 25578 29 _ _ (2029899 / 100000) (1014951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654321920 :
    ThetaLowerSegment 654321920 654387456 (65429640177271 / 100000) (65436148068731 / 100000) := by
  exact
    packedTile32768 654321920 654387456 13 3206 25579 29 _ _ (202991 / 10000) (2029913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654387456 :
    ThetaLowerSegment 654387456 654452992 (65436148068731 / 100000) (65442572765531 / 100000) := by
  exact
    packedTile32768 654387456 654452992 13 3165 25580 29 _ _ (12687 / 625) (2029923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654452992 :
    ThetaLowerSegment 654452992 654518528 (65442572765531 / 100000) (65449149738731 / 100000) := by
  exact
    packedTile32768 654452992 654518528 13 3240 25582 29 _ _ (202993 / 10000) (2029933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654518528 :
    ThetaLowerSegment 654518528 654584064 (65449149738731 / 100000) (65455704414991 / 100000) := by
  exact
    packedTile32768 654518528 654584064 13 3229 25583 29 _ _ (101497 / 5000) (2029943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654584064 :
    ThetaLowerSegment 654584064 654649600 (65455704414991 / 100000) (65462283482941 / 100000) := by
  exact
    packedTile32768 654584064 654649600 13 3241 25584 29 _ _ (40599 / 2000) (2029953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654649600 :
    ThetaLowerSegment 654649600 654715136 (65462283482941 / 100000) (65468864613261 / 100000) := by
  exact
    packedTile32768 654649600 654715136 13 3242 25586 29 _ _ (50749 / 2500) (2029963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654715136 :
    ThetaLowerSegment 654715136 654780672 (65468864613261 / 100000) (65475321947831 / 100000) := by
  exact
    packedTile32768 654715136 654780672 13 3181 25587 29 _ _ (202997 / 10000) (2029973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654780672 :
    ThetaLowerSegment 654780672 654846208 (65475321947831 / 100000) (65481795554051 / 100000) := by
  exact
    packedTile32768 654780672 654846208 13 3189 25588 29 _ _ (101499 / 5000) (2029983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654846208 :
    ThetaLowerSegment 654846208 654911744 (65481795554051 / 100000) (65488319941911 / 100000) := by
  exact
    packedTile32768 654846208 654911744 13 3214 25589 29 _ _ (202999 / 10000) (2029993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654911744 :
    ThetaLowerSegment 654911744 654977280 (65488319941911 / 100000) (65494750981911 / 100000) := by
  exact
    packedTile32768 654911744 654977280 13 3168 25591 29 _ _ (203 / 10) (2030003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell654977280 :
    ThetaLowerSegment 654977280 655042816 (65494750981911 / 100000) (65501423624781 / 100000) := by
  exact
    packedTile32768 654977280 655042816 13 3287 25592 29 _ _ (203001 / 10000) (2030013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655042816 :
    ThetaLowerSegment 655042816 655108352 (65501423624781 / 100000) (65507927808861 / 100000) := by
  exact
    packedTile32768 655042816 655108352 13 3204 25593 29 _ _ (101501 / 5000) (2030023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655108352 :
    ThetaLowerSegment 655108352 655173888 (65507927808861 / 100000) (65514417814771 / 100000) := by
  exact
    packedTile32768 655108352 655173888 13 3197 25595 29 _ _ (203003 / 10000) (2030033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655173888 :
    ThetaLowerSegment 655173888 655239424 (65514417814771 / 100000) (65521108826611 / 100000) := by
  exact
    packedTile32768 655173888 655239424 13 3296 25596 29 _ _ (50751 / 2500) (2030043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655239424 :
    ThetaLowerSegment 655239424 655304960 (65521108826611 / 100000) (65527562355561 / 100000) := by
  exact
    packedTile32768 655239424 655304960 13 3179 25597 29 _ _ (40601 / 2000) (2030053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655304960 :
    ThetaLowerSegment 655304960 655370496 (65527562355561 / 100000) (65534160050561 / 100000) := by
  exact
    packedTile32768 655304960 655370496 13 3250 25598 29 _ _ (101503 / 5000) (2030063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655370496 :
    ThetaLowerSegment 655370496 655436032 (65534160050561 / 100000) (65540573041691 / 100000) := by
  exact
    packedTile32768 655370496 655436032 13 3159 25600 29 _ _ (203007 / 10000) (2030073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655436032 :
    ThetaLowerSegment 655436032 655501568 (65540573041691 / 100000) (65547195162651 / 100000) := by
  exact
    packedTile32768 655436032 655501568 13 3262 25601 29 _ _ (12688 / 625) (2030083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655501568 :
    ThetaLowerSegment 655501568 655567104 (65547195162651 / 100000) (65553717841821 / 100000) := by
  exact
    packedTile32768 655501568 655567104 13 3213 25602 29 _ _ (203009 / 10000) (2030093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655567104 :
    ThetaLowerSegment 655567104 655632640 (65553717841821 / 100000) (65560161379221 / 100000) := by
  exact
    packedTile32768 655567104 655632640 13 3174 25604 29 _ _ (20301 / 1000) (2030103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655632640 :
    ThetaLowerSegment 655632640 655698176 (65560161379221 / 100000) (65566568406381 / 100000) := by
  exact
    packedTile32768 655632640 655698176 13 3156 25605 29 _ _ (203011 / 10000) (2030113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655698176 :
    ThetaLowerSegment 655698176 655763712 (65566568406381 / 100000) (65573233290341 / 100000) := by
  exact
    packedTile32768 655698176 655763712 13 3283 25606 29 _ _ (50753 / 2500) (2030123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655763712 :
    ThetaLowerSegment 655763712 655829248 (65573233290341 / 100000) (65579808881411 / 100000) := by
  exact
    packedTile32768 655763712 655829248 13 3239 25607 29 _ _ (203013 / 10000) (2030133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655829248 :
    ThetaLowerSegment 655829248 655894784 (65579808881411 / 100000) (65586423077531 / 100000) := by
  exact
    packedTile32768 655829248 655894784 13 3258 25609 29 _ _ (101507 / 5000) (2030143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655894784 :
    ThetaLowerSegment 655894784 655960320 (65586423077531 / 100000) (65592937828881 / 100000) := by
  exact
    packedTile32768 655894784 655960320 13 3209 25610 29 _ _ (40603 / 2000) (2030153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell655960320 :
    ThetaLowerSegment 655960320 656025856 (65592937828881 / 100000) (65599627206081 / 100000) := by
  exact
    packedTile32768 655960320 656025856 13 3295 25611 29 _ _ (25377 / 1250) (2030163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656025856 :
    ThetaLowerSegment 656025856 656091392 (65599627206081 / 100000) (65606219168071 / 100000) := by
  exact
    packedTile32768 656025856 656091392 13 3247 25613 29 _ _ (203017 / 10000) (2030173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656091392 :
    ThetaLowerSegment 656091392 656156928 (65606219168071 / 100000) (65612798981451 / 100000) := by
  exact
    packedTile32768 656091392 656156928 13 3241 25614 29 _ _ (101509 / 5000) (2030183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656156928 :
    ThetaLowerSegment 656156928 656222464 (65612798981451 / 100000) (65619297619641 / 100000) := by
  exact
    packedTile32768 656156928 656222464 13 3201 25615 29 _ _ (203019 / 10000) (2030193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656222464 :
    ThetaLowerSegment 656222464 656288000 (65619297619641 / 100000) (65625918101841 / 100000) := by
  exact
    packedTile32768 656222464 656288000 13 3261 25616 29 _ _ (10151 / 500) (2030203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656288000 :
    ThetaLowerSegment 656288000 656353536 (65625918101841 / 100000) (65632475680141 / 100000) := by
  exact
    packedTile32768 656288000 656353536 13 3230 25618 29 _ _ (203021 / 10000) (2030213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656353536 :
    ThetaLowerSegment 656353536 656419072 (65632475680141 / 100000) (65639041411621 / 100000) := by
  exact
    packedTile32768 656353536 656419072 13 3234 25619 29 _ _ (101511 / 5000) (2030223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656419072 :
    ThetaLowerSegment 656419072 656484608 (65639041411621 / 100000) (16411361696029 / 25000) := by
  exact
    packedTile32768 656419072 656484608 13 3155 25620 29 _ _ (2030229 / 100000) (253779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656484608 :
    ThetaLowerSegment 656484608 656550144 (16411361696029 / 25000) (65651961821067 / 100000) := by
  exact
    packedTile32768 656484608 656550144 13 3209 25621 29 _ _ (2030239 / 100000) (1015121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656550144 :
    ThetaLowerSegment 656550144 656615680 (65651961821067 / 100000) (65658576372309 / 100000) := by
  exact
    packedTile32768 656550144 656615680 13 3258 25623 29 _ _ (2030249 / 100000) (507563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656615680 :
    ThetaLowerSegment 656615680 656681216 (65658576372309 / 100000) (65665174714059 / 100000) := by
  exact
    packedTile32768 656615680 656681216 13 3250 25624 29 _ _ (2030259 / 100000) (1015131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656681216 :
    ThetaLowerSegment 656681216 656746752 (65665174714059 / 100000) (65671764967233 / 100000) := by
  exact
    packedTile32768 656681216 656746752 13 3246 25625 29 _ _ (2030269 / 100000) (63446 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656746752 :
    ThetaLowerSegment 656746752 656812288 (65671764967233 / 100000) (65678290283939 / 100000) := by
  exact
    packedTile32768 656746752 656812288 13 3214 25627 29 _ _ (2030279 / 100000) (1015141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656812288 :
    ThetaLowerSegment 656812288 656877824 (65678290283939 / 100000) (65684892783767 / 100000) := by
  exact
    packedTile32768 656812288 656877824 13 3252 25628 29 _ _ (2030289 / 100000) (507573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656877824 :
    ThetaLowerSegment 656877824 656943360 (65684892783767 / 100000) (16422867230557 / 25000) := by
  exact
    packedTile32768 656877824 656943360 13 3239 25629 29 _ _ (2030299 / 100000) (1015151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell656943360 :
    ThetaLowerSegment 656943360 657008896 (16422867230557 / 25000) (32849005288913 / 50000) := by
  exact
    packedTile32768 656943360 657008896 13 3222 25630 29 _ _ (2030309 / 100000) (253789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657008896 :
    ThetaLowerSegment 657008896 657074432 (32849005288913 / 50000) (6570454008373 / 10000) := by
  exact
    packedTile32768 657008896 657074432 13 3216 25632 29 _ _ (2030319 / 100000) (1015161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657074432 :
    ThetaLowerSegment 657074432 657139968 (6570454008373 / 10000) (32855563235503 / 50000) := by
  exact
    packedTile32768 657074432 657139968 13 3244 25633 29 _ _ (2030329 / 100000) (507583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657139968 :
    ThetaLowerSegment 657139968 657205504 (32855563235503 / 50000) (65717710860383 / 100000) := by
  exact
    packedTile32768 657139968 657205504 13 3243 25634 29 _ _ (2030339 / 100000) (1015171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657205504 :
    ThetaLowerSegment 657205504 657271040 (65717710860383 / 100000) (16431064683977 / 25000) := by
  exact
    packedTile32768 657205504 657271040 13 3225 25636 29 _ _ (2030349 / 100000) (126897 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657271040 :
    ThetaLowerSegment 657271040 657336576 (16431064683977 / 25000) (4108178841461 / 6250) := by
  exact
    packedTile32768 657271040 657336576 13 3252 25637 29 _ _ (2030359 / 100000) (1015181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657336576 :
    ThetaLowerSegment 657336576 657402112 (4108178841461 / 6250) (16434370116579 / 25000) := by
  exact
    packedTile32768 657336576 657402112 13 3260 25638 29 _ _ (2030369 / 100000) (507593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657402112 :
    ThetaLowerSegment 657402112 657467648 (16434370116579 / 25000) (32872039599033 / 50000) := by
  exact
    packedTile32768 657402112 657467648 13 3250 25639 29 _ _ (2030379 / 100000) (1015191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657467648 :
    ThetaLowerSegment 657467648 657533184 (32872039599033 / 50000) (65750533804697 / 100000) := by
  exact
    packedTile32768 657467648 657533184 13 3179 25641 29 _ _ (2030389 / 100000) (253799 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657533184 :
    ThetaLowerSegment 657533184 657598720 (65750533804697 / 100000) (65757201635013 / 100000) := by
  exact
    packedTile32768 657533184 657598720 13 3284 25642 29 _ _ (2030399 / 100000) (1015201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657598720 :
    ThetaLowerSegment 657598720 657664256 (65757201635013 / 100000) (411023156469 / 625) := by
  exact
    packedTile32768 657598720 657664256 13 3203 25643 29 _ _ (2030409 / 100000) (507603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657664256 :
    ThetaLowerSegment 657664256 657729792 (411023156469 / 625) (6577022268003 / 10000) := by
  exact
    packedTile32768 657664256 657729792 13 3210 25644 29 _ _ (2030419 / 100000) (1015211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657729792 :
    ThetaLowerSegment 657729792 657795328 (6577022268003 / 10000) (3288843109143 / 5000) := by
  exact
    packedTile32768 657729792 657795328 13 3270 25646 29 _ _ (2030429 / 100000) (63451 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657795328 :
    ThetaLowerSegment 657795328 657860864 (3288843109143 / 5000) (65783406287757 / 100000) := by
  exact
    packedTile32768 657795328 657860864 13 3223 25647 29 _ _ (2030439 / 100000) (1015221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657860864 :
    ThetaLowerSegment 657860864 657926400 (65783406287757 / 100000) (32894977242891 / 50000) := by
  exact
    packedTile32768 657860864 657926400 13 3225 25648 29 _ _ (2030449 / 100000) (507613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657926400 :
    ThetaLowerSegment 657926400 657991936 (32894977242891 / 50000) (65796462106877 / 100000) := by
  exact
    packedTile32768 657926400 657991936 13 3205 25650 29 _ _ (2030459 / 100000) (1015231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell657991936 :
    ThetaLowerSegment 657991936 658057472 (65796462106877 / 100000) (16450729241957 / 25000) := by
  exact
    packedTile32768 657991936 658057472 13 3179 25651 29 _ _ (2030469 / 100000) (253809 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658057472 :
    ThetaLowerSegment 658057472 658123008 (16450729241957 / 25000) (32904749890373 / 50000) := by
  exact
    packedTile32768 658057472 658123008 13 3242 25652 29 _ _ (2030479 / 100000) (1015241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658123008 :
    ThetaLowerSegment 658123008 658188544 (32904749890373 / 50000) (13163195814229 / 20000) := by
  exact
    packedTile32768 658123008 658188544 13 3191 25653 29 _ _ (2030489 / 100000) (507623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658188544 :
    ThetaLowerSegment 658188544 658254080 (13163195814229 / 20000) (6582258834539 / 10000) := by
  exact
    packedTile32768 658188544 658254080 13 3255 25655 29 _ _ (2030499 / 100000) (1015251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658254080 :
    ThetaLowerSegment 658254080 658319616 (6582258834539 / 10000) (32914575475239 / 50000) := by
  exact
    packedTile32768 658254080 658319616 13 3232 25656 29 _ _ (2030509 / 100000) (126907 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658319616 :
    ThetaLowerSegment 658319616 658385152 (32914575475239 / 50000) (16458933473269 / 25000) := by
  exact
    packedTile32768 658319616 658385152 13 3242 25657 29 _ _ (2030519 / 100000) (1015261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658385152 :
    ThetaLowerSegment 658385152 658450688 (16458933473269 / 25000) (32921109701351 / 50000) := by
  exact
    packedTile32768 658385152 658450688 13 3194 25659 29 _ _ (2030529 / 100000) (507633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658450688 :
    ThetaLowerSegment 658450688 658516224 (32921109701351 / 50000) (65848820684991 / 100000) := by
  exact
    packedTile32768 658450688 658516224 13 3251 25660 29 _ _ (2030539 / 100000) (1015271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658516224 :
    ThetaLowerSegment 658516224 658581760 (65848820684991 / 100000) (65855279858179 / 100000) := by
  exact
    packedTile32768 658516224 658581760 13 3181 25661 29 _ _ (507637 / 25000) (2030551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658581760 :
    ThetaLowerSegment 658581760 658647296 (65855279858179 / 100000) (65861877141121 / 100000) := by
  exact
    packedTile32768 658581760 658647296 13 3249 25662 29 _ _ (1015279 / 50000) (2030561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658647296 :
    ThetaLowerSegment 658647296 658712832 (65861877141121 / 100000) (65868425722921 / 100000) := by
  exact
    packedTile32768 658647296 658712832 13 3225 25664 29 _ _ (253821 / 12500) (2030571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658712832 :
    ThetaLowerSegment 658712832 658778368 (65868425722921 / 100000) (65874876869227 / 100000) := by
  exact
    packedTile32768 658712832 658778368 13 3177 25665 29 _ _ (1015289 / 50000) (2030581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658778368 :
    ThetaLowerSegment 658778368 658843904 (65874876869227 / 100000) (65881338200243 / 100000) := by
  exact
    packedTile32768 658778368 658843904 13 3182 25666 29 _ _ (507647 / 25000) (2030591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658843904 :
    ThetaLowerSegment 658843904 658909440 (65881338200243 / 100000) (13177607428609 / 20000) := by
  exact
    packedTile32768 658843904 658909440 13 3299 25667 29 _ _ (1015299 / 50000) (2030601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658909440 :
    ThetaLowerSegment 658909440 658974976 (13177607428609 / 20000) (65894732057621 / 100000) := by
  exact
    packedTile32768 658909440 658974976 13 3297 25669 29 _ _ (126913 / 6250) (2030611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell658974976 :
    ThetaLowerSegment 658974976 659040512 (65894732057621 / 100000) (2636049445083 / 4000) := by
  exact
    packedTile32768 658974976 659040512 13 3203 25670 29 _ _ (1015309 / 50000) (2030621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659040512 :
    ThetaLowerSegment 659040512 659106048 (2636049445083 / 4000) (65907699615999 / 100000) := by
  exact
    packedTile32768 659040512 659106048 13 3183 25671 29 _ _ (507657 / 25000) (2030631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659106048 :
    ThetaLowerSegment 659106048 659171584 (65907699615999 / 100000) (65914331679707 / 100000) := by
  exact
    packedTile32768 659106048 659171584 13 3266 25673 29 _ _ (1015319 / 50000) (2030641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659171584 :
    ThetaLowerSegment 659171584 659237120 (65914331679707 / 100000) (65920992205147 / 100000) := by
  exact
    packedTile32768 659171584 659237120 13 3280 25674 29 _ _ (253831 / 12500) (2030651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659237120 :
    ThetaLowerSegment 659237120 659302656 (65920992205147 / 100000) (13185520805519 / 20000) := by
  exact
    packedTile32768 659237120 659302656 13 3256 25675 29 _ _ (1015329 / 50000) (2030661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659302656 :
    ThetaLowerSegment 659302656 659368192 (13185520805519 / 20000) (65934201667927 / 100000) := by
  exact
    packedTile32768 659302656 659368192 13 3249 25676 29 _ _ (507667 / 25000) (2030671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659368192 :
    ThetaLowerSegment 659368192 659433728 (65934201667927 / 100000) (65940716082951 / 100000) := by
  exact
    packedTile32768 659368192 659433728 13 3208 25678 29 _ _ (1015339 / 50000) (2030681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659433728 :
    ThetaLowerSegment 659433728 659499264 (65940716082951 / 100000) (65947325972391 / 100000) := by
  exact
    packedTile32768 659433728 659499264 13 3255 25679 29 _ _ (63459 / 3125) (2030691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659499264 :
    ThetaLowerSegment 659499264 659564800 (65947325972391 / 100000) (65953751100863 / 100000) := by
  exact
    packedTile32768 659499264 659564800 13 3164 25680 29 _ _ (1015349 / 50000) (2030701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659564800 :
    ThetaLowerSegment 659564800 659630336 (65953751100863 / 100000) (2638413142563 / 4000) := by
  exact
    packedTile32768 659564800 659630336 13 3239 25681 29 _ _ (507677 / 25000) (2030711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659630336 :
    ThetaLowerSegment 659630336 659695872 (2638413142563 / 4000) (65966926366857 / 100000) := by
  exact
    packedTile32768 659630336 659695872 13 3249 25683 29 _ _ (1015359 / 50000) (2030721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659695872 :
    ThetaLowerSegment 659695872 659761408 (65966926366857 / 100000) (65973522168153 / 100000) := by
  exact
    packedTile32768 659695872 659761408 13 3248 25684 29 _ _ (2030727 / 100000) (203073 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659761408 :
    ThetaLowerSegment 659761408 659826944 (65973522168153 / 100000) (65980061141293 / 100000) := by
  exact
    packedTile32768 659761408 659826944 13 3220 25685 29 _ _ (2030737 / 100000) (101537 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659826944 :
    ThetaLowerSegment 659826944 659892480 (65980061141293 / 100000) (65986685438007 / 100000) := by
  exact
    packedTile32768 659826944 659892480 13 3262 25687 29 _ _ (2030747 / 100000) (8123 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659892480 :
    ThetaLowerSegment 659892480 659958016 (65986685438007 / 100000) (2639729303943 / 4000) := by
  exact
    packedTile32768 659892480 659958016 13 3224 25688 29 _ _ (2030757 / 100000) (50769 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell659958016 :
    ThetaLowerSegment 659958016 660023552 (2639729303943 / 4000) (65999641699227 / 100000) := by
  exact
    packedTile32768 659958016 660023552 13 3156 25689 29 _ _ (2030767 / 100000) (203077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660023552 :
    ThetaLowerSegment 660023552 660089088 (65999641699227 / 100000) (13201254031071 / 20000) := by
  exact
    packedTile32768 660023552 660089088 13 3264 25690 29 _ _ (2030777 / 100000) (101539 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660089088 :
    ThetaLowerSegment 660089088 660154624 (13201254031071 / 20000) (16503222122547 / 25000) := by
  exact
    packedTile32768 660089088 660154624 13 3259 25692 29 _ _ (2030787 / 100000) (203079 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660154624 :
    ThetaLowerSegment 660154624 660220160 (16503222122547 / 25000) (16504838636959 / 25000) := by
  exact
    packedTile32768 660154624 660220160 13 3184 25693 29 _ _ (2030797 / 100000) (5077 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660220160 :
    ThetaLowerSegment 660220160 660285696 (16504838636959 / 25000) (66025940454937 / 100000) := by
  exact
    packedTile32768 660220160 660285696 13 3243 25694 29 _ _ (2030807 / 100000) (203081 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660285696 :
    ThetaLowerSegment 660285696 660351232 (66025940454937 / 100000) (8254058691449 / 12500) := by
  exact
    packedTile32768 660285696 660351232 13 3215 25696 29 _ _ (2030817 / 100000) (101541 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660351232 :
    ThetaLowerSegment 660351232 660416768 (8254058691449 / 12500) (4127442619019 / 6250) := by
  exact
    packedTile32768 660351232 660416768 13 3256 25697 29 _ _ (2030827 / 100000) (203083 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660416768 :
    ThetaLowerSegment 660416768 660482304 (4127442619019 / 6250) (13209133581739 / 20000) := by
  exact
    packedTile32768 660416768 660482304 13 3243 25698 29 _ _ (2030837 / 100000) (50771 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660482304 :
    ThetaLowerSegment 660482304 660547840 (13209133581739 / 20000) (33026084324971 / 50000) := by
  exact
    packedTile32768 660482304 660547840 13 3201 25699 29 _ _ (2030847 / 100000) (40617 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660547840 :
    ThetaLowerSegment 660547840 660613376 (33026084324971 / 50000) (16514665832657 / 25000) := by
  exact
    packedTile32768 660547840 660613376 13 3198 25701 29 _ _ (2030857 / 100000) (101543 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660613376 :
    ThetaLowerSegment 660613376 660678912 (16514665832657 / 25000) (33032640961461 / 50000) := by
  exact
    packedTile32768 660613376 660678912 13 3259 25702 29 _ _ (1015433 / 50000) (2030869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660678912 :
    ThetaLowerSegment 660678912 660744448 (33032640961461 / 50000) (33035927934267 / 50000) := by
  exact
    packedTile32768 660678912 660744448 13 3237 25703 29 _ _ (507719 / 25000) (2030879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660744448 :
    ThetaLowerSegment 660744448 660809984 (33035927934267 / 50000) (3303917836731 / 5000) := by
  exact
    packedTile32768 660744448 660809984 13 3201 25704 29 _ _ (1015443 / 50000) (2030889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660809984 :
    ThetaLowerSegment 660809984 660875520 (3303917836731 / 5000) (16521245379343 / 25000) := by
  exact
    packedTile32768 660809984 660875520 13 3262 25706 29 _ _ (126931 / 6250) (2030899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660875520 :
    ThetaLowerSegment 660875520 660941056 (16521245379343 / 25000) (6609156774553 / 10000) := by
  exact
    packedTile32768 660875520 660941056 13 3243 25707 29 _ _ (1015453 / 50000) (2030909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell660941056 :
    ThetaLowerSegment 660941056 661006592 (6609156774553 / 10000) (6609809714047 / 10000) := by
  exact
    packedTile32768 660941056 661006592 13 3215 25708 29 _ _ (507729 / 25000) (2030919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661006592 :
    ThetaLowerSegment 661006592 661072128 (6609809714047 / 10000) (264419034311 / 400) := by
  exact
    packedTile32768 661006592 661072128 13 3280 25710 29 _ _ (1015463 / 50000) (2030929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661072128 :
    ThetaLowerSegment 661072128 661137664 (264419034311 / 400) (33055673467067 / 50000) := by
  exact
    packedTile32768 661072128 661137664 13 3244 25711 29 _ _ (253867 / 12500) (2030939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661137664 :
    ThetaLowerSegment 661137664 661203200 (33055673467067 / 50000) (3305893415087 / 5000) := by
  exact
    packedTile32768 661137664 661203200 13 3211 25712 29 _ _ (1015473 / 50000) (2030949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661203200 :
    ThetaLowerSegment 661203200 661268736 (3305893415087 / 5000) (16531094886669 / 25000) := by
  exact
    packedTile32768 661203200 661268736 13 3206 25713 29 _ _ (507739 / 25000) (2030959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661268736 :
    ThetaLowerSegment 661268736 661334272 (16531094886669 / 25000) (33065470798911 / 50000) := by
  exact
    packedTile32768 661268736 661334272 13 3231 25715 29 _ _ (1015483 / 50000) (2030969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661334272 :
    ThetaLowerSegment 661334272 661399808 (33065470798911 / 50000) (16534369318843 / 25000) := by
  exact
    packedTile32768 661334272 661399808 13 3218 25716 29 _ _ (81239 / 4000) (1015489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661399808 :
    ThetaLowerSegment 661399808 661465344 (16534369318843 / 25000) (16536006292753 / 25000) := by
  exact
    packedTile32768 661399808 661465344 13 3224 25717 29 _ _ (406197 / 20000) (507747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661465344 :
    ThetaLowerSegment 661465344 661530880 (16536006292753 / 25000) (33075308890391 / 50000) := by
  exact
    packedTile32768 661465344 661530880 13 3246 25718 29 _ _ (406199 / 20000) (1015499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661530880 :
    ThetaLowerSegment 661530880 661596416 (33075308890391 / 50000) (66157322128287 / 100000) := by
  exact
    packedTile32768 661530880 661596416 13 3301 25720 29 _ _ (406201 / 20000) (63469 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661596416 :
    ThetaLowerSegment 661596416 661661952 (66157322128287 / 100000) (66163902616887 / 100000) := by
  exact
    packedTile32768 661596416 661661952 13 3240 25721 29 _ _ (406203 / 20000) (1015509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661661952 :
    ThetaLowerSegment 661661952 661727488 (66163902616887 / 100000) (66170466889687 / 100000) := by
  exact
    packedTile32768 661661952 661727488 13 3232 25722 29 _ _ (81241 / 4000) (507757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661727488 :
    ThetaLowerSegment 661727488 661793024 (66170466889687 / 100000) (33088447557731 / 50000) := by
  exact
    packedTile32768 661727488 661793024 13 3165 25724 29 _ _ (406207 / 20000) (1015519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661793024 :
    ThetaLowerSegment 661793024 661858560 (33088447557731 / 50000) (66183441173497 / 100000) := by
  exact
    packedTile32768 661793024 661858560 13 3223 25725 29 _ _ (406209 / 20000) (253881 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661858560 :
    ThetaLowerSegment 661858560 661924096 (66183441173497 / 100000) (66189985232707 / 100000) := by
  exact
    packedTile32768 661858560 661924096 13 3222 25726 29 _ _ (406211 / 20000) (1015529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661924096 :
    ThetaLowerSegment 661924096 661989632 (66189985232707 / 100000) (66196521199877 / 100000) := by
  exact
    packedTile32768 661924096 661989632 13 3218 25727 29 _ _ (406213 / 20000) (507767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell661989632 :
    ThetaLowerSegment 661989632 662055168 (66196521199877 / 100000) (66203118131477 / 100000) := by
  exact
    packedTile32768 661989632 662055168 13 3248 25729 29 _ _ (81243 / 4000) (1015539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662055168 :
    ThetaLowerSegment 662055168 662120704 (66203118131477 / 100000) (66209711030141 / 100000) := by
  exact
    packedTile32768 662055168 662120704 13 3246 25730 29 _ _ (507771 / 25000) (2031087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662120704 :
    ThetaLowerSegment 662120704 662186240 (66209711030141 / 100000) (66216308023453 / 100000) := by
  exact
    packedTile32768 662120704 662186240 13 3248 25731 29 _ _ (1015547 / 50000) (2031097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662186240 :
    ThetaLowerSegment 662186240 662251776 (66216308023453 / 100000) (66222939578013 / 100000) := by
  exact
    packedTile32768 662186240 662251776 13 3265 25732 29 _ _ (63472 / 3125) (2031107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662251776 :
    ThetaLowerSegment 662251776 662317312 (66222939578013 / 100000) (66229372116051 / 100000) := by
  exact
    packedTile32768 662251776 662317312 13 3167 25734 29 _ _ (1015557 / 50000) (2031117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662317312 :
    ThetaLowerSegment 662317312 662382848 (66229372116051 / 100000) (66235906241959 / 100000) := by
  exact
    packedTile32768 662317312 662382848 13 3217 25735 29 _ _ (507781 / 25000) (2031127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662382848 :
    ThetaLowerSegment 662382848 662448384 (66235906241959 / 100000) (66242493209521 / 100000) := by
  exact
    packedTile32768 662382848 662448384 13 3243 25736 29 _ _ (1015567 / 50000) (2031137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662448384 :
    ThetaLowerSegment 662448384 662513920 (66242493209521 / 100000) (66249108645529 / 100000) := by
  exact
    packedTile32768 662448384 662513920 13 3257 25738 29 _ _ (253893 / 12500) (2031147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662513920 :
    ThetaLowerSegment 662513920 662579456 (66249108645529 / 100000) (66255638805639 / 100000) := by
  exact
    packedTile32768 662513920 662579456 13 3215 25739 29 _ _ (1015577 / 50000) (2031157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662579456 :
    ThetaLowerSegment 662579456 662644992 (66255638805639 / 100000) (66262110094143 / 100000) := by
  exact
    packedTile32768 662579456 662644992 13 3186 25740 29 _ _ (507791 / 25000) (2031167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662644992 :
    ThetaLowerSegment 662644992 662710528 (66262110094143 / 100000) (16567193593189 / 25000) := by
  exact
    packedTile32768 662644992 662710528 13 3281 25741 29 _ _ (2031173 / 100000) (253897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662710528 :
    ThetaLowerSegment 662710528 662776064 (16567193593189 / 25000) (1325506214393 / 2000) := by
  exact
    packedTile32768 662710528 662776064 13 3218 25743 29 _ _ (2031183 / 100000) (1015593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662776064 :
    ThetaLowerSegment 662776064 662841600 (1325506214393 / 2000) (33140941830099 / 50000) := by
  exact
    packedTile32768 662776064 662841600 13 3236 25744 29 _ _ (2031193 / 100000) (507799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662841600 :
    ThetaLowerSegment 662841600 662907136 (33140941830099 / 50000) (33144199879711 / 50000) := by
  exact
    packedTile32768 662841600 662907136 13 3208 25745 29 _ _ (2031203 / 100000) (1015603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662907136 :
    ThetaLowerSegment 662907136 662972672 (33144199879711 / 50000) (8286854838079 / 12500) := by
  exact
    packedTile32768 662907136 662972672 13 3170 25746 29 _ _ (2031213 / 100000) (126951 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell662972672 :
    ThetaLowerSegment 662972672 663038208 (8286854838079 / 12500) (66301332524563 / 100000) := by
  exact
    packedTile32768 662972672 663038208 13 3197 25748 29 _ _ (2031223 / 100000) (1015613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663038208 :
    ThetaLowerSegment 663038208 663103744 (66301332524563 / 100000) (13261568119019 / 20000) := by
  exact
    packedTile32768 663038208 663103744 13 3204 25749 29 _ _ (2031233 / 100000) (507809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663103744 :
    ThetaLowerSegment 663103744 663169280 (13261568119019 / 20000) (66314466509761 / 100000) := by
  exact
    packedTile32768 663103744 663169280 13 3262 25750 29 _ _ (2031243 / 100000) (1015623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663169280 :
    ThetaLowerSegment 663169280 663234816 (66314466509761 / 100000) (66321027456951 / 100000) := by
  exact
    packedTile32768 663169280 663234816 13 3230 25752 29 _ _ (2031253 / 100000) (253907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663234816 :
    ThetaLowerSegment 663234816 663300352 (66321027456951 / 100000) (66327596558259 / 100000) := by
  exact
    packedTile32768 663234816 663300352 13 3234 25753 29 _ _ (1015631 / 50000) (406253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663300352 :
    ThetaLowerSegment 663300352 663365888 (66327596558259 / 100000) (13266828669583 / 20000) := by
  exact
    packedTile32768 663300352 663365888 13 3223 25754 29 _ _ (253909 / 12500) (81251 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663365888 :
    ThetaLowerSegment 663365888 663431424 (13266828669583 / 20000) (2653630206833 / 4000) := by
  exact
    packedTile32768 663365888 663431424 13 3255 25755 29 _ _ (1015641 / 50000) (406257 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663431424 :
    ThetaLowerSegment 663431424 663496960 (2653630206833 / 4000) (13269459186213 / 20000) := by
  exact
    packedTile32768 663431424 663496960 13 3220 25757 29 _ _ (507823 / 25000) (406259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663496960 :
    ThetaLowerSegment 663496960 663562496 (13269459186213 / 20000) (66353844848713 / 100000) := by
  exact
    packedTile32768 663496960 663562496 13 3224 25758 29 _ _ (1015651 / 50000) (406261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663562496 :
    ThetaLowerSegment 663562496 663628032 (66353844848713 / 100000) (66360460831897 / 100000) := by
  exact
    packedTile32768 663562496 663628032 13 3257 25759 29 _ _ (126957 / 6250) (406263 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663628032 :
    ThetaLowerSegment 663628032 663693568 (66360460831897 / 100000) (66366981375517 / 100000) := by
  exact
    packedTile32768 663628032 663693568 13 3210 25760 29 _ _ (1015661 / 50000) (81253 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663693568 :
    ThetaLowerSegment 663693568 663759104 (66366981375517 / 100000) (66373593361177 / 100000) := by
  exact
    packedTile32768 663693568 663759104 13 3255 25762 29 _ _ (507833 / 25000) (406267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663759104 :
    ThetaLowerSegment 663759104 663824640 (66373593361177 / 100000) (66380085527013 / 100000) := by
  exact
    packedTile32768 663759104 663824640 13 3196 25763 29 _ _ (2031341 / 100000) (126959 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663824640 :
    ThetaLowerSegment 663824640 663890176 (66380085527013 / 100000) (6638672195073 / 10000) := by
  exact
    packedTile32768 663824640 663890176 13 3267 25764 29 _ _ (2031351 / 100000) (1015677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663890176 :
    ThetaLowerSegment 663890176 663955712 (6638672195073 / 10000) (66393297466287 / 100000) := by
  exact
    packedTile32768 663890176 663955712 13 3237 25766 29 _ _ (2031361 / 100000) (507841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell663955712 :
    ThetaLowerSegment 663955712 664021248 (66393297466287 / 100000) (33199928381623 / 50000) := by
  exact
    packedTile32768 663955712 664021248 13 3229 25767 29 _ _ (2031371 / 100000) (1015687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664021248 :
    ThetaLowerSegment 664021248 664086784 (33199928381623 / 50000) (13281279155737 / 20000) := by
  exact
    packedTile32768 664021248 664086784 13 3219 25768 29 _ _ (2031381 / 100000) (253923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664086784 :
    ThetaLowerSegment 664086784 664152320 (13281279155737 / 20000) (33206430848119 / 50000) := by
  exact
    packedTile32768 664086784 664152320 13 3183 25769 29 _ _ (2031391 / 100000) (1015697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664152320 :
    ThetaLowerSegment 664152320 664217856 (33206430848119 / 50000) (16604863905971 / 25000) := by
  exact
    packedTile32768 664152320 664217856 13 3246 25771 29 _ _ (2031401 / 100000) (507851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664217856 :
    ThetaLowerSegment 664217856 664283392 (16604863905971 / 25000) (1660650731747 / 2500) := by
  exact
    packedTile32768 664217856 664283392 13 3236 25772 29 _ _ (2031411 / 100000) (1015707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664283392 :
    ThetaLowerSegment 664283392 664348928 (1660650731747 / 2500) (1660814870483 / 2500) := by
  exact
    packedTile32768 664283392 664348928 13 3232 25773 29 _ _ (101571 / 5000) (2031423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664348928 :
    ThetaLowerSegment 664348928 664414464 (1660814870483 / 2500) (6643916649537 / 10000) := by
  exact
    packedTile32768 664348928 664414464 13 3235 25774 29 _ _ (203143 / 10000) (2031433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664414464 :
    ThetaLowerSegment 664414464 664480000 (6643916649537 / 10000) (6644559194009 / 10000) := by
  exact
    packedTile32768 664414464 664480000 13 3163 25776 29 _ _ (25393 / 1250) (2031443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664480000 :
    ThetaLowerSegment 664480000 664545536 (6644559194009 / 10000) (6645219415259 / 10000) := by
  exact
    packedTile32768 664480000 664545536 13 3250 25777 29 _ _ (40629 / 2000) (2031453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664545536 :
    ThetaLowerSegment 664545536 664611072 (6645219415259 / 10000) (6645882077511 / 10000) := by
  exact
    packedTile32768 664545536 664611072 13 3262 25778 29 _ _ (101573 / 5000) (2031463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664611072 :
    ThetaLowerSegment 664611072 664676608 (6645882077511 / 10000) (6646528897559 / 10000) := by
  exact
    packedTile32768 664611072 664676608 13 3184 25780 29 _ _ (203147 / 10000) (2031473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664676608 :
    ThetaLowerSegment 664676608 664742144 (6646528897559 / 10000) (6647176127087 / 10000) := by
  exact
    packedTile32768 664676608 664742144 13 3186 25781 29 _ _ (50787 / 2500) (2031483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664742144 :
    ThetaLowerSegment 664742144 664807680 (6647176127087 / 10000) (66478247815247 / 100000) := by
  exact
    packedTile32768 664742144 664807680 13 3193 25782 29 _ _ (2031489 / 100000) (507873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664807680 :
    ThetaLowerSegment 664807680 664873216 (66478247815247 / 100000) (33242322502799 / 50000) := by
  exact
    packedTile32768 664807680 664873216 13 3149 25783 29 _ _ (2031499 / 100000) (1015751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664873216 :
    ThetaLowerSegment 664873216 664938752 (33242322502799 / 50000) (33245597295307 / 50000) := by
  exact
    packedTile32768 664873216 664938752 13 3224 25785 29 _ _ (2031509 / 100000) (253939 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell664938752 :
    ThetaLowerSegment 664938752 665004288 (33245597295307 / 50000) (66497729987237 / 100000) := by
  exact
    packedTile32768 664938752 665004288 13 3217 25786 29 _ _ (2031519 / 100000) (1015761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665004288 :
    ThetaLowerSegment 665004288 665069824 (66497729987237 / 100000) (415652293703 / 625) := by
  exact
    packedTile32768 665004288 665069824 13 3267 25787 29 _ _ (2031529 / 100000) (507883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665069824 :
    ThetaLowerSegment 665069824 665135360 (415652293703 / 625) (33255513188661 / 50000) := by
  exact
    packedTile32768 665069824 665135360 13 3278 25788 29 _ _ (2031539 / 100000) (1015771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665135360 :
    ThetaLowerSegment 665135360 665200896 (33255513188661 / 50000) (33258832739727 / 50000) := by
  exact
    packedTile32768 665135360 665200896 13 3268 25790 29 _ _ (2031549 / 100000) (63486 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665200896 :
    ThetaLowerSegment 665200896 665266432 (33258832739727 / 50000) (415776383232 / 625) := by
  exact
    packedTile32768 665200896 665266432 13 3227 25791 29 _ _ (1015779 / 50000) (2031561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665266432 :
    ThetaLowerSegment 665266432 665331968 (415776383232 / 625) (4158166209757 / 6250) := by
  exact
    packedTile32768 665266432 665331968 13 3169 25792 29 _ _ (126973 / 6250) (2031571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665331968 :
    ThetaLowerSegment 665331968 665397504 (4158166209757 / 6250) (33268577155489 / 50000) := by
  exact
    packedTile32768 665331968 665397504 13 3197 25794 29 _ _ (1015789 / 50000) (2031581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665397504 :
    ThetaLowerSegment 665397504 665463040 (33268577155489 / 50000) (6654366351893 / 10000) := by
  exact
    packedTile32768 665397504 665463040 13 3204 25795 29 _ _ (507897 / 25000) (2031591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665463040 :
    ThetaLowerSegment 665463040 665528576 (6654366351893 / 10000) (33275137169411 / 50000) := by
  exact
    packedTile32768 665463040 665528576 13 3254 25796 29 _ _ (1015799 / 50000) (2031601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665528576 :
    ThetaLowerSegment 665528576 665594112 (33275137169411 / 50000) (33278442595627 / 50000) := by
  exact
    packedTile32768 665528576 665594112 13 3254 25797 29 _ _ (253951 / 12500) (2031611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665594112 :
    ThetaLowerSegment 665594112 665659648 (33278442595627 / 50000) (8320425581677 / 12500) := by
  exact
    packedTile32768 665594112 665659648 13 3209 25799 29 _ _ (1015809 / 50000) (2031621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665659648 :
    ThetaLowerSegment 665659648 665725184 (8320425581677 / 12500) (66570176066207 / 100000) := by
  exact
    packedTile32768 665659648 665725184 13 3333 25800 29 _ _ (2031627 / 100000) (203163 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665725184 :
    ThetaLowerSegment 665725184 665790720 (66570176066207 / 100000) (832207171139 / 1250) := by
  exact
    packedTile32768 665725184 665790720 13 3149 25801 29 _ _ (2031637 / 100000) (50791 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665790720 :
    ThetaLowerSegment 665790720 665856256 (832207171139 / 1250) (66583072929873 / 100000) := by
  exact
    packedTile32768 665790720 665856256 13 3199 25802 29 _ _ (2031647 / 100000) (40633 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665856256 :
    ThetaLowerSegment 665856256 665921792 (66583072929873 / 100000) (2080927686669 / 3125) := by
  exact
    packedTile32768 665856256 665921792 13 3255 25804 29 _ _ (2031657 / 100000) (101583 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665921792 :
    ThetaLowerSegment 665921792 665987328 (2080927686669 / 3125) (1664907527029 / 2500) := by
  exact
    packedTile32768 665921792 665987328 13 3256 25805 29 _ _ (2031667 / 100000) (203167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell665987328 :
    ThetaLowerSegment 665987328 666052864 (1664907527029 / 2500) (8325346242591 / 12500) := by
  exact
    packedTile32768 665987328 666052864 13 3184 25806 29 _ _ (2031677 / 100000) (12698 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666052864 :
    ThetaLowerSegment 666052864 666118400 (8325346242591 / 12500) (416308098226 / 625) := by
  exact
    packedTile32768 666052864 666118400 13 3212 25808 29 _ _ (1015843 / 50000) (2031689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666118400 :
    ThetaLowerSegment 666118400 666183936 (416308098226 / 625) (832698099197 / 1250) := by
  exact
    packedTile32768 666118400 666183936 13 3225 25809 29 _ _ (126981 / 6250) (2031699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666183936 :
    ThetaLowerSegment 666183936 666249472 (832698099197 / 1250) (2081948926519 / 3125) := by
  exact
    packedTile32768 666183936 666249472 13 3208 25810 29 _ _ (1015853 / 50000) (2031709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666249472 :
    ThetaLowerSegment 666249472 666315008 (2081948926519 / 3125) (16657238625899 / 25000) := by
  exact
    packedTile32768 666249472 666315008 13 3243 25811 29 _ _ (507929 / 25000) (2031719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666315008 :
    ThetaLowerSegment 666315008 666380544 (16657238625899 / 25000) (1665888127637 / 2500) := by
  exact
    packedTile32768 666315008 666380544 13 3234 25813 29 _ _ (1015863 / 50000) (2031729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666380544 :
    ThetaLowerSegment 666380544 666446080 (1665888127637 / 2500) (2082564412506 / 3125) := by
  exact
    packedTile32768 666380544 666446080 13 3217 25814 29 _ _ (253967 / 12500) (2031739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666446080 :
    ThetaLowerSegment 666446080 666511616 (2082564412506 / 3125) (8331064252789 / 12500) := by
  exact
    packedTile32768 666446080 666511616 13 3176 25815 29 _ _ (406349 / 20000) (507937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666511616 :
    ThetaLowerSegment 666511616 666577152 (8331064252789 / 12500) (66655172083447 / 100000) := by
  exact
    packedTile32768 666511616 666577152 13 3277 25816 29 _ _ (406351 / 20000) (1015879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666577152 :
    ThetaLowerSegment 666577152 666642688 (66655172083447 / 100000) (33330848040431 / 50000) := by
  exact
    packedTile32768 666577152 666642688 13 3211 25818 29 _ _ (406353 / 20000) (253971 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666642688 :
    ThetaLowerSegment 666642688 666708224 (33330848040431 / 50000) (16667074837403 / 25000) := by
  exact
    packedTile32768 666642688 666708224 13 3250 25819 29 _ _ (81271 / 4000) (1015889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666708224 :
    ThetaLowerSegment 666708224 666773760 (16667074837403 / 25000) (33337439134721 / 50000) := by
  exact
    packedTile32768 666708224 666773760 13 3238 25820 29 _ _ (406357 / 20000) (507947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666773760 :
    ThetaLowerSegment 666773760 666839296 (33337439134721 / 50000) (66681426744727 / 100000) := by
  exact
    packedTile32768 666773760 666839296 13 3223 25821 29 _ _ (406359 / 20000) (1015899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666839296 :
    ThetaLowerSegment 666839296 666904832 (66681426744727 / 100000) (13337588548031 / 20000) := by
  exact
    packedTile32768 666839296 666904832 13 3207 25823 29 _ _ (507951 / 25000) (2031807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666904832 :
    ThetaLowerSegment 666904832 666970368 (13337588548031 / 20000) (66694493308491 / 100000) := by
  exact
    packedTile32768 666904832 666970368 13 3224 25824 29 _ _ (1015907 / 50000) (2031817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell666970368 :
    ThetaLowerSegment 666970368 667035904 (66694493308491 / 100000) (13340219753663 / 20000) := by
  exact
    packedTile32768 666970368 667035904 13 3251 25825 29 _ _ (126989 / 6250) (2031827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667035904 :
    ThetaLowerSegment 667035904 667101440 (13340219753663 / 20000) (13341528254759 / 20000) := by
  exact
    packedTile32768 667035904 667101440 13 3220 25827 29 _ _ (1015917 / 50000) (2031837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667101440 :
    ThetaLowerSegment 667101440 667166976 (13341528254759 / 20000) (66714191938851 / 100000) := by
  exact
    packedTile32768 667101440 667166976 13 3224 25828 29 _ _ (507961 / 25000) (2031847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667166976 :
    ThetaLowerSegment 667166976 667232512 (66714191938851 / 100000) (66720752795417 / 100000) := by
  exact
    packedTile32768 667166976 667232512 13 3229 25829 29 _ _ (1015927 / 50000) (2031857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667232512 :
    ThetaLowerSegment 667232512 667298048 (66720752795417 / 100000) (13345465580817 / 20000) := by
  exact
    packedTile32768 667232512 667298048 13 3236 25830 29 _ _ (2031863 / 100000) (1015933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667298048 :
    ThetaLowerSegment 667298048 667363584 (13345465580817 / 20000) (16683452902707 / 25000) := by
  exact
    packedTile32768 667298048 667363584 13 3191 25832 29 _ _ (2031873 / 100000) (507969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667363584 :
    ThetaLowerSegment 667363584 667429120 (16683452902707 / 25000) (3337022183847 / 5000) := by
  exact
    packedTile32768 667363584 667429120 13 3264 25833 29 _ _ (2031883 / 100000) (1015943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667429120 :
    ThetaLowerSegment 667429120 667494656 (3337022183847 / 5000) (2085844340084 / 3125) := by
  exact
    packedTile32768 667429120 667494656 13 3236 25834 29 _ _ (2031893 / 100000) (253987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667494656 :
    ThetaLowerSegment 667494656 667560192 (2085844340084 / 3125) (417210318838 / 625) := by
  exact
    packedTile32768 667494656 667560192 13 3264 25835 29 _ _ (2031903 / 100000) (1015953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667560192 :
    ThetaLowerSegment 667560192 667625728 (417210318838 / 625) (66760220188809 / 100000) := by
  exact
    packedTile32768 667560192 667625728 13 3233 25837 29 _ _ (2031913 / 100000) (507979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667625728 :
    ThetaLowerSegment 667625728 667691264 (66760220188809 / 100000) (66766704051911 / 100000) := by
  exact
    packedTile32768 667625728 667691264 13 3191 25838 29 _ _ (1015961 / 50000) (81277 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667691264 :
    ThetaLowerSegment 667691264 667756800 (66766704051911 / 100000) (66773173723399 / 100000) := by
  exact
    packedTile32768 667691264 667756800 13 3184 25839 29 _ _ (507983 / 25000) (406387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667756800 :
    ThetaLowerSegment 667756800 667822336 (66773173723399 / 100000) (66779677969741 / 100000) := by
  exact
    packedTile32768 667756800 667822336 13 3201 25840 29 _ _ (1015971 / 50000) (406389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667822336 :
    ThetaLowerSegment 667822336 667887872 (66779677969741 / 100000) (66786107065869 / 100000) := by
  exact
    packedTile32768 667822336 667887872 13 3164 25842 29 _ _ (126997 / 6250) (406391 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667887872 :
    ThetaLowerSegment 667887872 667953408 (66786107065869 / 100000) (13358508864297 / 20000) := by
  exact
    packedTile32768 667887872 667953408 13 3168 25843 29 _ _ (1015981 / 50000) (406393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell667953408 :
    ThetaLowerSegment 667953408 668018944 (13358508864297 / 20000) (66799144163293 / 100000) := by
  exact
    packedTile32768 667953408 668018944 13 3248 25844 29 _ _ (2031971 / 100000) (1015987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668018944 :
    ThetaLowerSegment 668018944 668084480 (66799144163293 / 100000) (13361146369139 / 20000) := by
  exact
    packedTile32768 668018944 668084480 13 3242 25846 29 _ _ (2031981 / 100000) (126999 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668084480 :
    ThetaLowerSegment 668084480 668150016 (13361146369139 / 20000) (66812266728751 / 100000) := by
  exact
    packedTile32768 668084480 668150016 13 3216 25847 29 _ _ (2031991 / 100000) (1015997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668150016 :
    ThetaLowerSegment 668150016 668215552 (66812266728751 / 100000) (33409416061991 / 50000) := by
  exact
    packedTile32768 668150016 668215552 13 3231 25848 29 _ _ (2032001 / 100000) (508001 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668215552 :
    ThetaLowerSegment 668215552 668281088 (33409416061991 / 50000) (33412744496009 / 50000) := by
  exact
    packedTile32768 668215552 668281088 13 3276 25849 29 _ _ (2032011 / 100000) (1016007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668281088 :
    ThetaLowerSegment 668281088 668346624 (33412744496009 / 50000) (33416004872099 / 50000) := by
  exact
    packedTile32768 668281088 668346624 13 3209 25851 29 _ _ (101601 / 5000) (2032023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668346624 :
    ThetaLowerSegment 668346624 668412160 (33416004872099 / 50000) (8354825968201 / 12500) := by
  exact
    packedTile32768 668346624 668412160 13 3247 25852 29 _ _ (203203 / 10000) (2032033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668412160 :
    ThetaLowerSegment 668412160 668477696 (8354825968201 / 12500) (8355658088581 / 12500) := by
  exact
    packedTile32768 668412160 668477696 13 3276 25853 29 _ _ (50801 / 2500) (2032043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668477696 :
    ThetaLowerSegment 668477696 668543232 (8355658088581 / 12500) (33425890746499 / 50000) := by
  exact
    packedTile32768 668477696 668543232 13 3207 25854 29 _ _ (40641 / 2000) (2032053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668543232 :
    ThetaLowerSegment 668543232 668608768 (33425890746499 / 50000) (33429145090589 / 50000) := by
  exact
    packedTile32768 668543232 668608768 13 3203 25856 29 _ _ (101603 / 5000) (2032063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668608768 :
    ThetaLowerSegment 668608768 668674304 (33429145090589 / 50000) (8358104688437 / 12500) := by
  exact
    packedTile32768 668608768 668674304 13 3222 25857 29 _ _ (2032069 / 100000) (254009 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668674304 :
    ThetaLowerSegment 668674304 668739840 (8358104688437 / 12500) (33435651791437 / 50000) := by
  exact
    packedTile32768 668674304 668739840 13 3182 25858 29 _ _ (2032079 / 100000) (1016041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668739840 :
    ThetaLowerSegment 668739840 668805376 (33435651791437 / 50000) (33438943775617 / 50000) := by
  exact
    packedTile32768 668739840 668805376 13 3240 25860 29 _ _ (2032089 / 100000) (508023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668805376 :
    ThetaLowerSegment 668805376 668870912 (33438943775617 / 50000) (66884355722351 / 100000) := by
  exact
    packedTile32768 668805376 668870912 13 3183 25861 29 _ _ (2032099 / 100000) (1016051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668870912 :
    ThetaLowerSegment 668870912 668936448 (66884355722351 / 100000) (13378174132761 / 20000) := by
  exact
    packedTile32768 668870912 668936448 13 3206 25862 29 _ _ (2032109 / 100000) (127007 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell668936448 :
    ThetaLowerSegment 668936448 669001984 (13378174132761 / 20000) (13379484848871 / 20000) := by
  exact
    packedTile32768 668936448 669001984 13 3225 25863 29 _ _ (1016059 / 50000) (2032121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669001984 :
    ThetaLowerSegment 669001984 669067520 (13379484848871 / 20000) (66904046949507 / 100000) := by
  exact
    packedTile32768 669001984 669067520 13 3259 25865 29 _ _ (63504 / 3125) (2032131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669067520 :
    ThetaLowerSegment 669067520 669133056 (66904046949507 / 100000) (66910578241039 / 100000) := by
  exact
    packedTile32768 669067520 669133056 13 3214 25866 29 _ _ (1016069 / 50000) (2032141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669133056 :
    ThetaLowerSegment 669133056 669198592 (66910578241039 / 100000) (66917062825307 / 100000) := by
  exact
    packedTile32768 669133056 669198592 13 3191 25867 29 _ _ (508037 / 25000) (2032151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669198592 :
    ThetaLowerSegment 669198592 669264128 (66917062825307 / 100000) (66923636856437 / 100000) := by
  exact
    packedTile32768 669198592 669264128 13 3235 25868 29 _ _ (1016079 / 50000) (2032161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669264128 :
    ThetaLowerSegment 669264128 669329664 (66923636856437 / 100000) (33465133908679 / 50000) := by
  exact
    packedTile32768 669264128 669329664 13 3263 25870 29 _ _ (2032167 / 100000) (203217 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669329664 :
    ThetaLowerSegment 669329664 669395200 (33465133908679 / 50000) (418354639583 / 625) := by
  exact
    packedTile32768 669329664 669395200 13 3186 25871 29 _ _ (2032177 / 100000) (101609 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669395200 :
    ThetaLowerSegment 669395200 669460736 (418354639583 / 625) (4183954865417 / 6250) := by
  exact
    packedTile32768 669395200 669460736 13 3216 25872 29 _ _ (2032187 / 100000) (203219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669460736 :
    ThetaLowerSegment 669460736 669526272 (4183954865417 / 6250) (33474916857097 / 50000) := by
  exact
    packedTile32768 669460736 669526272 13 3226 25873 29 _ _ (2032197 / 100000) (10161 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669526272 :
    ThetaLowerSegment 669526272 669591808 (33474916857097 / 50000) (66956351002043 / 100000) := by
  exact
    packedTile32768 669526272 669591808 13 3207 25875 29 _ _ (2032207 / 100000) (203221 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669591808 :
    ThetaLowerSegment 669591808 669657344 (66956351002043 / 100000) (66962943510747 / 100000) := by
  exact
    packedTile32768 669591808 669657344 13 3244 25876 29 _ _ (254027 / 12500) (2032219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669657344 :
    ThetaLowerSegment 669657344 669722880 (66962943510747 / 100000) (66969471020659 / 100000) := by
  exact
    packedTile32768 669657344 669722880 13 3212 25877 29 _ _ (1016113 / 50000) (2032229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669722880 :
    ThetaLowerSegment 669722880 669788416 (66969471020659 / 100000) (66975990433747 / 100000) := by
  exact
    packedTile32768 669722880 669788416 13 3208 25879 29 _ _ (508059 / 25000) (2032239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669788416 :
    ThetaLowerSegment 669788416 669853952 (66975990433747 / 100000) (66982554588327 / 100000) := by
  exact
    packedTile32768 669788416 669853952 13 3230 25880 29 _ _ (1016123 / 50000) (2032249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669853952 :
    ThetaLowerSegment 669853952 669919488 (66982554588327 / 100000) (66989098452647 / 100000) := by
  exact
    packedTile32768 669853952 669919488 13 3220 25881 29 _ _ (63508 / 3125) (2032259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669919488 :
    ThetaLowerSegment 669919488 669985024 (66989098452647 / 100000) (66995646410477 / 100000) := by
  exact
    packedTile32768 669919488 669985024 13 3222 25882 29 _ _ (406453 / 20000) (508067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell669985024 :
    ThetaLowerSegment 669985024 670050560 (66995646410477 / 100000) (67002202529627 / 100000) := by
  exact
    packedTile32768 669985024 670050560 13 3226 25884 29 _ _ (81291 / 4000) (1016139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670050560 :
    ThetaLowerSegment 670050560 670116096 (67002202529627 / 100000) (67008815585017 / 100000) := by
  exact
    packedTile32768 670050560 670116096 13 3254 25885 29 _ _ (406457 / 20000) (63509 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670116096 :
    ThetaLowerSegment 670116096 670181632 (67008815585017 / 100000) (16753872918523 / 25000) := by
  exact
    packedTile32768 670116096 670181632 13 3285 25886 29 _ _ (406459 / 20000) (1016149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670181632 :
    ThetaLowerSegment 670181632 670247168 (16753872918523 / 25000) (16755534327043 / 25000) := by
  exact
    packedTile32768 670181632 670247168 13 3270 25887 29 _ _ (127019 / 6250) (2032307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670247168 :
    ThetaLowerSegment 670247168 670312704 (16755534327043 / 25000) (33514331534213 / 50000) := by
  exact
    packedTile32768 670247168 670312704 13 3211 25889 29 _ _ (1016157 / 50000) (2032317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670312704 :
    ThetaLowerSegment 670312704 670378240 (33514331534213 / 50000) (6703522950727 / 10000) := by
  exact
    packedTile32768 670312704 670378240 13 3231 25890 29 _ _ (508081 / 25000) (2032327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670378240 :
    ThetaLowerSegment 670378240 670443776 (6703522950727 / 10000) (4190110724401 / 6250) := by
  exact
    packedTile32768 670378240 670443776 13 3219 25891 29 _ _ (1016167 / 50000) (2032337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670443776 :
    ThetaLowerSegment 670443776 670509312 (4190110724401 / 6250) (2095255929149 / 3125) := by
  exact
    packedTile32768 670443776 670509312 13 3158 25892 29 _ _ (254043 / 12500) (2032347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670509312 :
    ThetaLowerSegment 670509312 670574848 (2095255929149 / 3125) (67054857882961 / 100000) := by
  exact
    packedTile32768 670509312 670574848 13 3281 25894 29 _ _ (2032353 / 100000) (508089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670574848 :
    ThetaLowerSegment 670574848 670640384 (67054857882961 / 100000) (33530675641373 / 50000) := by
  exact
    packedTile32768 670574848 670640384 13 3195 25895 29 _ _ (2032363 / 100000) (1016183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670640384 :
    ThetaLowerSegment 670640384 670705920 (33530675641373 / 50000) (16766980994257 / 25000) := by
  exact
    packedTile32768 670640384 670705920 13 3234 25896 29 _ _ (2032373 / 100000) (254047 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670705920 :
    ThetaLowerSegment 670705920 670771456 (16766980994257 / 25000) (67074519059863 / 100000) := by
  exact
    packedTile32768 670705920 670771456 13 3245 25897 29 _ _ (2032383 / 100000) (1016193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670771456 :
    ThetaLowerSegment 670771456 670836992 (67074519059863 / 100000) (13416206981723 / 20000) := by
  exact
    packedTile32768 670771456 670836992 13 3206 25899 29 _ _ (254049 / 12500) (406479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670836992 :
    ThetaLowerSegment 670836992 670902528 (13416206981723 / 20000) (67087644279919 / 100000) := by
  exact
    packedTile32768 670836992 670902528 13 3252 25900 29 _ _ (1016201 / 50000) (406481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670902528 :
    ThetaLowerSegment 670902528 670968064 (67087644279919 / 100000) (67094190678971 / 100000) := by
  exact
    packedTile32768 670902528 670968064 13 3221 25901 29 _ _ (508103 / 25000) (406483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell670968064 :
    ThetaLowerSegment 670968064 671033600 (67094190678971 / 100000) (67100836698911 / 100000) := by
  exact
    packedTile32768 670968064 671033600 13 3270 25903 29 _ _ (1016211 / 50000) (81297 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671033600 :
    ThetaLowerSegment 671033600 671099136 (67100836698911 / 100000) (67107352672697 / 100000) := by
  exact
    packedTile32768 671033600 671099136 13 3206 25904 29 _ _ (2032431 / 100000) (1016217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671099136 :
    ThetaLowerSegment 671099136 671164672 (67107352672697 / 100000) (33556953647461 / 50000) := by
  exact
    packedTile32768 671099136 671164672 13 3225 25905 29 _ _ (2032441 / 100000) (508111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671164672 :
    ThetaLowerSegment 671164672 671230208 (33556953647461 / 50000) (2684820754321 / 4000) := by
  exact
    packedTile32768 671164672 671230208 13 3253 25906 29 _ _ (2032451 / 100000) (1016227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671230208 :
    ThetaLowerSegment 671230208 671295744 (2684820754321 / 4000) (16781738915503 / 25000) := by
  exact
    packedTile32768 671230208 671295744 13 3167 25908 29 _ _ (2032461 / 100000) (127029 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671295744 :
    ThetaLowerSegment 671295744 671361280 (16781738915503 / 25000) (33566800921091 / 50000) := by
  exact
    packedTile32768 671295744 671361280 13 3270 25909 29 _ _ (2032471 / 100000) (1016237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671361280 :
    ThetaLowerSegment 671361280 671426816 (33566800921091 / 50000) (33570019353171 / 50000) := by
  exact
    packedTile32768 671361280 671426816 13 3167 25910 29 _ _ (12703 / 625) (2032483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671426816 :
    ThetaLowerSegment 671426816 671492352 (33570019353171 / 50000) (33573257109741 / 50000) := by
  exact
    packedTile32768 671426816 671492352 13 3186 25911 29 _ _ (203249 / 10000) (2032493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671492352 :
    ThetaLowerSegment 671492352 671557888 (33573257109741 / 50000) (33576520288491 / 50000) := by
  exact
    packedTile32768 671492352 671557888 13 3211 25913 29 _ _ (813 / 40) (2032503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671557888 :
    ThetaLowerSegment 671557888 671623424 (33576520288491 / 50000) (33579758076921 / 50000) := by
  exact
    packedTile32768 671557888 671623424 13 3186 25914 29 _ _ (203251 / 10000) (2032513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671623424 :
    ThetaLowerSegment 671623424 671688960 (33579758076921 / 50000) (67166030377237 / 100000) := by
  exact
    packedTile32768 671623424 671688960 13 3205 25915 29 _ _ (2032519 / 100000) (1016261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671688960 :
    ThetaLowerSegment 671688960 671754496 (67166030377237 / 100000) (67172627966371 / 100000) := by
  exact
    packedTile32768 671688960 671754496 13 3246 25916 29 _ _ (2032529 / 100000) (508133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671754496 :
    ThetaLowerSegment 671754496 671820032 (67172627966371 / 100000) (8397391257329 / 12500) := by
  exact
    packedTile32768 671754496 671820032 13 3199 25918 29 _ _ (2032539 / 100000) (1016271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671820032 :
    ThetaLowerSegment 671820032 671885568 (8397391257329 / 12500) (16796418716603 / 25000) := by
  exact
    packedTile32768 671820032 671885568 13 3220 25919 29 _ _ (2032549 / 100000) (254069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671885568 :
    ThetaLowerSegment 671885568 671951104 (16796418716603 / 25000) (16798058990909 / 25000) := by
  exact
    packedTile32768 671885568 671951104 13 3228 25920 29 _ _ (1016279 / 50000) (2032561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell671951104 :
    ThetaLowerSegment 671951104 672016640 (16798058990909 / 25000) (16799719090823 / 25000) := by
  exact
    packedTile32768 671951104 672016640 13 3267 25922 29 _ _ (254071 / 12500) (2032571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672016640 :
    ThetaLowerSegment 672016640 672082176 (16799719090823 / 25000) (33602695387891 / 50000) := by
  exact
    packedTile32768 672016640 672082176 13 3205 25923 29 _ _ (1016289 / 50000) (2032581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672082176 :
    ThetaLowerSegment 672082176 672147712 (33602695387891 / 50000) (33605981066393 / 50000) := by
  exact
    packedTile32768 672082176 672147712 13 3233 25924 29 _ _ (508147 / 25000) (2032591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672147712 :
    ThetaLowerSegment 672147712 672213248 (33605981066393 / 50000) (33609208830429 / 50000) := by
  exact
    packedTile32768 672147712 672213248 13 3176 25925 29 _ _ (2032597 / 100000) (10163 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672213248 :
    ThetaLowerSegment 672213248 672278784 (33609208830429 / 50000) (33612432545131 / 50000) := by
  exact
    packedTile32768 672213248 672278784 13 3172 25927 29 _ _ (2032607 / 100000) (203261 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672278784 :
    ThetaLowerSegment 672278784 672344320 (33612432545131 / 50000) (33615705058501 / 50000) := by
  exact
    packedTile32768 672278784 672344320 13 3220 25928 29 _ _ (2032617 / 100000) (101631 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672344320 :
    ThetaLowerSegment 672344320 672409856 (33615705058501 / 50000) (67237936882299 / 100000) := by
  exact
    packedTile32768 672344320 672409856 13 3211 25929 29 _ _ (2032627 / 100000) (203263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672409856 :
    ThetaLowerSegment 672409856 672475392 (67237936882299 / 100000) (67244508394487 / 100000) := by
  exact
    packedTile32768 672409856 672475392 13 3233 25930 29 _ _ (508159 / 25000) (2032639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672475392 :
    ThetaLowerSegment 672475392 672540928 (67244508394487 / 100000) (67251214093641 / 100000) := by
  exact
    packedTile32768 672475392 672540928 13 3299 25932 29 _ _ (1016323 / 50000) (2032649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672540928 :
    ThetaLowerSegment 672540928 672606464 (67251214093641 / 100000) (67257771441897 / 100000) := by
  exact
    packedTile32768 672540928 672606464 13 3226 25933 29 _ _ (127041 / 6250) (2032659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672606464 :
    ThetaLowerSegment 672606464 672672000 (67257771441897 / 100000) (67264436553711 / 100000) := by
  exact
    packedTile32768 672606464 672672000 13 3279 25934 29 _ _ (1016333 / 50000) (2032669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672672000 :
    ThetaLowerSegment 672672000 672737536 (67264436553711 / 100000) (67270945179061 / 100000) := by
  exact
    packedTile32768 672672000 672737536 13 3202 25935 29 _ _ (81307 / 4000) (1016339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672737536 :
    ThetaLowerSegment 672737536 672803072 (67270945179061 / 100000) (33638831601493 / 50000) := by
  exact
    packedTile32768 672737536 672803072 13 3305 25937 29 _ _ (406537 / 20000) (127043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672803072 :
    ThetaLowerSegment 672803072 672868608 (33638831601493 / 50000) (2102629863463 / 3125) := by
  exact
    packedTile32768 672803072 672868608 13 3194 25938 29 _ _ (406539 / 20000) (1016349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672868608 :
    ThetaLowerSegment 672868608 672934144 (2102629863463 / 3125) (33645368764803 / 50000) := by
  exact
    packedTile32768 672868608 672934144 13 3238 25939 29 _ _ (406541 / 20000) (508177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672934144 :
    ThetaLowerSegment 672934144 672999680 (33645368764803 / 50000) (8412172808959 / 12500) := by
  exact
    packedTile32768 672934144 672999680 13 3269 25940 29 _ _ (1016357 / 50000) (2032717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell672999680 :
    ThetaLowerSegment 672999680 673065216 (8412172808959 / 12500) (134607965453 / 200) := by
  exact
    packedTile32768 672999680 673065216 13 3247 25942 29 _ _ (508181 / 25000) (2032727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673065216 :
    ThetaLowerSegment 673065216 673130752 (134607965453 / 200) (33655256950421 / 50000) := by
  exact
    packedTile32768 673065216 673130752 13 3213 25943 29 _ _ (1016367 / 50000) (2032737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673130752 :
    ThetaLowerSegment 673130752 673196288 (33655256950421 / 50000) (33658534750121 / 50000) := by
  exact
    packedTile32768 673130752 673196288 13 3225 25944 29 _ _ (254093 / 12500) (2032747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673196288 :
    ThetaLowerSegment 673196288 673261824 (33658534750121 / 50000) (67323641390691 / 100000) := by
  exact
    packedTile32768 673196288 673261824 13 3233 25946 29 _ _ (2032753 / 100000) (508189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673261824 :
    ThetaLowerSegment 673261824 673327360 (67323641390691 / 100000) (6733021331347 / 10000) := by
  exact
    packedTile32768 673261824 673327360 13 3233 25947 29 _ _ (2032763 / 100000) (1016383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673327360 :
    ThetaLowerSegment 673327360 673392896 (6733021331347 / 10000) (13467361932371 / 20000) := by
  exact
    packedTile32768 673327360 673392896 13 3245 25948 29 _ _ (2032773 / 100000) (254097 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673392896 :
    ThetaLowerSegment 673392896 673458432 (13467361932371 / 20000) (67343300334781 / 100000) := by
  exact
    packedTile32768 673392896 673458432 13 3193 25949 29 _ _ (1016391 / 50000) (406557 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673458432 :
    ThetaLowerSegment 673458432 673523968 (67343300334781 / 100000) (67349821531517 / 100000) := by
  exact
    packedTile32768 673458432 673523968 13 3208 25951 29 _ _ (254099 / 12500) (406559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673523968 :
    ThetaLowerSegment 673523968 673589504 (67349821531517 / 100000) (67356352924343 / 100000) := by
  exact
    packedTile32768 673523968 673589504 13 3213 25952 29 _ _ (1016401 / 50000) (406561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673589504 :
    ThetaLowerSegment 673589504 673655040 (67356352924343 / 100000) (67362888414923 / 100000) := by
  exact
    packedTile32768 673589504 673655040 13 3215 25953 29 _ _ (508203 / 25000) (406563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673655040 :
    ThetaLowerSegment 673655040 673720576 (67362888414923 / 100000) (2105295641413 / 3125) := by
  exact
    packedTile32768 673655040 673720576 13 3233 25954 29 _ _ (2032821 / 100000) (254103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673720576 :
    ThetaLowerSegment 673720576 673786112 (2105295641413 / 3125) (4211003947519 / 6250) := by
  exact
    packedTile32768 673720576 673786112 13 3248 25956 29 _ _ (2032831 / 100000) (1016417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673786112 :
    ThetaLowerSegment 673786112 673851648 (4211003947519 / 6250) (67382505233433 / 100000) := by
  exact
    packedTile32768 673786112 673851648 13 3169 25957 29 _ _ (2032841 / 100000) (508211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673851648 :
    ThetaLowerSegment 673851648 673917184 (67382505233433 / 100000) (33694516358997 / 50000) := by
  exact
    packedTile32768 673851648 673917184 13 3211 25958 29 _ _ (2032851 / 100000) (1016427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673917184 :
    ThetaLowerSegment 673917184 673982720 (33694516358997 / 50000) (33697786214307 / 50000) := by
  exact
    packedTile32768 673917184 673982720 13 3217 25959 29 _ _ (101643 / 5000) (2032863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell673982720 :
    ThetaLowerSegment 673982720 674048256 (33697786214307 / 50000) (33701063200747 / 50000) := by
  exact
    packedTile32768 673982720 674048256 13 3224 25961 29 _ _ (203287 / 10000) (2032873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674048256 :
    ThetaLowerSegment 674048256 674113792 (33701063200747 / 50000) (33704332071787 / 50000) := by
  exact
    packedTile32768 674048256 674113792 13 3216 25962 29 _ _ (25411 / 1250) (2032883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674113792 :
    ThetaLowerSegment 674113792 674179328 (33704332071787 / 50000) (67415236473711 / 100000) := by
  exact
    packedTile32768 674113792 674179328 13 3233 25963 29 _ _ (2032889 / 100000) (508223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674179328 :
    ThetaLowerSegment 674179328 674244864 (67415236473711 / 100000) (67421644171359 / 100000) := by
  exact
    packedTile32768 674179328 674244864 13 3152 25964 29 _ _ (2032899 / 100000) (1016451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674244864 :
    ThetaLowerSegment 674244864 674310400 (67421644171359 / 100000) (33714102184351 / 50000) := by
  exact
    packedTile32768 674244864 674310400 13 3227 25966 29 _ _ (2032909 / 100000) (127057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674310400 :
    ThetaLowerSegment 674310400 674375936 (33714102184351 / 50000) (4214669102729 / 6250) := by
  exact
    packedTile32768 674310400 674375936 13 3198 25967 29 _ _ (2032919 / 100000) (1016461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674375936 :
    ThetaLowerSegment 674375936 674441472 (4214669102729 / 6250) (4215074798923 / 6250) := by
  exact
    packedTile32768 674375936 674441472 13 3193 25968 29 _ _ (63529 / 3125) (2032931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674441472 :
    ThetaLowerSegment 674441472 674507008 (4215074798923 / 6250) (8430980053019 / 12500) := by
  exact
    packedTile32768 674441472 674507008 13 3268 25970 29 _ _ (1016469 / 50000) (2032941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674507008 :
    ThetaLowerSegment 674507008 674572544 (8430980053019 / 12500) (421590500202 / 625) := by
  exact
    packedTile32768 674507008 674572544 13 3266 25971 29 _ _ (508237 / 25000) (2032951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674572544 :
    ThetaLowerSegment 674572544 674638080 (421590500202 / 625) (67461068845957 / 100000) := by
  exact
    packedTile32768 674572544 674638080 13 3241 25972 29 _ _ (2032957 / 100000) (12706 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674638080 :
    ThetaLowerSegment 674638080 674703616 (67461068845957 / 100000) (33733778021827 / 50000) := by
  exact
    packedTile32768 674638080 674703616 13 3191 25973 29 _ _ (2032967 / 100000) (203297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674703616 :
    ThetaLowerSegment 674703616 674769152 (33733778021827 / 50000) (67474083932801 / 100000) := by
  exact
    packedTile32768 674703616 674769152 13 3211 25975 29 _ _ (2032977 / 100000) (101649 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674769152 :
    ThetaLowerSegment 674769152 674834688 (67474083932801 / 100000) (13496134975331 / 20000) := by
  exact
    packedTile32768 674769152 674834688 13 3242 25976 29 _ _ (2032987 / 100000) (203299 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674834688 :
    ThetaLowerSegment 674834688 674900224 (13496134975331 / 20000) (67487247552723 / 100000) := by
  exact
    packedTile32768 674834688 674900224 13 3233 25977 29 _ _ (508249 / 25000) (2032999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674900224 :
    ThetaLowerSegment 674900224 674965760 (67487247552723 / 100000) (67493791799037 / 100000) := by
  exact
    packedTile32768 674900224 674965760 13 3219 25978 29 _ _ (1016503 / 50000) (2033009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell674965760 :
    ThetaLowerSegment 674965760 675031296 (67493791799037 / 100000) (67500332011509 / 100000) := by
  exact
    packedTile32768 674965760 675031296 13 3217 25980 29 _ _ (254127 / 12500) (2033019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675031296 :
    ThetaLowerSegment 675031296 675096832 (67500332011509 / 100000) (67506898682259 / 100000) := by
  exact
    packedTile32768 675031296 675096832 13 3230 25981 29 _ _ (81321 / 4000) (508257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675096832 :
    ThetaLowerSegment 675096832 675162368 (67506898682259 / 100000) (67513314940719 / 100000) := by
  exact
    packedTile32768 675096832 675162368 13 3156 25982 29 _ _ (406607 / 20000) (1016519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675162368 :
    ThetaLowerSegment 675162368 675227904 (67513314940719 / 100000) (33759945920647 / 50000) := by
  exact
    packedTile32768 675162368 675227904 13 3235 25983 29 _ _ (406609 / 20000) (254131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675227904 :
    ThetaLowerSegment 675227904 675293440 (33759945920647 / 50000) (16881604486961 / 25000) := by
  exact
    packedTile32768 675227904 675293440 13 3210 25985 29 _ _ (406611 / 20000) (1016529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675293440 :
    ThetaLowerSegment 675293440 675358976 (16881604486961 / 25000) (16883246694407 / 25000) := by
  exact
    packedTile32768 675293440 675358976 13 3231 25986 29 _ _ (254133 / 12500) (2033067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675358976 :
    ThetaLowerSegment 675358976 675424512 (16883246694407 / 25000) (6753943772143 / 10000) := by
  exact
    packedTile32768 675358976 675424512 13 3173 25987 29 _ _ (1016537 / 50000) (2033077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675424512 :
    ThetaLowerSegment 675424512 675490048 (6753943772143 / 10000) (33772974844741 / 50000) := by
  exact
    packedTile32768 675424512 675490048 13 3203 25988 29 _ _ (508271 / 25000) (2033087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675490048 :
    ThetaLowerSegment 675490048 675555584 (33772974844741 / 50000) (67552616201429 / 100000) := by
  exact
    packedTile32768 675490048 675555584 13 3279 25990 29 _ _ (2033093 / 100000) (254137 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675555584 :
    ThetaLowerSegment 675555584 675621120 (67552616201429 / 100000) (2702367487613 / 4000) := by
  exact
    packedTile32768 675555584 675621120 13 3232 25991 29 _ _ (2033103 / 100000) (1016553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675621120 :
    ThetaLowerSegment 675621120 675686656 (2702367487613 / 4000) (33782863857423 / 50000) := by
  exact
    packedTile32768 675621120 675686656 13 3217 25992 29 _ _ (2033113 / 100000) (508279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675686656 :
    ThetaLowerSegment 675686656 675752192 (33782863857423 / 50000) (33786106687013 / 50000) := by
  exact
    packedTile32768 675686656 675752192 13 3190 25993 29 _ _ (1016561 / 50000) (3253 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675752192 :
    ThetaLowerSegment 675752192 675817728 (33786106687013 / 50000) (1351573656001 / 2000) := by
  exact
    packedTile32768 675752192 675817728 13 3182 25995 29 _ _ (508283 / 25000) (406627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675817728 :
    ThetaLowerSegment 675817728 675883264 (1351573656001 / 2000) (6758524984871 / 10000) := by
  exact
    packedTile32768 675817728 675883264 13 3230 25996 29 _ _ (1016571 / 50000) (406629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675883264 :
    ThetaLowerSegment 675883264 675948800 (6758524984871 / 10000) (33795887116739 / 50000) := by
  exact
    packedTile32768 675883264 675948800 13 3209 25997 29 _ _ (63536 / 3125) (406631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell675948800 :
    ThetaLowerSegment 675948800 676014336 (33795887116739 / 50000) (67598408437821 / 100000) := by
  exact
    packedTile32768 675948800 676014336 13 3263 25999 29 _ _ (2033161 / 100000) (508291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676014336 :
    ThetaLowerSegment 676014336 676079872 (67598408437821 / 100000) (67604873921601 / 100000) := by
  exact
    packedTile32768 676014336 676079872 13 3180 26000 29 _ _ (2033171 / 100000) (1016587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676079872 :
    ThetaLowerSegment 676079872 676145408 (67604873921601 / 100000) (2112858360237 / 3125) := by
  exact
    packedTile32768 676079872 676145408 13 3243 26001 29 _ _ (2033181 / 100000) (63537 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676145408 :
    ThetaLowerSegment 676145408 676210944 (2112858360237 / 3125) (16904514782391 / 25000) := by
  exact
    packedTile32768 676145408 676210944 13 3242 26002 29 _ _ (203319 / 10000) (2033193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676210944 :
    ThetaLowerSegment 676210944 676276480 (16904514782391 / 25000) (16906144900491 / 25000) := by
  exact
    packedTile32768 676210944 676276480 13 3207 26004 29 _ _ (5083 / 250) (2033203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676276480 :
    ThetaLowerSegment 676276480 676342016 (16906144900491 / 25000) (4226940071459 / 6250) := by
  exact
    packedTile32768 676276480 676342016 13 3178 26005 29 _ _ (203321 / 10000) (2033213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676342016 :
    ThetaLowerSegment 676342016 676407552 (4226940071459 / 6250) (338187981207 / 500) := by
  exact
    packedTile32768 676342016 676407552 13 3224 26006 29 _ _ (2033219 / 100000) (1016611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676407552 :
    ThetaLowerSegment 676407552 676473088 (338187981207 / 500) (67644242867001 / 100000) := by
  exact
    packedTile32768 676407552 676473088 13 3269 26007 29 _ _ (2033229 / 100000) (127077 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676473088 :
    ThetaLowerSegment 676473088 676538624 (67644242867001 / 100000) (845634390813 / 1250) := by
  exact
    packedTile32768 676473088 676538624 13 3201 26009 29 _ _ (2033239 / 100000) (1016621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676538624 :
    ThetaLowerSegment 676538624 676604160 (845634390813 / 1250) (33828655263157 / 50000) := by
  exact
    packedTile32768 676538624 676604160 13 3226 26010 29 _ _ (2033249 / 100000) (508313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676604160 :
    ThetaLowerSegment 676604160 676669696 (33828655263157 / 50000) (33831902376183 / 50000) := by
  exact
    packedTile32768 676604160 676669696 13 3194 26011 29 _ _ (1016629 / 50000) (2033261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676669696 :
    ThetaLowerSegment 676669696 676735232 (33831902376183 / 50000) (33835167804591 / 50000) := by
  exact
    packedTile32768 676669696 676735232 13 3212 26012 29 _ _ (508317 / 25000) (2033271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676735232 :
    ThetaLowerSegment 676735232 676800768 (33835167804591 / 50000) (1691923644899 / 2500) := by
  exact
    packedTile32768 676735232 676800768 13 3251 26014 29 _ _ (1016639 / 50000) (2033281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676800768 :
    ThetaLowerSegment 676800768 676866304 (1691923644899 / 2500) (33841748523337 / 50000) := by
  exact
    packedTile32768 676800768 676866304 13 3222 26015 29 _ _ (2033287 / 100000) (203329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676866304 :
    ThetaLowerSegment 676866304 676931840 (33841748523337 / 50000) (67690025963341 / 100000) := by
  exact
    packedTile32768 676866304 676931840 13 3211 26016 29 _ _ (2033297 / 100000) (20333 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676931840 :
    ThetaLowerSegment 676931840 676997376 (67690025963341 / 100000) (67696504079443 / 100000) := by
  exact
    packedTile32768 676931840 676997376 13 3186 26017 29 _ _ (2033307 / 100000) (203331 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell676997376 :
    ThetaLowerSegment 676997376 677062912 (67696504079443 / 100000) (67703006624011 / 100000) := by
  exact
    packedTile32768 676997376 677062912 13 3198 26019 29 _ _ (508329 / 25000) (2033319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677062912 :
    ThetaLowerSegment 677062912 677128448 (67703006624011 / 100000) (67709586466947 / 100000) := by
  exact
    packedTile32768 677062912 677128448 13 3236 26020 29 _ _ (1016663 / 50000) (2033329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677128448 :
    ThetaLowerSegment 677128448 677193984 (67709586466947 / 100000) (67716131775531 / 100000) := by
  exact
    packedTile32768 677128448 677193984 13 3219 26021 29 _ _ (254167 / 12500) (2033339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677193984 :
    ThetaLowerSegment 677193984 677259520 (67716131775531 / 100000) (67722634412841 / 100000) := by
  exact
    packedTile32768 677193984 677259520 13 3198 26022 29 _ _ (406669 / 20000) (508337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677259520 :
    ThetaLowerSegment 677259520 677325056 (67722634412841 / 100000) (67729145215551 / 100000) := by
  exact
    packedTile32768 677259520 677325056 13 3202 26024 29 _ _ (406671 / 20000) (1016679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677325056 :
    ThetaLowerSegment 677325056 677390592 (67729145215551 / 100000) (33867849375473 / 50000) := by
  exact
    packedTile32768 677325056 677390592 13 3223 26025 29 _ _ (406673 / 20000) (254171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677390592 :
    ThetaLowerSegment 677390592 677456128 (33867849375473 / 50000) (16935563078837 / 25000) := by
  exact
    packedTile32768 677390592 677456128 13 3223 26026 29 _ _ (1016687 / 50000) (2033377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677456128 :
    ThetaLowerSegment 677456128 677521664 (16935563078837 / 25000) (16937179110771 / 25000) := by
  exact
    packedTile32768 677456128 677521664 13 3179 26027 29 _ _ (254173 / 12500) (2033387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677521664 :
    ThetaLowerSegment 677521664 677587200 (16937179110771 / 25000) (33877608601851 / 50000) := by
  exact
    packedTile32768 677521664 677587200 13 3197 26029 29 _ _ (1016697 / 50000) (2033397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677587200 :
    ThetaLowerSegment 677587200 677652736 (33877608601851 / 50000) (67761860331303 / 100000) := by
  exact
    packedTile32768 677587200 677652736 13 3267 26030 29 _ _ (2033403 / 100000) (1016703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677652736 :
    ThetaLowerSegment 677652736 677718272 (67761860331303 / 100000) (67768363186077 / 100000) := by
  exact
    packedTile32768 677652736 677718272 13 3198 26031 29 _ _ (2033413 / 100000) (254177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677718272 :
    ThetaLowerSegment 677718272 677783808 (67768363186077 / 100000) (67774939276059 / 100000) := by
  exact
    packedTile32768 677718272 677783808 13 3234 26033 29 _ _ (2033423 / 100000) (1016713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677783808 :
    ThetaLowerSegment 677783808 677849344 (67774939276059 / 100000) (67781629267339 / 100000) := by
  exact
    packedTile32768 677783808 677849344 13 3290 26034 29 _ _ (254179 / 12500) (406687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677849344 :
    ThetaLowerSegment 677849344 677914880 (67781629267339 / 100000) (67788117980761 / 100000) := by
  exact
    packedTile32768 677849344 677914880 13 3191 26035 29 _ _ (1016721 / 50000) (406689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677914880 :
    ThetaLowerSegment 677914880 677980416 (67788117980761 / 100000) (67794635194421 / 100000) := by
  exact
    packedTile32768 677914880 677980416 13 3205 26036 29 _ _ (508363 / 25000) (406691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell677980416 :
    ThetaLowerSegment 677980416 678045952 (67794635194421 / 100000) (67801199206529 / 100000) := by
  exact
    packedTile32768 677980416 678045952 13 3228 26038 29 _ _ (2033461 / 100000) (254183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678045952 :
    ThetaLowerSegment 678045952 678111488 (67801199206529 / 100000) (16951961655807 / 25000) := by
  exact
    packedTile32768 678045952 678111488 13 3269 26039 29 _ _ (2033471 / 100000) (1016737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678111488 :
    ThetaLowerSegment 678111488 678177024 (16951961655807 / 25000) (6781443916863 / 10000) := by
  exact
    packedTile32768 678111488 678177024 13 3242 26040 29 _ _ (2033481 / 100000) (508371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678177024 :
    ThetaLowerSegment 678177024 678242560 (6781443916863 / 10000) (339105473907 / 500) := by
  exact
    packedTile32768 678177024 678242560 13 3273 26041 29 _ _ (203349 / 10000) (2033493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678242560 :
    ThetaLowerSegment 678242560 678308096 (339105473907 / 500) (339137887897 / 500) := by
  exact
    packedTile32768 678242560 678308096 13 3188 26043 29 _ _ (4067 / 200) (2033503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678308096 :
    ThetaLowerSegment 678308096 678373632 (339137887897 / 500) (847925958467 / 1250) := by
  exact
    packedTile32768 678308096 678373632 13 3196 26044 29 _ _ (203351 / 10000) (2033513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678373632 :
    ThetaLowerSegment 678373632 678439168 (847925958467 / 1250) (4240044630211 / 6250) := by
  exact
    packedTile32768 678373632 678439168 13 3264 26045 29 _ _ (2033519 / 100000) (1016761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678439168 :
    ThetaLowerSegment 678439168 678504704 (4240044630211 / 6250) (33923588319269 / 50000) := by
  exact
    packedTile32768 678439168 678504704 13 3178 26046 29 _ _ (2033529 / 100000) (508383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678504704 :
    ThetaLowerSegment 678504704 678570240 (33923588319269 / 50000) (3392688061891 / 5000) := by
  exact
    packedTile32768 678504704 678570240 13 3238 26048 29 _ _ (2033539 / 100000) (1016771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678570240 :
    ThetaLowerSegment 678570240 678635776 (3392688061891 / 5000) (4241275810833 / 6250) := by
  exact
    packedTile32768 678570240 678635776 13 3271 26049 29 _ _ (508387 / 25000) (2033551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678635776 :
    ThetaLowerSegment 678635776 678701312 (4241275810833 / 6250) (33933432726431 / 50000) := by
  exact
    packedTile32768 678635776 678701312 13 3173 26050 29 _ _ (1016779 / 50000) (2033561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678701312 :
    ThetaLowerSegment 678701312 678766848 (33933432726431 / 50000) (33936690502367 / 50000) := by
  exact
    packedTile32768 678701312 678766848 13 3204 26051 29 _ _ (63549 / 3125) (2033571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678766848 :
    ThetaLowerSegment 678766848 678832384 (33936690502367 / 50000) (33939968628491 / 50000) := by
  exact
    packedTile32768 678766848 678832384 13 3224 26053 29 _ _ (2033577 / 100000) (101679 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678832384 :
    ThetaLowerSegment 678832384 678897920 (33939968628491 / 50000) (8485823385809 / 12500) := by
  exact
    packedTile32768 678832384 678897920 13 3270 26054 29 _ _ (2033587 / 100000) (203359 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678897920 :
    ThetaLowerSegment 678897920 678963456 (8485823385809 / 12500) (67893088496081 / 100000) := by
  exact
    packedTile32768 678897920 678963456 13 3197 26055 29 _ _ (2033597 / 100000) (2542 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell678963456 :
    ThetaLowerSegment 678963456 679028992 (67893088496081 / 100000) (67899697715581 / 100000) := by
  exact
    packedTile32768 678963456 679028992 13 3250 26056 29 _ _ (1016803 / 50000) (2033609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679028992 :
    ThetaLowerSegment 679028992 679094528 (67899697715581 / 100000) (67906221555709 / 100000) := by
  exact
    packedTile32768 679028992 679094528 13 3208 26058 29 _ _ (127101 / 6250) (2033619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679094528 :
    ThetaLowerSegment 679094528 679160064 (67906221555709 / 100000) (67912836941087 / 100000) := by
  exact
    packedTile32768 679094528 679160064 13 3253 26059 29 _ _ (1016813 / 50000) (2033629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679160064 :
    ThetaLowerSegment 679160064 679225600 (67912836941087 / 100000) (33959718043331 / 50000) := by
  exact
    packedTile32768 679160064 679225600 13 3245 26060 29 _ _ (406727 / 20000) (1016819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679225600 :
    ThetaLowerSegment 679225600 679291136 (33959718043331 / 50000) (4245369704977 / 6250) := by
  exact
    packedTile32768 679225600 679291136 13 3186 26061 29 _ _ (406729 / 20000) (127103 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679291136 :
    ThetaLowerSegment 679291136 679356672 (4245369704977 / 6250) (67932595836307 / 100000) := by
  exact
    packedTile32768 679291136 679356672 13 3285 26063 29 _ _ (406731 / 20000) (1016829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679356672 :
    ThetaLowerSegment 679356672 679422208 (67932595836307 / 100000) (13587793054391 / 20000) := by
  exact
    packedTile32768 679356672 679422208 13 3132 26064 29 _ _ (63552 / 3125) (2033667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679422208 :
    ThetaLowerSegment 679422208 679487744 (13587793054391 / 20000) (13589143413927 / 20000) := by
  exact
    packedTile32768 679422208 679487744 13 3320 26065 29 _ _ (1016837 / 50000) (2033677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679487744 :
    ThetaLowerSegment 679487744 679553280 (13589143413927 / 20000) (67952180114209 / 100000) := by
  exact
    packedTile32768 679487744 679553280 13 3178 26066 29 _ _ (2033683 / 100000) (1016843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679553280 :
    ThetaLowerSegment 679553280 679618816 (67952180114209 / 100000) (339793307469 / 500) := by
  exact
    packedTile32768 679553280 679618816 13 3187 26068 29 _ _ (2033693 / 100000) (63553 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679618816 :
    ThetaLowerSegment 679618816 679684352 (339793307469 / 500) (424782816822 / 625) := by
  exact
    packedTile32768 679618816 679684352 13 3240 26069 29 _ _ (2033703 / 100000) (1016853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679684352 :
    ThetaLowerSegment 679684352 679749888 (424782816822 / 625) (4248242409933 / 6250) := by
  exact
    packedTile32768 679684352 679749888 13 3259 26070 29 _ _ (127107 / 6250) (406743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679749888 :
    ThetaLowerSegment 679749888 679815424 (4248242409933 / 6250) (33989267465517 / 50000) := by
  exact
    packedTile32768 679749888 679815424 13 3273 26072 29 _ _ (1016861 / 50000) (81349 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679815424 :
    ThetaLowerSegment 679815424 679880960 (33989267465517 / 50000) (33992521436717 / 50000) := by
  exact
    packedTile32768 679815424 679880960 13 3200 26073 29 _ _ (508433 / 25000) (406747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679880960 :
    ThetaLowerSegment 679880960 679946496 (33992521436717 / 50000) (4249473707313 / 6250) := by
  exact
    packedTile32768 679880960 679946496 13 3214 26074 29 _ _ (2033741 / 100000) (127109 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell679946496 :
    ThetaLowerSegment 679946496 680012032 (4249473707313 / 6250) (33999118908891 / 50000) := by
  exact
    packedTile32768 679946496 680012032 13 3274 26075 29 _ _ (2033751 / 100000) (1016877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680012032 :
    ThetaLowerSegment 680012032 680077568 (33999118908891 / 50000) (34002311913661 / 50000) := by
  exact
    packedTile32768 680012032 680077568 13 3140 26077 29 _ _ (2033761 / 100000) (508441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680077568 :
    ThetaLowerSegment 680077568 680143104 (34002311913661 / 50000) (34005557810581 / 50000) := by
  exact
    packedTile32768 680077568 680143104 13 3192 26078 29 _ _ (203377 / 10000) (2033773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680143104 :
    ThetaLowerSegment 680143104 680208640 (34005557810581 / 50000) (34008810841691 / 50000) := by
  exact
    packedTile32768 680143104 680208640 13 3199 26079 29 _ _ (101689 / 5000) (2033783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680208640 :
    ThetaLowerSegment 680208640 680274176 (34008810841691 / 50000) (34012109649071 / 50000) := by
  exact
    packedTile32768 680208640 680274176 13 3244 26080 29 _ _ (203379 / 10000) (2033793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680274176 :
    ThetaLowerSegment 680274176 680339712 (34012109649071 / 50000) (17007715421419 / 25000) := by
  exact
    packedTile32768 680274176 680339712 13 3266 26082 29 _ _ (2033799 / 100000) (1016901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680339712 :
    ThetaLowerSegment 680339712 680405248 (17007715421419 / 25000) (544299137971 / 800) := by
  exact
    packedTile32768 680339712 680405248 13 3211 26083 29 _ _ (2033809 / 100000) (508453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680405248 :
    ThetaLowerSegment 680405248 680470784 (544299137971 / 800) (2721762120013 / 4000) := by
  exact
    packedTile32768 680405248 680470784 13 3275 26084 29 _ _ (1016909 / 50000) (2033821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680470784 :
    ThetaLowerSegment 680470784 680536320 (2721762120013 / 4000) (68050483964461 / 100000) := by
  exact
    packedTile32768 680470784 680536320 13 3162 26085 29 _ _ (508457 / 25000) (2033831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680536320 :
    ThetaLowerSegment 680536320 680601856 (68050483964461 / 100000) (68056872249619 / 100000) := by
  exact
    packedTile32768 680536320 680601856 13 3141 26087 29 _ _ (1016919 / 50000) (2033841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680601856 :
    ThetaLowerSegment 680601856 680667392 (68056872249619 / 100000) (1361266512923 / 2000) := by
  exact
    packedTile32768 680601856 680667392 13 3173 26088 29 _ _ (2033847 / 100000) (40677 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680667392 :
    ThetaLowerSegment 680667392 680732928 (1361266512923 / 2000) (13613972899281 / 20000) := by
  exact
    packedTile32768 680667392 680732928 13 3215 26089 29 _ _ (2033857 / 100000) (101693 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680732928 :
    ThetaLowerSegment 680732928 680798464 (13613972899281 / 20000) (34038250502213 / 50000) := by
  exact
    packedTile32768 680732928 680798464 13 3263 26090 29 _ _ (2033867 / 100000) (203387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680798464 :
    ThetaLowerSegment 680798464 680864000 (34038250502213 / 50000) (6808298703499 / 10000) := by
  exact
    packedTile32768 680798464 680864000 13 3189 26092 29 _ _ (508469 / 25000) (2033879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680864000 :
    ThetaLowerSegment 680864000 680929536 (6808298703499 / 10000) (17022382511563 / 25000) := by
  exact
    packedTile32768 680864000 680929536 13 3217 26093 29 _ _ (1016943 / 50000) (2033889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680929536 :
    ThetaLowerSegment 680929536 680995072 (17022382511563 / 25000) (68095955120557 / 100000) := by
  exact
    packedTile32768 680929536 680995072 13 3159 26094 29 _ _ (406779 / 20000) (1016949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell680995072 :
    ThetaLowerSegment 680995072 681060608 (68095955120557 / 100000) (68102573447427 / 100000) := by
  exact
    packedTile32768 680995072 681060608 13 3254 26095 29 _ _ (406781 / 20000) (508477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681060608 :
    ThetaLowerSegment 681060608 681126144 (68102573447427 / 100000) (34054651836081 / 50000) := by
  exact
    packedTile32768 681060608 681126144 13 3309 26097 29 _ _ (406783 / 20000) (1016959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681126144 :
    ThetaLowerSegment 681126144 681191680 (34054651836081 / 50000) (34057937640303 / 50000) := by
  exact
    packedTile32768 681126144 681191680 13 3231 26098 29 _ _ (508481 / 25000) (2033927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681191680 :
    ThetaLowerSegment 681191680 681257216 (34057937640303 / 50000) (17030588340099 / 25000) := by
  exact
    packedTile32768 681191680 681257216 13 3185 26099 29 _ _ (1016967 / 50000) (2033937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681257216 :
    ThetaLowerSegment 681257216 681322752 (17030588340099 / 25000) (17032201257691 / 25000) := by
  exact
    packedTile32768 681257216 681322752 13 3172 26100 29 _ _ (254243 / 12500) (2033947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681322752 :
    ThetaLowerSegment 681322752 681339136 (17032201257691 / 25000) (13626085218261 / 20000) := by
  exact
    packedTile32768 681322752 681339136 11 797 26102 29 _ _ (2033953 / 100000) (508489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681339136 :
    ThetaLowerSegment 681339136 681341184 (13626085218261 / 20000) (68130641690641 / 100000) := by
  exact
    packedTile32768 681339136 681341184 8 106 26102 29 _ _ (508489 / 25000) (2033959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_649341184_681341184 :
    ThetaLowerSegment 649341184 681341184 (12986227721673 / 20000) (68130641690641 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell649341184 cell649406720)
                    (ThetaLowerSegment.join cell649472256 cell649537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell649603328 cell649668864)
                    (ThetaLowerSegment.join cell649734400 cell649799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell649865472 cell649931008)
                    (ThetaLowerSegment.join cell649996544 cell650062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell650127616 cell650193152)
                    (ThetaLowerSegment.join cell650258688 cell650324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell650389760 cell650455296)
                    (ThetaLowerSegment.join cell650520832 cell650586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell650651904 cell650717440)
                    (ThetaLowerSegment.join cell650782976 cell650848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell650914048 cell650979584)
                    (ThetaLowerSegment.join cell651045120 cell651110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell651176192 cell651241728)
                    (ThetaLowerSegment.join cell651307264 cell651372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell651438336 cell651503872)
                    (ThetaLowerSegment.join cell651569408 cell651634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell651700480 cell651766016)
                    (ThetaLowerSegment.join cell651831552 cell651897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell651962624 cell652028160)
                    (ThetaLowerSegment.join cell652093696 cell652159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell652224768 cell652290304)
                    (ThetaLowerSegment.join cell652355840 cell652421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell652486912 cell652552448)
                    (ThetaLowerSegment.join cell652617984 cell652683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell652749056 cell652814592)
                    (ThetaLowerSegment.join cell652880128 cell652945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell653011200 cell653076736)
                    (ThetaLowerSegment.join cell653142272 cell653207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell653273344 cell653338880)
                    (ThetaLowerSegment.join cell653404416 cell653469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell653535488 cell653601024)
                    (ThetaLowerSegment.join cell653666560 cell653732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell653797632 cell653863168)
                    (ThetaLowerSegment.join cell653928704 cell653994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell654059776 cell654125312)
                    (ThetaLowerSegment.join cell654190848 cell654256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell654321920 cell654387456)
                    (ThetaLowerSegment.join cell654452992 cell654518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell654584064 cell654649600)
                    (ThetaLowerSegment.join cell654715136 cell654780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell654846208 cell654911744)
                    (ThetaLowerSegment.join cell654977280 cell655042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell655108352 cell655173888)
                    (ThetaLowerSegment.join cell655239424 cell655304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell655370496 cell655436032)
                    (ThetaLowerSegment.join cell655501568 cell655567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell655632640 cell655698176)
                    (ThetaLowerSegment.join cell655763712 cell655829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell655894784 cell655960320)
                    (ThetaLowerSegment.join cell656025856 cell656091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell656156928 cell656222464)
                    (ThetaLowerSegment.join cell656288000 cell656353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell656419072 cell656484608)
                    (ThetaLowerSegment.join cell656550144 cell656615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell656681216 cell656746752)
                    (ThetaLowerSegment.join cell656812288 cell656877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell656943360 cell657008896)
                    (ThetaLowerSegment.join cell657074432 cell657139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell657205504 cell657271040)
                    (ThetaLowerSegment.join cell657336576 cell657402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell657467648 cell657533184)
                    (ThetaLowerSegment.join cell657598720 cell657664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell657729792 cell657795328)
                    (ThetaLowerSegment.join cell657860864 cell657926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell657991936 cell658057472)
                    (ThetaLowerSegment.join cell658123008 cell658188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell658254080 cell658319616)
                    (ThetaLowerSegment.join cell658385152 cell658450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell658516224 cell658581760)
                    (ThetaLowerSegment.join cell658647296 cell658712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell658778368 cell658843904)
                    (ThetaLowerSegment.join cell658909440 cell658974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell659040512 cell659106048)
                    (ThetaLowerSegment.join cell659171584 cell659237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell659302656 cell659368192)
                    (ThetaLowerSegment.join cell659433728 cell659499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell659564800 cell659630336)
                    (ThetaLowerSegment.join cell659695872 cell659761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell659826944 cell659892480)
                    (ThetaLowerSegment.join cell659958016 cell660023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell660089088 cell660154624)
                    (ThetaLowerSegment.join cell660220160 cell660285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell660351232 cell660416768)
                    (ThetaLowerSegment.join cell660482304 cell660547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell660613376 cell660678912)
                    (ThetaLowerSegment.join cell660744448 cell660809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell660875520 cell660941056)
                    (ThetaLowerSegment.join cell661006592 cell661072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell661137664 cell661203200)
                    (ThetaLowerSegment.join cell661268736 cell661334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell661399808 cell661465344)
                    (ThetaLowerSegment.join cell661530880 cell661596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell661661952 cell661727488)
                    (ThetaLowerSegment.join cell661793024 cell661858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell661924096 cell661989632)
                    (ThetaLowerSegment.join cell662055168 cell662120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell662186240 cell662251776)
                    (ThetaLowerSegment.join cell662317312 cell662382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell662448384 cell662513920)
                    (ThetaLowerSegment.join cell662579456 cell662644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell662710528 cell662776064)
                    (ThetaLowerSegment.join cell662841600 cell662907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell662972672 cell663038208)
                    (ThetaLowerSegment.join cell663103744 cell663169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell663234816 cell663300352)
                    (ThetaLowerSegment.join cell663365888 cell663431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell663496960 cell663562496)
                    (ThetaLowerSegment.join cell663628032 cell663693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell663759104 cell663824640)
                    (ThetaLowerSegment.join cell663890176 cell663955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell664021248 cell664086784)
                    (ThetaLowerSegment.join cell664152320 cell664217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell664283392 cell664348928)
                    (ThetaLowerSegment.join cell664414464 cell664480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell664545536 cell664611072)
                    (ThetaLowerSegment.join cell664676608 cell664742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell664807680 cell664873216)
                    (ThetaLowerSegment.join cell664938752 cell665004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell665069824 cell665135360)
                    (ThetaLowerSegment.join cell665200896 cell665266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell665331968 cell665397504)
                    (ThetaLowerSegment.join cell665463040 cell665528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell665594112 cell665659648)
                    (ThetaLowerSegment.join cell665725184 cell665790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell665856256 cell665921792)
                    (ThetaLowerSegment.join cell665987328 cell666052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell666118400 cell666183936)
                    (ThetaLowerSegment.join cell666249472 cell666315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell666380544 cell666446080)
                    (ThetaLowerSegment.join cell666511616 cell666577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell666642688 cell666708224)
                    (ThetaLowerSegment.join cell666773760 cell666839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell666904832 cell666970368)
                    (ThetaLowerSegment.join cell667035904 cell667101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell667166976 cell667232512)
                    (ThetaLowerSegment.join cell667298048 cell667363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell667429120 cell667494656)
                    (ThetaLowerSegment.join cell667560192 cell667625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell667691264 cell667756800)
                    (ThetaLowerSegment.join cell667822336 cell667887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell667953408 cell668018944)
                    (ThetaLowerSegment.join cell668084480 cell668150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell668215552 cell668281088)
                    (ThetaLowerSegment.join cell668346624 cell668412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell668477696 cell668543232)
                    (ThetaLowerSegment.join cell668608768 cell668674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell668739840 cell668805376)
                    (ThetaLowerSegment.join cell668870912 cell668936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell669001984 cell669067520)
                    (ThetaLowerSegment.join cell669133056 cell669198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell669264128 cell669329664)
                    (ThetaLowerSegment.join cell669395200 cell669460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell669526272 cell669591808)
                    (ThetaLowerSegment.join cell669657344 cell669722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell669788416 cell669853952)
                    (ThetaLowerSegment.join cell669919488 cell669985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell670050560 cell670116096)
                    (ThetaLowerSegment.join cell670181632 cell670247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell670312704 cell670378240)
                    (ThetaLowerSegment.join cell670443776 cell670509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell670574848 cell670640384)
                    (ThetaLowerSegment.join cell670705920 cell670771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell670836992 cell670902528)
                    (ThetaLowerSegment.join cell670968064 cell671033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell671099136 cell671164672)
                    (ThetaLowerSegment.join cell671230208 cell671295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell671361280 cell671426816)
                    (ThetaLowerSegment.join cell671492352 cell671557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell671623424 cell671688960)
                    (ThetaLowerSegment.join cell671754496 cell671820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell671885568 cell671951104)
                    (ThetaLowerSegment.join cell672016640 cell672082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell672147712 cell672213248)
                    (ThetaLowerSegment.join cell672278784 cell672344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell672409856 cell672475392)
                    (ThetaLowerSegment.join cell672540928 cell672606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell672672000 cell672737536)
                    (ThetaLowerSegment.join cell672803072 cell672868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell672934144 cell672999680)
                    (ThetaLowerSegment.join cell673065216 cell673130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell673196288 cell673261824)
                    (ThetaLowerSegment.join cell673327360 cell673392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell673458432 cell673523968)
                    (ThetaLowerSegment.join cell673589504 cell673655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell673720576 cell673786112)
                    (ThetaLowerSegment.join cell673851648 cell673917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell673982720 cell674048256)
                    (ThetaLowerSegment.join cell674113792 cell674179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell674244864 cell674310400)
                    (ThetaLowerSegment.join cell674375936 cell674441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell674507008 cell674572544)
                    (ThetaLowerSegment.join cell674638080 cell674703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell674769152 cell674834688)
                    (ThetaLowerSegment.join cell674900224 cell674965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell675031296 cell675096832)
                    (ThetaLowerSegment.join cell675162368 cell675227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell675293440 cell675358976)
                    (ThetaLowerSegment.join cell675424512 cell675490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell675555584 cell675621120)
                    (ThetaLowerSegment.join cell675686656 cell675752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell675817728 cell675883264)
                    (ThetaLowerSegment.join cell675948800 cell676014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell676079872 cell676145408)
                    (ThetaLowerSegment.join cell676210944 cell676276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell676342016 cell676407552)
                    (ThetaLowerSegment.join cell676473088 cell676538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell676604160 cell676669696)
                    (ThetaLowerSegment.join cell676735232 cell676800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell676866304 cell676931840)
                    (ThetaLowerSegment.join cell676997376 cell677062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell677128448 cell677193984)
                    (ThetaLowerSegment.join cell677259520 cell677325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell677390592 cell677456128)
                    (ThetaLowerSegment.join cell677521664 cell677587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell677652736 cell677718272)
                    (ThetaLowerSegment.join cell677783808 cell677849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell677914880 cell677980416)
                    (ThetaLowerSegment.join cell678045952 cell678111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell678177024 cell678242560)
                    (ThetaLowerSegment.join cell678308096 cell678373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell678439168 cell678504704)
                    (ThetaLowerSegment.join cell678570240 cell678635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell678701312 cell678766848)
                    (ThetaLowerSegment.join cell678832384 cell678897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell678963456 cell679028992)
                    (ThetaLowerSegment.join cell679094528 cell679160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell679225600 cell679291136)
                    (ThetaLowerSegment.join cell679356672 cell679422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell679487744 cell679553280)
                    (ThetaLowerSegment.join cell679618816 cell679684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell679749888 cell679815424)
                    (ThetaLowerSegment.join cell679880960 cell679946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell680012032 cell680077568)
                    (ThetaLowerSegment.join cell680143104 cell680208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell680274176 cell680339712)
                    (ThetaLowerSegment.join cell680405248 cell680470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell680536320 cell680601856)
                    (ThetaLowerSegment.join cell680667392 cell680732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell680798464 cell680864000)
                  (ThetaLowerSegment.join cell680929536 cell680995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell681060608 cell681126144)
                  (ThetaLowerSegment.join cell681191680 cell681257216)))
              (ThetaLowerSegment.join cell681322752 cell681339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
