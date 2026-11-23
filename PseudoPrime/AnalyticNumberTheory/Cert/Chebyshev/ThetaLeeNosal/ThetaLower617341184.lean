/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 617341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell585341184 :
    ThetaLowerSegment 585341184 585406720 (5853077896789 / 10000) (58537253160073 / 100000) := by
  exact
    packedTile32768 585341184 585406720 13 3207 24193 29 _ _ (2018769 / 100000) (504693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585406720 :
    ThetaLowerSegment 585406720 585472256 (58537253160073 / 100000) (58543915134073 / 100000) := by
  exact
    packedTile32768 585406720 585472256 13 3300 24195 29 _ _ (100939 / 5000) (2018783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585472256 :
    ThetaLowerSegment 585472256 585537792 (58543915134073 / 100000) (58550488317569 / 100000) := by
  exact
    packedTile32768 585472256 585537792 13 3256 24196 29 _ _ (2018791 / 100000) (1009397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585537792 :
    ThetaLowerSegment 585537792 585603328 (58550488317569 / 100000) (29278566099121 / 50000) := by
  exact
    packedTile32768 585537792 585603328 13 3291 24197 29 _ _ (2018803 / 100000) (1009403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585603328 :
    ThetaLowerSegment 585603328 585668864 (29278566099121 / 50000) (1830116363311 / 3125) := by
  exact
    packedTile32768 585603328 585668864 13 3265 24199 29 _ _ (1009407 / 50000) (2018817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585668864 :
    ThetaLowerSegment 585668864 585734400 (1830116363311 / 3125) (58570254524827 / 100000) := by
  exact
    packedTile32768 585668864 585734400 13 3235 24200 29 _ _ (80753 / 4000) (504707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585734400 :
    ThetaLowerSegment 585734400 585799936 (58570254524827 / 100000) (58576743063731 / 100000) := by
  exact
    packedTile32768 585734400 585799936 13 3214 24201 29 _ _ (504709 / 25000) (2018839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585799936 :
    ThetaLowerSegment 585799936 585865472 (58576743063731 / 100000) (58583203374131 / 100000) := by
  exact
    packedTile32768 585799936 585865472 13 3200 24203 29 _ _ (2018847 / 100000) (40377 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585865472 :
    ThetaLowerSegment 585865472 585931008 (58583203374131 / 100000) (58589764665881 / 100000) := by
  exact
    packedTile32768 585865472 585931008 13 3250 24204 29 _ _ (2018859 / 100000) (1009431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585931008 :
    ThetaLowerSegment 585931008 585996544 (58589764665881 / 100000) (58596251295191 / 100000) := by
  exact
    packedTile32768 585931008 585996544 13 3213 24206 29 _ _ (201887 / 10000) (2018873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585996544 :
    ThetaLowerSegment 585996544 586062080 (58596251295191 / 100000) (7325339216659 / 12500) := by
  exact
    packedTile32768 585996544 586062080 13 3201 24207 29 _ _ (2018881 / 100000) (504721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586062080 :
    ThetaLowerSegment 586062080 586127616 (7325339216659 / 12500) (14652316259453 / 25000) := by
  exact
    packedTile32768 586062080 586127616 13 3245 24208 29 _ _ (504723 / 25000) (403779 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586127616 :
    ThetaLowerSegment 586127616 586193152 (14652316259453 / 25000) (14653935419659 / 25000) := by
  exact
    packedTile32768 586127616 586193152 13 3208 24210 29 _ _ (2018903 / 100000) (1009453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586193152 :
    ThetaLowerSegment 586193152 586258688 (14653935419659 / 25000) (29311201037961 / 50000) := by
  exact
    packedTile32768 586193152 586258688 13 3299 24211 29 _ _ (1009457 / 50000) (2018917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586258688 :
    ThetaLowerSegment 586258688 586324224 (29311201037961 / 50000) (29314524190157 / 50000) := by
  exact
    packedTile32768 586258688 586324224 13 3292 24212 29 _ _ (1009463 / 50000) (2018929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586324224 :
    ThetaLowerSegment 586324224 586389760 (29314524190157 / 50000) (58635583679383 / 100000) := by
  exact
    packedTile32768 586324224 586389760 13 3237 24214 29 _ _ (2018937 / 100000) (100947 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586389760 :
    ThetaLowerSegment 586389760 586455296 (58635583679383 / 100000) (58642026142451 / 100000) := by
  exact
    packedTile32768 586389760 586455296 13 3191 24215 29 _ _ (504737 / 25000) (2018951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586455296 :
    ThetaLowerSegment 586455296 586520832 (58642026142451 / 100000) (14662145425581 / 25000) := by
  exact
    packedTile32768 586455296 586520832 13 3247 24216 29 _ _ (2018959 / 100000) (1009481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586520832 :
    ThetaLowerSegment 586520832 586586368 (14662145425581 / 25000) (14663819151711 / 25000) := by
  exact
    packedTile32768 586520832 586586368 13 3316 24218 29 _ _ (201897 / 10000) (2018973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586586368 :
    ThetaLowerSegment 586586368 586651904 (14663819151711 / 25000) (14665464622041 / 25000) := by
  exact
    packedTile32768 586586368 586651904 13 3260 24219 29 _ _ (1009491 / 50000) (403797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586651904 :
    ThetaLowerSegment 586651904 586717440 (14665464622041 / 25000) (58668430310379 / 100000) := by
  exact
    packedTile32768 586651904 586717440 13 3255 24220 29 _ _ (2018993 / 100000) (504749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586717440 :
    ThetaLowerSegment 586717440 586782976 (58668430310379 / 100000) (58674961788319 / 100000) := by
  exact
    packedTile32768 586717440 586782976 13 3235 24222 29 _ _ (504751 / 25000) (2019007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586782976 :
    ThetaLowerSegment 586782976 586848512 (58674961788319 / 100000) (14670369287431 / 25000) := by
  exact
    packedTile32768 586782976 586848512 13 3227 24223 29 _ _ (403803 / 20000) (1009509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586848512 :
    ThetaLowerSegment 586848512 586914048 (14670369287431 / 25000) (29344024539677 / 50000) := by
  exact
    packedTile32768 586848512 586914048 13 3255 24224 29 _ _ (1009513 / 50000) (2019029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586914048 :
    ThetaLowerSegment 586914048 586979584 (29344024539677 / 50000) (14673644661253 / 25000) := by
  exact
    packedTile32768 586914048 586979584 13 3234 24226 29 _ _ (2019037 / 100000) (12619 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell586979584 :
    ThetaLowerSegment 586979584 587045120 (14673644661253 / 25000) (58701086039939 / 100000) := by
  exact
    packedTile32768 586979584 587045120 13 3223 24227 29 _ _ (2019049 / 100000) (504763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587045120 :
    ThetaLowerSegment 587045120 587110656 (58701086039939 / 100000) (58707639908699 / 100000) := by
  exact
    packedTile32768 587045120 587110656 13 3246 24229 29 _ _ (100953 / 5000) (2019063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587110656 :
    ThetaLowerSegment 587110656 587176192 (58707639908699 / 100000) (58714157469887 / 100000) := by
  exact
    packedTile32768 587110656 587176192 13 3228 24230 29 _ _ (2019071 / 100000) (1009537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587176192 :
    ThetaLowerSegment 587176192 587241728 (58714157469887 / 100000) (58720745734453 / 100000) := by
  exact
    packedTile32768 587176192 587241728 13 3263 24231 29 _ _ (1009541 / 50000) (403817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587241728 :
    ThetaLowerSegment 587241728 587307264 (58720745734453 / 100000) (5872718462203 / 10000) := by
  exact
    packedTile32768 587241728 587307264 13 3189 24233 29 _ _ (2019093 / 100000) (252387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587307264 :
    ThetaLowerSegment 587307264 587372800 (5872718462203 / 10000) (29366952100071 / 50000) := by
  exact
    packedTile32768 587307264 587372800 13 3328 24234 29 _ _ (63097 / 3125) (2019107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587372800 :
    ThetaLowerSegment 587372800 587438336 (29366952100071 / 50000) (5874041181101 / 10000) := by
  exact
    packedTile32768 587372800 587438336 13 3223 24235 29 _ _ (504779 / 25000) (2019119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587438336 :
    ThetaLowerSegment 587438336 587503872 (5874041181101 / 10000) (58747008298919 / 100000) := by
  exact
    packedTile32768 587438336 587503872 13 3267 24237 29 _ _ (2019127 / 100000) (201913 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587503872 :
    ThetaLowerSegment 587503872 587569408 (58747008298919 / 100000) (11750722983691 / 20000) := by
  exact
    packedTile32768 587503872 587569408 13 3272 24238 29 _ _ (1009569 / 50000) (2019141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587569408 :
    ThetaLowerSegment 587569408 587634944 (11750722983691 / 20000) (58760104463341 / 100000) := by
  exact
    packedTile32768 587569408 587634944 13 3214 24239 29 _ _ (2019149 / 100000) (126197 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587634944 :
    ThetaLowerSegment 587634944 587700480 (58760104463341 / 100000) (58766620292661 / 100000) := by
  exact
    packedTile32768 587634944 587700480 13 3227 24241 29 _ _ (50479 / 2500) (2019163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587700480 :
    ThetaLowerSegment 587700480 587766016 (58766620292661 / 100000) (14693289087297 / 25000) := by
  exact
    packedTile32768 587700480 587766016 13 3237 24242 29 _ _ (2019171 / 100000) (1009587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587766016 :
    ThetaLowerSegment 587766016 587831552 (14693289087297 / 25000) (7347461807563 / 12500) := by
  exact
    packedTile32768 587766016 587831552 13 3238 24243 29 _ _ (1009591 / 50000) (403837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587831552 :
    ThetaLowerSegment 587831552 587897088 (7347461807563 / 12500) (47029020011 / 80) := by
  exact
    packedTile32768 587831552 587897088 13 3259 24245 29 _ _ (1009597 / 50000) (2019197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587897088 :
    ThetaLowerSegment 587897088 587962624 (47029020011 / 80) (1175856344759 / 2000) := by
  exact
    packedTile32768 587897088 587962624 13 3240 24246 29 _ _ (403841 / 20000) (252401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell587962624 :
    ThetaLowerSegment 587962624 588028160 (1175856344759 / 2000) (29399642393399 / 50000) := by
  exact
    packedTile32768 587962624 588028160 13 3203 24247 29 _ _ (126201 / 6250) (2019219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588028160 :
    ThetaLowerSegment 588028160 588093696 (29399642393399 / 50000) (11761157743393 / 20000) := by
  exact
    packedTile32768 588028160 588093696 13 3221 24249 29 _ _ (2019227 / 100000) (201923 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588093696 :
    ThetaLowerSegment 588093696 588159232 (11761157743393 / 20000) (58812329028847 / 100000) := by
  exact
    packedTile32768 588093696 588159232 13 3239 24250 29 _ _ (1009619 / 50000) (2019241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588159232 :
    ThetaLowerSegment 588159232 588224768 (58812329028847 / 100000) (29409370072211 / 50000) := by
  exact
    packedTile32768 588159232 588224768 13 3175 24251 29 _ _ (2019249 / 100000) (504813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588224768 :
    ThetaLowerSegment 588224768 588290304 (29409370072211 / 50000) (29412696803061 / 50000) := by
  exact
    packedTile32768 588224768 588290304 13 3295 24253 29 _ _ (100963 / 5000) (2019263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588290304 :
    ThetaLowerSegment 588290304 588355840 (29412696803061 / 50000) (29415990235693 / 50000) := by
  exact
    packedTile32768 588290304 588355840 13 3262 24254 29 _ _ (252409 / 12500) (80771 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588355840 :
    ThetaLowerSegment 588355840 588421376 (29415990235693 / 50000) (58838561314683 / 100000) := by
  exact
    packedTile32768 588355840 588421376 13 3259 24256 29 _ _ (2019283 / 100000) (1009643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588421376 :
    ThetaLowerSegment 588421376 588486912 (58838561314683 / 100000) (58845065460657 / 100000) := by
  exact
    packedTile32768 588421376 588486912 13 3221 24257 29 _ _ (1009647 / 50000) (2019297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588486912 :
    ThetaLowerSegment 588486912 588552448 (58845065460657 / 100000) (14712891400863 / 25000) := by
  exact
    packedTile32768 588486912 588552448 13 3219 24258 29 _ _ (403861 / 20000) (504827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588552448 :
    ThetaLowerSegment 588552448 588617984 (14712891400863 / 25000) (1471449827157 / 2500) := by
  exact
    packedTile32768 588552448 588617984 13 3183 24260 29 _ _ (504829 / 25000) (2019319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588617984 :
    ThetaLowerSegment 588617984 588683520 (1471449827157 / 2500) (14716119791151 / 25000) := by
  exact
    packedTile32768 588617984 588683520 13 3212 24261 29 _ _ (2019327 / 100000) (201933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588683520 :
    ThetaLowerSegment 588683520 588749056 (14716119791151 / 25000) (5887101576171 / 10000) := by
  exact
    packedTile32768 588683520 588749056 13 3237 24262 29 _ _ (1009669 / 50000) (2019341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588749056 :
    ThetaLowerSegment 588749056 588814592 (5887101576171 / 10000) (2943880043103 / 5000) := by
  exact
    packedTile32768 588749056 588814592 13 3261 24264 29 _ _ (40387 / 2000) (2019353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588814592 :
    ThetaLowerSegment 588814592 588880128 (2943880043103 / 5000) (1472104599473 / 2500) := by
  exact
    packedTile32768 588814592 588880128 13 3260 24265 29 _ _ (2019361 / 100000) (504841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588880128 :
    ThetaLowerSegment 588880128 588945664 (1472104599473 / 2500) (14722705413671 / 25000) := by
  exact
    packedTile32768 588880128 588945664 13 3287 24266 29 _ _ (504843 / 25000) (3231 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell588945664 :
    ThetaLowerSegment 588945664 589011200 (14722705413671 / 25000) (58897515909329 / 100000) := by
  exact
    packedTile32768 588945664 589011200 13 3315 24268 29 _ _ (2019383 / 100000) (1009693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589011200 :
    ThetaLowerSegment 589011200 589076736 (58897515909329 / 100000) (58904020377403 / 100000) := by
  exact
    packedTile32768 589011200 589076736 13 3221 24269 29 _ _ (1009697 / 50000) (2019397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589076736 :
    ThetaLowerSegment 589076736 589142272 (58904020377403 / 100000) (58910611715323 / 100000) := by
  exact
    packedTile32768 589076736 589142272 13 3264 24270 29 _ _ (403881 / 20000) (126213 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589142272 :
    ThetaLowerSegment 589142272 589207808 (58910611715323 / 100000) (58917306079363 / 100000) := by
  exact
    packedTile32768 589142272 589207808 13 3315 24272 29 _ _ (252427 / 12500) (2019419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589207808 :
    ThetaLowerSegment 589207808 589273344 (58917306079363 / 100000) (58923857100551 / 100000) := by
  exact
    packedTile32768 589207808 589273344 13 3244 24273 29 _ _ (2019427 / 100000) (201943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589273344 :
    ThetaLowerSegment 589273344 589338880 (58923857100551 / 100000) (14732597496429 / 25000) := by
  exact
    packedTile32768 589273344 589338880 13 3235 24274 29 _ _ (2019439 / 100000) (1009721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589338880 :
    ThetaLowerSegment 589338880 589404416 (14732597496429 / 25000) (7367119149777 / 12500) := by
  exact
    packedTile32768 589338880 589404416 13 3250 24276 29 _ _ (40389 / 2000) (2019453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589404416 :
    ThetaLowerSegment 589404416 589469952 (7367119149777 / 12500) (2357742192649 / 4000) := by
  exact
    packedTile32768 589404416 589469952 13 3269 24277 29 _ _ (2019461 / 100000) (252433 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589469952 :
    ThetaLowerSegment 589469952 589535488 (2357742192649 / 4000) (11790015542157 / 20000) := by
  exact
    packedTile32768 589469952 589535488 13 3230 24279 29 _ _ (126217 / 6250) (80779 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589535488 :
    ThetaLowerSegment 589535488 589601024 (11790015542157 / 20000) (29478297291213 / 50000) := by
  exact
    packedTile32768 589535488 589601024 13 3227 24280 29 _ _ (2019483 / 100000) (1009743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589601024 :
    ThetaLowerSegment 589601024 589666560 (29478297291213 / 50000) (29481580988457 / 50000) := by
  exact
    packedTile32768 589601024 589666560 13 3252 24281 29 _ _ (1009747 / 50000) (2019497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589666560 :
    ThetaLowerSegment 589666560 589732096 (29481580988457 / 50000) (29484832391507 / 50000) := by
  exact
    packedTile32768 589666560 589732096 13 3220 24283 29 _ _ (403901 / 20000) (504877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589732096 :
    ThetaLowerSegment 589732096 589797632 (29484832391507 / 50000) (235905284431 / 400) := by
  exact
    packedTile32768 589732096 589797632 13 3296 24284 29 _ _ (504879 / 25000) (2019519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589797632 :
    ThetaLowerSegment 589797632 589863168 (235905284431 / 400) (29491493784839 / 50000) := by
  exact
    packedTile32768 589797632 589863168 13 3301 24285 29 _ _ (252441 / 12500) (2019531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589863168 :
    ThetaLowerSegment 589863168 589928704 (29491493784839 / 50000) (58989573286357 / 100000) := by
  exact
    packedTile32768 589863168 589928704 13 3261 24287 29 _ _ (2019539 / 100000) (1009771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589928704 :
    ThetaLowerSegment 589928704 589994240 (58989573286357 / 100000) (58996169136657 / 100000) := by
  exact
    packedTile32768 589928704 589994240 13 3266 24288 29 _ _ (40391 / 2000) (2019553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell589994240 :
    ThetaLowerSegment 589994240 590059776 (58996169136657 / 100000) (29501365345173 / 50000) := by
  exact
    packedTile32768 589994240 590059776 13 3249 24289 29 _ _ (2019561 / 100000) (504891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590059776 :
    ThetaLowerSegment 590059776 590125312 (29501365345173 / 50000) (29504630993097 / 50000) := by
  exact
    packedTile32768 590059776 590125312 13 3234 24291 29 _ _ (504893 / 25000) (80783 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590125312 :
    ThetaLowerSegment 590125312 590190848 (29504630993097 / 50000) (59015823611361 / 100000) := by
  exact
    packedTile32768 590125312 590190848 13 3249 24292 29 _ _ (2019583 / 100000) (1009793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590190848 :
    ThetaLowerSegment 590190848 590256384 (59015823611361 / 100000) (59022371135109 / 100000) := by
  exact
    packedTile32768 590190848 590256384 13 3242 24293 29 _ _ (1009797 / 50000) (2019597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590256384 :
    ThetaLowerSegment 590256384 590321920 (59022371135109 / 100000) (14757278649051 / 25000) := by
  exact
    packedTile32768 590256384 590321920 13 3339 24295 29 _ _ (403921 / 20000) (252451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590321920 :
    ThetaLowerSegment 590321920 590387456 (14757278649051 / 25000) (14758876670211 / 25000) := by
  exact
    packedTile32768 590321920 590387456 13 3165 24296 29 _ _ (63113 / 3125) (2019619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590387456 :
    ThetaLowerSegment 590387456 590452992 (14758876670211 / 25000) (59041951310601 / 100000) := by
  exact
    packedTile32768 590387456 590452992 13 3191 24297 29 _ _ (2019627 / 100000) (201963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590452992 :
    ThetaLowerSegment 590452992 590518528 (59041951310601 / 100000) (59048636315691 / 100000) := by
  exact
    packedTile32768 590452992 590518528 13 3310 24299 29 _ _ (2019639 / 100000) (1009821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590518528 :
    ThetaLowerSegment 590518528 590584064 (59048636315691 / 100000) (59055289042791 / 100000) := by
  exact
    packedTile32768 590518528 590584064 13 3294 24300 29 _ _ (40393 / 2000) (2019653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590584064 :
    ThetaLowerSegment 590584064 590649600 (59055289042791 / 100000) (1181235806631 / 2000) := by
  exact
    packedTile32768 590584064 590649600 13 3219 24301 29 _ _ (2019661 / 100000) (126229 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590649600 :
    ThetaLowerSegment 590649600 590715136 (1181235806631 / 2000) (29534194299987 / 50000) := by
  exact
    packedTile32768 590649600 590715136 13 3267 24303 29 _ _ (252459 / 12500) (80787 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590715136 :
    ThetaLowerSegment 590715136 590780672 (29534194299987 / 50000) (59074893998917 / 100000) := by
  exact
    packedTile32768 590715136 590780672 13 3221 24304 29 _ _ (2019683 / 100000) (1009843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590780672 :
    ThetaLowerSegment 590780672 590846208 (59074893998917 / 100000) (59081455984723 / 100000) := by
  exact
    packedTile32768 590780672 590846208 13 3249 24305 29 _ _ (1009847 / 50000) (2019697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590846208 :
    ThetaLowerSegment 590846208 590911744 (59081455984723 / 100000) (59088133129453 / 100000) := by
  exact
    packedTile32768 590846208 590911744 13 3306 24307 29 _ _ (403941 / 20000) (504927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590911744 :
    ThetaLowerSegment 590911744 590977280 (59088133129453 / 100000) (59094749719069 / 100000) := by
  exact
    packedTile32768 590911744 590977280 13 3276 24308 29 _ _ (504929 / 25000) (2019719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell590977280 :
    ThetaLowerSegment 590977280 591042816 (59094749719069 / 100000) (11820270037381 / 20000) := by
  exact
    packedTile32768 590977280 591042816 13 3268 24310 29 _ _ (2019727 / 100000) (201973 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591042816 :
    ThetaLowerSegment 591042816 591108352 (11820270037381 / 20000) (11821582867081 / 20000) := by
  exact
    packedTile32768 591042816 591108352 13 3250 24311 29 _ _ (1009869 / 50000) (2019741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591108352 :
    ThetaLowerSegment 591108352 591173888 (11821582867081 / 20000) (14778624174349 / 25000) := by
  exact
    packedTile32768 591108352 591173888 13 3259 24312 29 _ _ (2019749 / 100000) (252469 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591173888 :
    ThetaLowerSegment 591173888 591239424 (14778624174349 / 25000) (59121042742797 / 100000) := by
  exact
    packedTile32768 591173888 591239424 13 3241 24314 29 _ _ (2019761 / 100000) (504941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591239424 :
    ThetaLowerSegment 591239424 591304960 (59121042742797 / 100000) (59127647397237 / 100000) := by
  exact
    packedTile32768 591239424 591304960 13 3270 24315 29 _ _ (504943 / 25000) (80791 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591304960 :
    ThetaLowerSegment 591304960 591370496 (59127647397237 / 100000) (59134187454591 / 100000) := by
  exact
    packedTile32768 591304960 591370496 13 3238 24316 29 _ _ (2019783 / 100000) (1009893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591370496 :
    ThetaLowerSegment 591370496 591436032 (59134187454591 / 100000) (59140705329829 / 100000) := by
  exact
    packedTile32768 591370496 591436032 13 3227 24318 29 _ _ (1009897 / 50000) (2019797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591436032 :
    ThetaLowerSegment 591436032 591501568 (59140705329829 / 100000) (59147213141539 / 100000) := by
  exact
    packedTile32768 591436032 591501568 13 3222 24319 29 _ _ (403961 / 20000) (63119 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591501568 :
    ThetaLowerSegment 591501568 591567104 (59147213141539 / 100000) (11830776110831 / 20000) := by
  exact
    packedTile32768 591501568 591567104 13 3301 24320 29 _ _ (252477 / 12500) (2019819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591567104 :
    ThetaLowerSegment 591567104 591632640 (11830776110831 / 20000) (59160331881593 / 100000) := by
  exact
    packedTile32768 591567104 591632640 13 3194 24322 29 _ _ (2019827 / 100000) (201983 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591632640 :
    ThetaLowerSegment 591632640 591698176 (59160331881593 / 100000) (59166956950233 / 100000) := by
  exact
    packedTile32768 591632640 591698176 13 3280 24323 29 _ _ (1009919 / 50000) (2019841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591698176 :
    ThetaLowerSegment 591698176 591763712 (59166956950233 / 100000) (59173586094651 / 100000) := by
  exact
    packedTile32768 591698176 591763712 13 3282 24324 29 _ _ (2019849 / 100000) (504963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591763712 :
    ThetaLowerSegment 591763712 591829248 (59173586094651 / 100000) (59180304149011 / 100000) := by
  exact
    packedTile32768 591763712 591829248 13 3326 24326 29 _ _ (100993 / 5000) (2019863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591829248 :
    ThetaLowerSegment 591829248 591894784 (59180304149011 / 100000) (59186844491309 / 100000) := by
  exact
    packedTile32768 591829248 591894784 13 3238 24327 29 _ _ (2019871 / 100000) (1009937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591894784 :
    ThetaLowerSegment 591894784 591960320 (59186844491309 / 100000) (59193247517249 / 100000) := by
  exact
    packedTile32768 591894784 591960320 13 3170 24328 29 _ _ (1009941 / 50000) (403977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell591960320 :
    ThetaLowerSegment 591960320 592025856 (59193247517249 / 100000) (59199903067979 / 100000) := by
  exact
    packedTile32768 591960320 592025856 13 3295 24330 29 _ _ (1009947 / 50000) (2019897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592025856 :
    ThetaLowerSegment 592025856 592091392 (59199903067979 / 100000) (29603174292417 / 50000) := by
  exact
    packedTile32768 592025856 592091392 13 3191 24331 29 _ _ (403981 / 20000) (504977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592091392 :
    ThetaLowerSegment 592091392 592156928 (29603174292417 / 50000) (29606484934741 / 50000) := by
  exact
    packedTile32768 592091392 592156928 13 3278 24332 29 _ _ (504979 / 25000) (2019919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592156928 :
    ThetaLowerSegment 592156928 592222464 (29606484934741 / 50000) (29609829933853 / 50000) := by
  exact
    packedTile32768 592156928 592222464 13 3312 24334 29 _ _ (2019927 / 100000) (201993 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592222464 :
    ThetaLowerSegment 592222464 592288000 (29609829933853 / 50000) (29613037595397 / 50000) := by
  exact
    packedTile32768 592222464 592288000 13 3176 24335 29 _ _ (1009969 / 50000) (2019941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592288000 :
    ThetaLowerSegment 592288000 592353536 (29613037595397 / 50000) (1184652558107 / 2000) := by
  exact
    packedTile32768 592288000 592353536 13 3244 24336 29 _ _ (2019949 / 100000) (126247 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592353536 :
    ThetaLowerSegment 592353536 592419072 (1184652558107 / 2000) (5923926549391 / 10000) := by
  exact
    packedTile32768 592353536 592419072 13 3286 24338 29 _ _ (50499 / 2500) (2019963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592419072 :
    ThetaLowerSegment 592419072 592484608 (5923926549391 / 10000) (29622892980149 / 50000) := by
  exact
    packedTile32768 592419072 592484608 13 3228 24339 29 _ _ (2019971 / 100000) (1009987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592484608 :
    ThetaLowerSegment 592484608 592550144 (29622892980149 / 50000) (29626139091223 / 50000) := by
  exact
    packedTile32768 592484608 592550144 13 3214 24341 29 _ _ (1009991 / 50000) (403997 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592550144 :
    ThetaLowerSegment 592550144 592615680 (29626139091223 / 50000) (740734731499 / 1250) := by
  exact
    packedTile32768 592550144 592615680 13 3218 24342 29 _ _ (2019993 / 100000) (504999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592615680 :
    ThetaLowerSegment 592615680 592681216 (740734731499 / 1250) (14816309118177 / 25000) := by
  exact
    packedTile32768 592615680 592681216 13 3197 24343 29 _ _ (505001 / 25000) (2020007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592681216 :
    ThetaLowerSegment 592681216 592746752 (14816309118177 / 25000) (14817941290297 / 25000) := by
  exact
    packedTile32768 592681216 592746752 13 3232 24345 29 _ _ (404003 / 20000) (1010009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592746752 :
    ThetaLowerSegment 592746752 592812288 (14817941290297 / 25000) (29639177243 / 50) := by
  exact
    packedTile32768 592746752 592812288 13 3262 24346 29 _ _ (1010013 / 50000) (2020029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592812288 :
    ThetaLowerSegment 592812288 592877824 (29639177243 / 50) (14821218791359 / 25000) := by
  exact
    packedTile32768 592812288 592877824 13 3228 24347 29 _ _ (2020037 / 100000) (50501 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592877824 :
    ThetaLowerSegment 592877824 592943360 (14821218791359 / 25000) (14822853515203 / 25000) := by
  exact
    packedTile32768 592877824 592943360 13 3237 24349 29 _ _ (126253 / 6250) (2020051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell592943360 :
    ThetaLowerSegment 592943360 593008896 (14822853515203 / 25000) (1185960877889 / 2000) := by
  exact
    packedTile32768 592943360 593008896 13 3282 24350 29 _ _ (2020059 / 100000) (1010031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593008896 :
    ThetaLowerSegment 593008896 593074432 (1185960877889 / 2000) (2965226112947 / 5000) := by
  exact
    packedTile32768 593008896 593074432 13 3207 24351 29 _ _ (202007 / 10000) (2020073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593074432 :
    ThetaLowerSegment 593074432 593139968 (2965226112947 / 5000) (29655506391203 / 50000) := by
  exact
    packedTile32768 593074432 593139968 13 3213 24353 29 _ _ (1010041 / 50000) (404017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593139968 :
    ThetaLowerSegment 593139968 593205504 (29655506391203 / 50000) (59317406376751 / 100000) := by
  exact
    packedTile32768 593139968 593205504 13 3165 24354 29 _ _ (2020093 / 100000) (63128 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593205504 :
    ThetaLowerSegment 593205504 593271040 (59317406376751 / 100000) (59323816166743 / 100000) := by
  exact
    packedTile32768 593205504 593271040 13 3173 24355 29 _ _ (252513 / 12500) (2020107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593271040 :
    ThetaLowerSegment 593271040 593336576 (59323816166743 / 100000) (29665181679729 / 50000) := by
  exact
    packedTile32768 593271040 593336576 13 3241 24357 29 _ _ (404023 / 20000) (1010059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593336576 :
    ThetaLowerSegment 593336576 593402112 (29665181679729 / 50000) (29668462364353 / 50000) := by
  exact
    packedTile32768 593336576 593402112 13 3248 24358 29 _ _ (1010063 / 50000) (2020129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593402112 :
    ThetaLowerSegment 593402112 593467648 (29668462364353 / 50000) (59343593200943 / 100000) := by
  exact
    packedTile32768 593402112 593467648 13 3301 24359 29 _ _ (2020137 / 100000) (101007 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593467648 :
    ThetaLowerSegment 593467648 593533184 (59343593200943 / 100000) (59350178883423 / 100000) := by
  exact
    packedTile32768 593467648 593533184 13 3260 24361 29 _ _ (505037 / 25000) (2020151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593533184 :
    ThetaLowerSegment 593533184 593598720 (59350178883423 / 100000) (11871352112289 / 20000) := by
  exact
    packedTile32768 593533184 593598720 13 3258 24362 29 _ _ (2020159 / 100000) (1010081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593598720 :
    ThetaLowerSegment 593598720 593664256 (11871352112289 / 20000) (11872647849327 / 20000) := by
  exact
    packedTile32768 593598720 593664256 13 3207 24363 29 _ _ (202017 / 10000) (2020173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593664256 :
    ThetaLowerSegment 593664256 593729792 (11872647849327 / 20000) (14842456764219 / 25000) := by
  exact
    packedTile32768 593664256 593729792 13 3261 24365 29 _ _ (2020181 / 100000) (252523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593729792 :
    ThetaLowerSegment 593729792 593795328 (14842456764219 / 25000) (14844063321907 / 25000) := by
  exact
    packedTile32768 593729792 593795328 13 3181 24366 29 _ _ (63131 / 3125) (404039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593795328 :
    ThetaLowerSegment 593795328 593860864 (14844063321907 / 25000) (29691441796937 / 50000) := by
  exact
    packedTile32768 593795328 593860864 13 3282 24367 29 _ _ (2020203 / 100000) (1010103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593860864 :
    ThetaLowerSegment 593860864 593926400 (29691441796937 / 50000) (29694793331963 / 50000) := by
  exact
    packedTile32768 593860864 593926400 13 3318 24369 29 _ _ (1010107 / 50000) (2020217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593926400 :
    ThetaLowerSegment 593926400 593991936 (29694793331963 / 50000) (59396295831151 / 100000) := by
  exact
    packedTile32768 593926400 593991936 13 3321 24370 29 _ _ (80809 / 4000) (505057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell593991936 :
    ThetaLowerSegment 593991936 594057472 (59396295831151 / 100000) (59402924225467 / 100000) := by
  exact
    packedTile32768 593991936 594057472 13 3281 24371 29 _ _ (505059 / 25000) (2020239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594057472 :
    ThetaLowerSegment 594057472 594123008 (59402924225467 / 100000) (59409522352169 / 100000) := by
  exact
    packedTile32768 594057472 594123008 13 3266 24373 29 _ _ (2020247 / 100000) (8081 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594123008 :
    ThetaLowerSegment 594123008 594188544 (59409522352169 / 100000) (59416128595829 / 100000) := by
  exact
    packedTile32768 594123008 594188544 13 3270 24374 29 _ _ (1010129 / 50000) (2020261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594188544 :
    ThetaLowerSegment 594188544 594254080 (59416128595829 / 100000) (29711289657373 / 50000) := by
  exact
    packedTile32768 594188544 594254080 13 3193 24375 29 _ _ (2020269 / 100000) (126267 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594254080 :
    ThetaLowerSegment 594254080 594319616 (29711289657373 / 50000) (29714523115513 / 50000) := by
  exact
    packedTile32768 594254080 594319616 13 3201 24377 29 _ _ (50507 / 2500) (2020283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594319616 :
    ThetaLowerSegment 594319616 594385152 (29714523115513 / 50000) (5943568086667 / 10000) := by
  exact
    packedTile32768 594319616 594385152 13 3284 24378 29 _ _ (2020291 / 100000) (1010147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594385152 :
    ThetaLowerSegment 594385152 594450688 (5943568086667 / 10000) (29721097160159 / 50000) := by
  exact
    packedTile32768 594385152 594450688 13 3224 24380 29 _ _ (1010151 / 50000) (404061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594450688 :
    ThetaLowerSegment 594450688 594516224 (29721097160159 / 50000) (14862184023453 / 25000) := by
  exact
    packedTile32768 594450688 594516224 13 3238 24381 29 _ _ (2020313 / 100000) (505079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594516224 :
    ThetaLowerSegment 594516224 594581760 (14862184023453 / 25000) (2972764299211 / 5000) := by
  exact
    packedTile32768 594516224 594581760 13 3242 24382 29 _ _ (505081 / 25000) (2020327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594581760 :
    ThetaLowerSegment 594581760 594647296 (2972764299211 / 5000) (11892366777991 / 20000) := by
  exact
    packedTile32768 594581760 594647296 13 3241 24384 29 _ _ (404067 / 20000) (1010169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594647296 :
    ThetaLowerSegment 594647296 594712832 (11892366777991 / 20000) (59468492950371 / 100000) := by
  exact
    packedTile32768 594647296 594712832 13 3296 24385 29 _ _ (1010173 / 50000) (2020349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594712832 :
    ThetaLowerSegment 594712832 594778368 (59468492950371 / 100000) (3717186017249 / 6250) := by
  exact
    packedTile32768 594712832 594778368 13 3209 24386 29 _ _ (2020357 / 100000) (50509 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594778368 :
    ThetaLowerSegment 594778368 594843904 (3717186017249 / 6250) (743519836501 / 1250) := by
  exact
    packedTile32768 594778368 594843904 13 3272 24388 29 _ _ (126273 / 6250) (2020371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594843904 :
    ThetaLowerSegment 594843904 594909440 (743519836501 / 1250) (1859004659721 / 3125) := by
  exact
    packedTile32768 594843904 594909440 13 3248 24389 29 _ _ (2020379 / 100000) (1010191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594909440 :
    ThetaLowerSegment 594909440 594974976 (1859004659721 / 3125) (7436819723519 / 12500) := by
  exact
    packedTile32768 594909440 594974976 13 3172 24390 29 _ _ (202039 / 10000) (2020393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell594974976 :
    ThetaLowerSegment 594974976 595040512 (7436819723519 / 12500) (59501198846239 / 100000) := by
  exact
    packedTile32768 594974976 595040512 13 3287 24392 29 _ _ (2020401 / 100000) (505101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595040512 :
    ThetaLowerSegment 595040512 595106048 (59501198846239 / 100000) (59507716698577 / 100000) := by
  exact
    packedTile32768 595040512 595106048 13 3226 24393 29 _ _ (2020413 / 100000) (63138 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595106048 :
    ThetaLowerSegment 595106048 595171584 (59507716698577 / 100000) (59514291158273 / 100000) := by
  exact
    packedTile32768 595106048 595171584 13 3254 24394 29 _ _ (252553 / 12500) (2020427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595171584 :
    ThetaLowerSegment 595171584 595237120 (59514291158273 / 100000) (59520978798123 / 100000) := by
  exact
    packedTile32768 595171584 595237120 13 3310 24396 29 _ _ (404087 / 20000) (1010219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595237120 :
    ThetaLowerSegment 595237120 595302656 (59520978798123 / 100000) (59527502818257 / 100000) := by
  exact
    packedTile32768 595237120 595302656 13 3229 24397 29 _ _ (1010223 / 50000) (2020449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595302656 :
    ThetaLowerSegment 595302656 595368192 (59527502818257 / 100000) (29767078091579 / 50000) := by
  exact
    packedTile32768 595302656 595368192 13 3293 24398 29 _ _ (2020457 / 100000) (101023 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595368192 :
    ThetaLowerSegment 595368192 595433728 (29767078091579 / 50000) (29770321952953 / 50000) := by
  exact
    packedTile32768 595368192 595433728 13 3211 24400 29 _ _ (505117 / 25000) (2020471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595433728 :
    ThetaLowerSegment 595433728 595499264 (29770321952953 / 50000) (1488679049279 / 2500) := by
  exact
    packedTile32768 595433728 595499264 13 3226 24401 29 _ _ (2020479 / 100000) (1010241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595499264 :
    ThetaLowerSegment 595499264 595564800 (1488679049279 / 2500) (2977687236379 / 5000) := by
  exact
    packedTile32768 595499264 595564800 13 3258 24402 29 _ _ (202049 / 10000) (2020493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595564800 :
    ThetaLowerSegment 595564800 595630336 (2977687236379 / 5000) (59560353786351 / 100000) := by
  exact
    packedTile32768 595564800 595630336 13 3271 24404 29 _ _ (2020501 / 100000) (252563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595630336 :
    ThetaLowerSegment 595630336 595695872 (59560353786351 / 100000) (11913388939299 / 20000) := by
  exact
    packedTile32768 595630336 595695872 13 3262 24405 29 _ _ (63141 / 3125) (404103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595695872 :
    ThetaLowerSegment 595695872 595761408 (11913388939299 / 20000) (59573555847751 / 100000) := by
  exact
    packedTile32768 595695872 595761408 13 3272 24406 29 _ _ (2020523 / 100000) (1010263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595761408 :
    ThetaLowerSegment 595761408 595826944 (59573555847751 / 100000) (11916026941291 / 20000) := by
  exact
    packedTile32768 595761408 595826944 13 3256 24408 29 _ _ (1010267 / 50000) (2020537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595826944 :
    ThetaLowerSegment 595826944 595892480 (11916026941291 / 20000) (11917357268119 / 20000) := by
  exact
    packedTile32768 595826944 595892480 13 3292 24409 29 _ _ (404109 / 20000) (505137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595892480 :
    ThetaLowerSegment 595892480 595958016 (11917357268119 / 20000) (59593431949279 / 100000) := by
  exact
    packedTile32768 595892480 595958016 13 3289 24410 29 _ _ (505139 / 25000) (2020559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell595958016 :
    ThetaLowerSegment 595958016 596023552 (59593431949279 / 100000) (7449995050157 / 12500) := by
  exact
    packedTile32768 595958016 596023552 13 3231 24412 29 _ _ (2020567 / 100000) (202057 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596023552 :
    ThetaLowerSegment 596023552 596089088 (7449995050157 / 12500) (29803323246929 / 50000) := by
  exact
    packedTile32768 596023552 596089088 13 3309 24413 29 _ _ (1010289 / 50000) (2020581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596089088 :
    ThetaLowerSegment 596089088 596154624 (29803323246929 / 50000) (476905755759 / 800) := by
  exact
    packedTile32768 596089088 596154624 13 3253 24414 29 _ _ (2020589 / 100000) (126287 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596154624 :
    ThetaLowerSegment 596154624 596220160 (476905755759 / 800) (2384791699267 / 4000) := by
  exact
    packedTile32768 596154624 596220160 13 3253 24416 29 _ _ (10103 / 500) (2020603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596220160 :
    ThetaLowerSegment 596220160 596285696 (2384791699267 / 4000) (14906574207121 / 25000) := by
  exact
    packedTile32768 596220160 596285696 13 3219 24417 29 _ _ (2020611 / 100000) (1010307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596285696 :
    ThetaLowerSegment 596285696 596351232 (14906574207121 / 25000) (298164602137 / 500) := by
  exact
    packedTile32768 596285696 596351232 13 3278 24418 29 _ _ (1010311 / 50000) (3233 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596351232 :
    ThetaLowerSegment 596351232 596416768 (298164602137 / 500) (59639465257687 / 100000) := by
  exact
    packedTile32768 596351232 596416768 13 3239 24420 29 _ _ (2020633 / 100000) (505159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596416768 :
    ThetaLowerSegment 596416768 596482304 (59639465257687 / 100000) (59646010123603 / 100000) := by
  exact
    packedTile32768 596416768 596482304 13 3239 24421 29 _ _ (505161 / 25000) (2020647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596482304 :
    ThetaLowerSegment 596482304 596547840 (59646010123603 / 100000) (29826247202749 / 50000) := by
  exact
    packedTile32768 596482304 596547840 13 3209 24422 29 _ _ (404131 / 20000) (1010329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596547840 :
    ThetaLowerSegment 596547840 596613376 (29826247202749 / 50000) (14914773474347 / 25000) := by
  exact
    packedTile32768 596547840 596613376 13 3266 24424 29 _ _ (404133 / 20000) (505167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596613376 :
    ThetaLowerSegment 596613376 596678912 (14914773474347 / 25000) (14916414263259 / 25000) := by
  exact
    packedTile32768 596613376 596678912 13 3248 24425 29 _ _ (505169 / 25000) (2020679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596678912 :
    ThetaLowerSegment 596678912 596744448 (14916414263259 / 25000) (1864756630052 / 3125) := by
  exact
    packedTile32768 596678912 596744448 13 3244 24427 29 _ _ (2020687 / 100000) (202069 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596744448 :
    ThetaLowerSegment 596744448 596809984 (1864756630052 / 3125) (29839384663337 / 50000) := by
  exact
    packedTile32768 596744448 596809984 13 3245 24428 29 _ _ (1010349 / 50000) (2020701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596809984 :
    ThetaLowerSegment 596809984 596875520 (29839384663337 / 50000) (59685342693051 / 100000) := by
  exact
    packedTile32768 596809984 596875520 13 3253 24429 29 _ _ (2020709 / 100000) (252589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596875520 :
    ThetaLowerSegment 596875520 596941056 (59685342693051 / 100000) (59691881742971 / 100000) := by
  exact
    packedTile32768 596875520 596941056 13 3236 24431 29 _ _ (25259 / 1250) (2020723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell596941056 :
    ThetaLowerSegment 596941056 597006592 (59691881742971 / 100000) (3731152691033 / 6250) := by
  exact
    packedTile32768 596941056 597006592 13 3247 24432 29 _ _ (2020731 / 100000) (1010367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597006592 :
    ThetaLowerSegment 597006592 597072128 (3731152691033 / 6250) (29852552721451 / 50000) := by
  exact
    packedTile32768 597006592 597072128 13 3297 24433 29 _ _ (1010371 / 50000) (404149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597072128 :
    ThetaLowerSegment 597072128 597137664 (29852552721451 / 50000) (29855794009263 / 50000) := by
  exact
    packedTile32768 597072128 597137664 13 3208 24435 29 _ _ (2020753 / 100000) (505189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597137664 :
    ThetaLowerSegment 597137664 597203200 (29855794009263 / 50000) (29859096948021 / 50000) := by
  exact
    packedTile32768 597137664 597203200 13 3269 24436 29 _ _ (505191 / 25000) (2020767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597203200 :
    ThetaLowerSegment 597203200 597268736 (29859096948021 / 50000) (59724832141917 / 100000) := by
  exact
    packedTile32768 597203200 597268736 13 3285 24437 29 _ _ (80831 / 4000) (1010389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597268736 :
    ThetaLowerSegment 597268736 597334272 (59724832141917 / 100000) (59731349176767 / 100000) := by
  exact
    packedTile32768 597268736 597334272 13 3225 24439 29 _ _ (1010393 / 50000) (2020789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597334272 :
    ThetaLowerSegment 597334272 597399808 (59731349176767 / 100000) (7467226208097 / 12500) := by
  exact
    packedTile32768 597334272 597399808 13 3197 24440 29 _ _ (2020797 / 100000) (2526 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597399808 :
    ThetaLowerSegment 597399808 597465344 (7467226208097 / 12500) (3734020928363 / 6250) := by
  exact
    packedTile32768 597399808 597465344 13 3229 24441 29 _ _ (252601 / 12500) (2020811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597465344 :
    ThetaLowerSegment 597465344 597530880 (3734020928363 / 6250) (59750759037409 / 100000) := by
  exact
    packedTile32768 597465344 597530880 13 3179 24443 29 _ _ (2020819 / 100000) (1010411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597530880 :
    ThetaLowerSegment 597530880 597596416 (59750759037409 / 100000) (59757191339299 / 100000) := by
  exact
    packedTile32768 597530880 597596416 13 3183 24444 29 _ _ (202083 / 10000) (2020833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597596416 :
    ThetaLowerSegment 597596416 597661952 (59757191339299 / 100000) (29881925005197 / 50000) := by
  exact
    packedTile32768 597596416 597661952 13 3295 24445 29 _ _ (2020841 / 100000) (505211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597661952 :
    ThetaLowerSegment 597661952 597727488 (29881925005197 / 50000) (29885169483083 / 50000) := by
  exact
    packedTile32768 597661952 597727488 13 3211 24447 29 _ _ (505213 / 25000) (404171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597727488 :
    ThetaLowerSegment 597727488 597793024 (29885169483083 / 50000) (29888467531499 / 50000) := by
  exact
    packedTile32768 597727488 597793024 13 3264 24448 29 _ _ (2020863 / 100000) (1010433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597793024 :
    ThetaLowerSegment 597793024 597858560 (29888467531499 / 50000) (7472926495521 / 12500) := by
  exact
    packedTile32768 597793024 597858560 13 3205 24449 29 _ _ (1010437 / 50000) (2020877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597858560 :
    ThetaLowerSegment 597858560 597924096 (7472926495521 / 12500) (29895002045519 / 50000) := by
  exact
    packedTile32768 597858560 597924096 13 3262 24451 29 _ _ (404177 / 20000) (252611 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597924096 :
    ThetaLowerSegment 597924096 597989632 (29895002045519 / 50000) (29898240531359 / 50000) := by
  exact
    packedTile32768 597924096 597989632 13 3205 24452 29 _ _ (63153 / 3125) (2020899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell597989632 :
    ThetaLowerSegment 597989632 598055168 (29898240531359 / 50000) (5980306113591 / 10000) := by
  exact
    packedTile32768 597989632 598055168 13 3256 24453 29 _ _ (2020907 / 100000) (202091 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598055168 :
    ThetaLowerSegment 598055168 598120704 (5980306113591 / 10000) (5980954828269 / 10000) := by
  exact
    packedTile32768 598055168 598120704 13 3210 24455 29 _ _ (1010459 / 50000) (2020921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598120704 :
    ThetaLowerSegment 598120704 598186240 (5980954828269 / 10000) (11963196988311 / 20000) := by
  exact
    packedTile32768 598120704 598186240 13 3185 24456 29 _ _ (2020929 / 100000) (505233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598186240 :
    ThetaLowerSegment 598186240 598251776 (11963196988311 / 20000) (11964520299823 / 20000) := by
  exact
    packedTile32768 598186240 598251776 13 3274 24457 29 _ _ (101047 / 5000) (2020943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598251776 :
    ThetaLowerSegment 598251776 598317312 (11964520299823 / 20000) (14957266630341 / 25000) := by
  exact
    packedTile32768 598251776 598317312 13 3199 24459 29 _ _ (2020951 / 100000) (1010477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598317312 :
    ThetaLowerSegment 598317312 598382848 (14957266630341 / 25000) (2991785572221 / 5000) := by
  exact
    packedTile32768 598317312 598382848 13 3288 24460 29 _ _ (1010481 / 50000) (404193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598382848 :
    ThetaLowerSegment 598382848 598448384 (2991785572221 / 5000) (11968461984253 / 20000) := by
  exact
    packedTile32768 598382848 598448384 13 3265 24461 29 _ _ (2020973 / 100000) (126311 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598448384 :
    ThetaLowerSegment 598448384 598513920 (11968461984253 / 20000) (59848690167753 / 100000) := by
  exact
    packedTile32768 598448384 598513920 13 3157 24463 29 _ _ (252623 / 12500) (2020987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598513920 :
    ThetaLowerSegment 598513920 598579456 (59848690167753 / 100000) (59855314989363 / 100000) := by
  exact
    packedTile32768 598513920 598579456 13 3278 24464 29 _ _ (404199 / 20000) (1010499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598579456 :
    ThetaLowerSegment 598579456 598644992 (59855314989363 / 100000) (59862020683953 / 100000) := by
  exact
    packedTile32768 598579456 598644992 13 3318 24465 29 _ _ (404201 / 20000) (126313 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598644992 :
    ThetaLowerSegment 598644992 598710528 (59862020683953 / 100000) (59868506124297 / 100000) := by
  exact
    packedTile32768 598644992 598710528 13 3209 24467 29 _ _ (252627 / 12500) (2021019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598710528 :
    ThetaLowerSegment 598710528 598776064 (59868506124297 / 100000) (11975012467177 / 20000) := by
  exact
    packedTile32768 598710528 598776064 13 3244 24468 29 _ _ (2021027 / 100000) (202103 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598776064 :
    ThetaLowerSegment 598776064 598841600 (11975012467177 / 20000) (59881636772499 / 100000) := by
  exact
    packedTile32768 598776064 598841600 13 3253 24469 29 _ _ (1010519 / 50000) (2021041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598841600 :
    ThetaLowerSegment 598841600 598907136 (59881636772499 / 100000) (59888176887063 / 100000) := by
  exact
    packedTile32768 598841600 598907136 13 3236 24471 29 _ _ (2021049 / 100000) (505263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598907136 :
    ThetaLowerSegment 598907136 598972672 (59888176887063 / 100000) (59894719058283 / 100000) := by
  exact
    packedTile32768 598907136 598972672 13 3237 24472 29 _ _ (101053 / 5000) (2021063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell598972672 :
    ThetaLowerSegment 598972672 599038208 (59894719058283 / 100000) (59901315834027 / 100000) := by
  exact
    packedTile32768 598972672 599038208 13 3264 24473 29 _ _ (2021071 / 100000) (1010537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599038208 :
    ThetaLowerSegment 599038208 599103744 (59901315834027 / 100000) (59907888392691 / 100000) := by
  exact
    packedTile32768 599038208 599103744 13 3252 24475 29 _ _ (1010541 / 50000) (404217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599103744 :
    ThetaLowerSegment 599103744 599169280 (59907888392691 / 100000) (59914347805919 / 100000) := by
  exact
    packedTile32768 599103744 599169280 13 3196 24476 29 _ _ (2021093 / 100000) (252637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599169280 :
    ThetaLowerSegment 599169280 599234816 (59914347805919 / 100000) (59920750663391 / 100000) := by
  exact
    packedTile32768 599169280 599234816 13 3168 24477 29 _ _ (126319 / 6250) (2021107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599234816 :
    ThetaLowerSegment 599234816 599300352 (59920750663391 / 100000) (59927303118221 / 100000) := by
  exact
    packedTile32768 599234816 599300352 13 3242 24479 29 _ _ (404223 / 20000) (1010559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599300352 :
    ThetaLowerSegment 599300352 599365888 (59927303118221 / 100000) (59933982939651 / 100000) := by
  exact
    packedTile32768 599300352 599365888 13 3305 24480 29 _ _ (1010563 / 50000) (2021129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599365888 :
    ThetaLowerSegment 599365888 599431424 (59933982939651 / 100000) (59940527381257 / 100000) := by
  exact
    packedTile32768 599365888 599431424 13 3238 24481 29 _ _ (2021137 / 100000) (101057 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599431424 :
    ThetaLowerSegment 599431424 599496960 (59940527381257 / 100000) (59946918251233 / 100000) := by
  exact
    packedTile32768 599431424 599496960 13 3162 24483 29 _ _ (505287 / 25000) (2021151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599496960 :
    ThetaLowerSegment 599496960 599562496 (59946918251233 / 100000) (1199070265861 / 2000) := by
  exact
    packedTile32768 599496960 599562496 13 3263 24484 29 _ _ (2021159 / 100000) (1010581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599562496 :
    ThetaLowerSegment 599562496 599628032 (1199070265861 / 2000) (5995997699471 / 10000) := by
  exact
    packedTile32768 599562496 599628032 13 3198 24485 29 _ _ (202117 / 10000) (2021173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599628032 :
    ThetaLowerSegment 599628032 599693568 (5995997699471 / 10000) (2398667088389 / 4000) := by
  exact
    packedTile32768 599628032 599693568 13 3315 24487 29 _ _ (2021181 / 100000) (63162 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599693568 :
    ThetaLowerSegment 599693568 599759104 (2398667088389 / 4000) (29986543203193 / 50000) := by
  exact
    packedTile32768 599693568 599759104 13 3171 24488 29 _ _ (2021191 / 100000) (1010597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599759104 :
    ThetaLowerSegment 599759104 599824640 (29986543203193 / 50000) (29989803402019 / 50000) := by
  exact
    packedTile32768 599759104 599824640 13 3226 24489 29 _ _ (1010601 / 50000) (404241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599824640 :
    ThetaLowerSegment 599824640 599890176 (29989803402019 / 50000) (29993077767079 / 50000) := by
  exact
    packedTile32768 599824640 599890176 13 3240 24491 29 _ _ (2021213 / 100000) (63163 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599890176 :
    ThetaLowerSegment 599890176 599955712 (29993077767079 / 50000) (29996397627499 / 50000) := by
  exact
    packedTile32768 599890176 599955712 13 3285 24492 29 _ _ (252653 / 12500) (2021227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell599955712 :
    ThetaLowerSegment 599955712 600021248 (29996397627499 / 50000) (59999301610463 / 100000) := by
  exact
    packedTile32768 599955712 600021248 13 3219 24493 29 _ _ (404247 / 20000) (1010619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600021248 :
    ThetaLowerSegment 600021248 600086784 (59999301610463 / 100000) (60005799916353 / 100000) := by
  exact
    packedTile32768 600021248 600086784 13 3215 24495 29 _ _ (1010623 / 50000) (2021249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600086784 :
    ThetaLowerSegment 600086784 600152320 (60005799916353 / 100000) (30006252212911 / 50000) := by
  exact
    packedTile32768 600086784 600152320 13 3317 24496 29 _ _ (2021257 / 100000) (101063 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600152320 :
    ThetaLowerSegment 600152320 600217856 (30006252212911 / 50000) (30009559007359 / 50000) := by
  exact
    packedTile32768 600152320 600217856 13 3272 24498 29 _ _ (505317 / 25000) (2021271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600217856 :
    ThetaLowerSegment 600217856 600283392 (30009559007359 / 50000) (60025721533211 / 100000) := by
  exact
    packedTile32768 600217856 600283392 13 3267 24499 29 _ _ (2021279 / 100000) (1010641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600283392 :
    ThetaLowerSegment 600283392 600348928 (60025721533211 / 100000) (60032304874741 / 100000) := by
  exact
    packedTile32768 600283392 600348928 13 3257 24500 29 _ _ (202129 / 10000) (2021293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600348928 :
    ThetaLowerSegment 600348928 600414464 (60032304874741 / 100000) (15009714988471 / 25000) := by
  exact
    packedTile32768 600348928 600414464 13 3243 24502 29 _ _ (2021301 / 100000) (252663 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600414464 :
    ThetaLowerSegment 600414464 600480000 (15009714988471 / 25000) (15011337091351 / 25000) := by
  exact
    packedTile32768 600414464 600480000 13 3210 24503 29 _ _ (63166 / 3125) (404263 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600480000 :
    ThetaLowerSegment 600480000 600545536 (15011337091351 / 25000) (30025967926901 / 50000) := by
  exact
    packedTile32768 600480000 600545536 13 3259 24504 29 _ _ (1010661 / 50000) (80853 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600545536 :
    ThetaLowerSegment 600545536 600611072 (30025967926901 / 50000) (30029262699691 / 50000) := by
  exact
    packedTile32768 600545536 600611072 13 3260 24506 29 _ _ (2021333 / 100000) (252667 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600611072 :
    ThetaLowerSegment 600611072 600676608 (30029262699691 / 50000) (30032531212939 / 50000) := by
  exact
    packedTile32768 600611072 600676608 13 3234 24507 29 _ _ (63167 / 3125) (2021347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600676608 :
    ThetaLowerSegment 600676608 600742144 (30032531212939 / 50000) (30035785594489 / 50000) := by
  exact
    packedTile32768 600676608 600742144 13 3220 24508 29 _ _ (404271 / 20000) (1010679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600742144 :
    ThetaLowerSegment 600742144 600807680 (30035785594489 / 50000) (15019531619729 / 25000) := by
  exact
    packedTile32768 600742144 600807680 13 3243 24510 29 _ _ (1010683 / 50000) (2021369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600807680 :
    ThetaLowerSegment 600807680 600873216 (15019531619729 / 25000) (15021209362639 / 25000) := by
  exact
    packedTile32768 600807680 600873216 13 3320 24511 29 _ _ (2021377 / 100000) (101069 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600873216 :
    ThetaLowerSegment 600873216 600938752 (15021209362639 / 25000) (7511417531969 / 12500) := by
  exact
    packedTile32768 600873216 600938752 13 3217 24512 29 _ _ (505347 / 25000) (2021391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell600938752 :
    ThetaLowerSegment 600938752 601004288 (7511417531969 / 12500) (12019576704863 / 20000) := by
  exact
    packedTile32768 600938752 601004288 13 3237 24514 29 _ _ (2021399 / 100000) (1010701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601004288 :
    ThetaLowerSegment 601004288 601069824 (12019576704863 / 20000) (480835075031 / 800) := by
  exact
    packedTile32768 601004288 601069824 13 3216 24515 29 _ _ (202141 / 10000) (2021413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601069824 :
    ThetaLowerSegment 601069824 601135360 (480835075031 / 800) (60110897397337 / 100000) := by
  exact
    packedTile32768 601069824 601135360 13 3222 24516 29 _ _ (2021421 / 100000) (126339 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601135360 :
    ThetaLowerSegment 601135360 601200896 (60110897397337 / 100000) (60117600465849 / 100000) := by
  exact
    packedTile32768 601135360 601200896 13 3316 24518 29 _ _ (252679 / 12500) (404287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601200896 :
    ThetaLowerSegment 601200896 601266432 (60117600465849 / 100000) (60123996308337 / 100000) := by
  exact
    packedTile32768 601200896 601266432 13 3164 24519 29 _ _ (1010721 / 50000) (404289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601266432 :
    ThetaLowerSegment 601266432 601331968 (60123996308337 / 100000) (12026095417331 / 20000) := by
  exact
    packedTile32768 601266432 601331968 13 3206 24520 29 _ _ (2021453 / 100000) (126341 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601331968 :
    ThetaLowerSegment 601331968 601397504 (12026095417331 / 20000) (60137129724679 / 100000) := by
  exact
    packedTile32768 601331968 601397504 13 3291 24522 29 _ _ (252683 / 12500) (2021467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601397504 :
    ThetaLowerSegment 601397504 601463040 (60137129724679 / 100000) (30071860877327 / 50000) := by
  exact
    packedTile32768 601397504 601463040 13 3261 24523 29 _ _ (80859 / 4000) (1010739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601463040 :
    ThetaLowerSegment 601463040 601528576 (30071860877327 / 50000) (3007519733997 / 5000) := by
  exact
    packedTile32768 601463040 601528576 13 3301 24524 29 _ _ (1010743 / 50000) (2021489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601528576 :
    ThetaLowerSegment 601528576 601594112 (3007519733997 / 5000) (3759805483019 / 6250) := by
  exact
    packedTile32768 601528576 601594112 13 3212 24526 29 _ _ (2021497 / 100000) (4043 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601594112 :
    ThetaLowerSegment 601594112 601659648 (3759805483019 / 6250) (7520432203663 / 12500) := by
  exact
    packedTile32768 601594112 601659648 13 3250 24527 29 _ _ (505377 / 25000) (2021511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601659648 :
    ThetaLowerSegment 601659648 601725184 (7520432203663 / 12500) (60170102362257 / 100000) := by
  exact
    packedTile32768 601659648 601725184 13 3287 24528 29 _ _ (2021519 / 100000) (1010761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601725184 :
    ThetaLowerSegment 601725184 601790720 (60170102362257 / 100000) (60176666270167 / 100000) := by
  exact
    packedTile32768 601725184 601790720 13 3247 24530 29 _ _ (202153 / 10000) (2021533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601790720 :
    ThetaLowerSegment 601790720 601856256 (60176666270167 / 100000) (300915807407 / 500) := by
  exact
    packedTile32768 601790720 601856256 13 3213 24531 29 _ _ (2021541 / 100000) (252693 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601856256 :
    ThetaLowerSegment 601856256 601921792 (300915807407 / 500) (60189668854069 / 100000) := by
  exact
    packedTile32768 601856256 601921792 13 3219 24532 29 _ _ (2021551 / 100000) (1010777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601921792 :
    ThetaLowerSegment 601921792 601987328 (60189668854069 / 100000) (60196158068089 / 100000) := by
  exact
    packedTile32768 601921792 601987328 13 3210 24534 29 _ _ (1010781 / 50000) (404313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell601987328 :
    ThetaLowerSegment 601987328 602052864 (60196158068089 / 100000) (3762669626833 / 6250) := by
  exact
    packedTile32768 601987328 602052864 13 3243 24535 29 _ _ (2021573 / 100000) (252697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602052864 :
    ThetaLowerSegment 602052864 602118400 (3762669626833 / 6250) (75261562263 / 125) := by
  exact
    packedTile32768 602052864 602118400 13 3233 24536 29 _ _ (126349 / 6250) (2021587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602118400 :
    ThetaLowerSegment 602118400 602183936 (75261562263 / 125) (12043173298167 / 20000) := by
  exact
    packedTile32768 602118400 602183936 13 3273 24538 29 _ _ (404319 / 20000) (1010799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602183936 :
    ThetaLowerSegment 602183936 602249472 (12043173298167 / 20000) (60222291154703 / 100000) := by
  exact
    packedTile32768 602183936 602249472 13 3178 24539 29 _ _ (1010803 / 50000) (2021609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602249472 :
    ThetaLowerSegment 602249472 602315008 (60222291154703 / 100000) (60228901842293 / 100000) := by
  exact
    packedTile32768 602249472 602315008 13 3270 24540 29 _ _ (2021617 / 100000) (101081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602315008 :
    ThetaLowerSegment 602315008 602380544 (60228901842293 / 100000) (60235552998413 / 100000) := by
  exact
    packedTile32768 602315008 602380544 13 3290 24542 29 _ _ (505407 / 25000) (2021631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602380544 :
    ThetaLowerSegment 602380544 602446080 (60235552998413 / 100000) (60242145559931 / 100000) := by
  exact
    packedTile32768 602380544 602446080 13 3261 24543 29 _ _ (1010819 / 50000) (2021641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602446080 :
    ThetaLowerSegment 602446080 602511616 (60242145559931 / 100000) (12049757739709 / 20000) := by
  exact
    packedTile32768 602446080 602511616 13 3286 24544 29 _ _ (2021649 / 100000) (505413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602511616 :
    ThetaLowerSegment 602511616 602577152 (12049757739709 / 20000) (12051053219437 / 20000) := by
  exact
    packedTile32768 602511616 602577152 13 3204 24546 29 _ _ (101083 / 5000) (2021663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602577152 :
    ThetaLowerSegment 602577152 602642688 (12051053219437 / 20000) (1883181822903 / 3125) := by
  exact
    packedTile32768 602577152 602642688 13 3241 24547 29 _ _ (2021671 / 100000) (1010837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602642688 :
    ThetaLowerSegment 602642688 602708224 (1883181822903 / 3125) (7533557192073 / 12500) := by
  exact
    packedTile32768 602642688 602708224 13 3284 24548 29 _ _ (1010841 / 50000) (404337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602708224 :
    ThetaLowerSegment 602708224 602773760 (7533557192073 / 12500) (7534365869273 / 12500) := by
  exact
    packedTile32768 602708224 602773760 13 3200 24550 29 _ _ (2021693 / 100000) (63178 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602773760 :
    ThetaLowerSegment 602773760 602839296 (7534365869273 / 12500) (7535183648541 / 12500) := by
  exact
    packedTile32768 602773760 602839296 13 3236 24551 29 _ _ (252713 / 12500) (2021707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602839296 :
    ThetaLowerSegment 602839296 602904832 (7535183648541 / 12500) (60287960915193 / 100000) := by
  exact
    packedTile32768 602839296 602904832 13 3211 24552 29 _ _ (404343 / 20000) (1010859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602904832 :
    ThetaLowerSegment 602904832 602970368 (60287960915193 / 100000) (60294523434543 / 100000) := by
  exact
    packedTile32768 602904832 602970368 13 3246 24554 29 _ _ (80869 / 4000) (63179 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell602970368 :
    ThetaLowerSegment 602970368 603035904 (60294523434543 / 100000) (60301183032927 / 100000) := by
  exact
    packedTile32768 602970368 603035904 13 3294 24555 29 _ _ (252717 / 12500) (2021739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603035904 :
    ThetaLowerSegment 603035904 603101440 (60301183032927 / 100000) (30153940540369 / 50000) := by
  exact
    packedTile32768 603035904 603101440 13 3313 24556 29 _ _ (2021747 / 100000) (8087 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603101440 :
    ThetaLowerSegment 603101440 603166976 (30153940540369 / 50000) (30157151092073 / 50000) := by
  exact
    packedTile32768 603101440 603166976 13 3176 24558 29 _ _ (1010879 / 50000) (2021761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603166976 :
    ThetaLowerSegment 603166976 603232512 (30157151092073 / 50000) (12064174991033 / 20000) := by
  exact
    packedTile32768 603166976 603232512 13 3251 24559 29 _ _ (2021769 / 100000) (505443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603232512 :
    ThetaLowerSegment 603232512 603298048 (12064174991033 / 20000) (2413097991349 / 4000) := by
  exact
    packedTile32768 603232512 603298048 13 3252 24560 29 _ _ (101089 / 5000) (2021783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603298048 :
    ThetaLowerSegment 603298048 603363584 (2413097991349 / 4000) (1885439849776 / 3125) := by
  exact
    packedTile32768 603298048 603363584 13 3277 24562 29 _ _ (2021791 / 100000) (1010897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603363584 :
    ThetaLowerSegment 603363584 603429120 (1885439849776 / 3125) (15085159490531 / 25000) := by
  exact
    packedTile32768 603363584 603429120 13 3246 24563 29 _ _ (1010901 / 50000) (404361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603429120 :
    ThetaLowerSegment 603429120 603494656 (15085159490531 / 25000) (15086787049191 / 25000) := by
  exact
    packedTile32768 603429120 603494656 13 3220 24564 29 _ _ (505453 / 25000) (404363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603494656 :
    ThetaLowerSegment 603494656 603560192 (15086787049191 / 25000) (60353749448859 / 100000) := by
  exact
    packedTile32768 603494656 603560192 13 3265 24566 29 _ _ (2021823 / 100000) (1010913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603560192 :
    ThetaLowerSegment 603560192 603625728 (60353749448859 / 100000) (60360332540363 / 100000) := by
  exact
    packedTile32768 603560192 603625728 13 3256 24567 29 _ _ (1010917 / 50000) (2021837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603625728 :
    ThetaLowerSegment 603625728 603691264 (60360332540363 / 100000) (60366935886133 / 100000) := by
  exact
    packedTile32768 603625728 603691264 13 3266 24568 29 _ _ (404369 / 20000) (252731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603691264 :
    ThetaLowerSegment 603691264 603756800 (60366935886133 / 100000) (60373537245973 / 100000) := by
  exact
    packedTile32768 603691264 603756800 13 3265 24570 29 _ _ (63183 / 3125) (2021859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603756800 :
    ThetaLowerSegment 603756800 603822336 (60373537245973 / 100000) (150950427479 / 250) := by
  exact
    packedTile32768 603756800 603822336 13 3281 24571 29 _ _ (2021867 / 100000) (202187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603822336 :
    ThetaLowerSegment 603822336 603887872 (150950427479 / 250) (30193337686563 / 50000) := by
  exact
    packedTile32768 603822336 603887872 13 3217 24572 29 _ _ (1010939 / 50000) (2021881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603887872 :
    ThetaLowerSegment 603887872 603953408 (30193337686563 / 50000) (30196662681379 / 50000) := by
  exact
    packedTile32768 603887872 603953408 13 3289 24574 29 _ _ (63184 / 3125) (2021891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell603953408 :
    ThetaLowerSegment 603953408 604018944 (30196662681379 / 50000) (2415998530287 / 4000) := by
  exact
    packedTile32768 603953408 604018944 13 3283 24575 29 _ _ (2021899 / 100000) (1010951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604018944 :
    ThetaLowerSegment 604018944 604084480 (2415998530287 / 4000) (2416261782969 / 4000) := by
  exact
    packedTile32768 604018944 604084480 13 3255 24576 29 _ _ (202191 / 10000) (2021913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604084480 :
    ThetaLowerSegment 604084480 604150016 (2416261782969 / 4000) (15103303722901 / 25000) := by
  exact
    packedTile32768 604084480 604150016 13 3299 24578 29 _ _ (2021921 / 100000) (505481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604150016 :
    ThetaLowerSegment 604150016 604215552 (15103303722901 / 25000) (1888117749163 / 3125) := by
  exact
    packedTile32768 604150016 604215552 13 3241 24579 29 _ _ (505483 / 25000) (404387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604215552 :
    ThetaLowerSegment 604215552 604281088 (1888117749163 / 3125) (60426232124987 / 100000) := by
  exact
    packedTile32768 604215552 604281088 13 3197 24580 29 _ _ (2021943 / 100000) (1010973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604281088 :
    ThetaLowerSegment 604281088 604346624 (60426232124987 / 100000) (60432896485371 / 100000) := by
  exact
    packedTile32768 604281088 604346624 13 3296 24582 29 _ _ (1010977 / 50000) (2021957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604346624 :
    ThetaLowerSegment 604346624 604412160 (60432896485371 / 100000) (60439488088011 / 100000) := by
  exact
    packedTile32768 604346624 604412160 13 3260 24583 29 _ _ (505491 / 25000) (2021967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604412160 :
    ThetaLowerSegment 604412160 604477696 (60439488088011 / 100000) (60446067594661 / 100000) := by
  exact
    packedTile32768 604412160 604477696 13 3254 24584 29 _ _ (80879 / 4000) (1010989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604477696 :
    ThetaLowerSegment 604477696 604543232 (60446067594661 / 100000) (60452661291007 / 100000) := by
  exact
    packedTile32768 604477696 604543232 13 3261 24586 29 _ _ (1010993 / 50000) (2021989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604543232 :
    ThetaLowerSegment 604543232 604608768 (60452661291007 / 100000) (1209183401987 / 2000) := by
  exact
    packedTile32768 604543232 604608768 13 3219 24587 29 _ _ (2021997 / 100000) (1011 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604608768 :
    ThetaLowerSegment 604608768 604674304 (1209183401987 / 2000) (1209312810499 / 2000) := by
  exact
    packedTile32768 604608768 604674304 13 3200 24588 29 _ _ (252751 / 12500) (2022011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604674304 :
    ThetaLowerSegment 604674304 604739840 (1209312810499 / 2000) (2418890505487 / 4000) := by
  exact
    packedTile32768 604674304 604739840 13 3275 24590 29 _ _ (2022019 / 100000) (1011011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604739840 :
    ThetaLowerSegment 604739840 604805376 (2418890505487 / 4000) (60478785702729 / 100000) := by
  exact
    packedTile32768 604739840 604805376 13 3226 24591 29 _ _ (2022029 / 100000) (126377 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604805376 :
    ThetaLowerSegment 604805376 604870912 (60478785702729 / 100000) (60485312847849 / 100000) := by
  exact
    packedTile32768 604805376 604870912 13 3228 24592 29 _ _ (50551 / 2500) (2022043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604870912 :
    ThetaLowerSegment 604870912 604936448 (60485312847849 / 100000) (7561474190163 / 12500) := by
  exact
    packedTile32768 604870912 604936448 13 3205 24594 29 _ _ (2022051 / 100000) (1011027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell604936448 :
    ThetaLowerSegment 604936448 605001984 (7561474190163 / 12500) (30249139137069 / 50000) := by
  exact
    packedTile32768 604936448 605001984 13 3207 24595 29 _ _ (1011031 / 50000) (404413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605001984 :
    ThetaLowerSegment 605001984 605067520 (30249139137069 / 50000) (15126176105533 / 25000) := by
  exact
    packedTile32768 605001984 605067520 13 3178 24596 29 _ _ (2022073 / 100000) (505519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605067520 :
    ThetaLowerSegment 605067520 605133056 (15126176105533 / 25000) (7563914326841 / 12500) := by
  exact
    packedTile32768 605067520 605133056 13 3269 24598 29 _ _ (505521 / 25000) (2022087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605133056 :
    ThetaLowerSegment 605133056 605198592 (7563914326841 / 12500) (30258952309537 / 50000) := by
  exact
    packedTile32768 605133056 605198592 13 3259 24599 29 _ _ (1011047 / 50000) (2022097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605198592 :
    ThetaLowerSegment 605198592 605264128 (30258952309537 / 50000) (30262167456487 / 50000) := by
  exact
    packedTile32768 605198592 605264128 13 3180 24600 29 _ _ (404421 / 20000) (505527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605264128 :
    ThetaLowerSegment 605264128 605329664 (30262167456487 / 50000) (30265445306523 / 50000) := by
  exact
    packedTile32768 605264128 605329664 13 3242 24602 29 _ _ (505529 / 25000) (2022119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605329664 :
    ThetaLowerSegment 605329664 605395200 (30265445306523 / 50000) (3026876361693 / 5000) := by
  exact
    packedTile32768 605329664 605395200 13 3282 24603 29 _ _ (2022127 / 100000) (202213 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605395200 :
    ThetaLowerSegment 605395200 605460736 (3026876361693 / 5000) (30272000048799 / 50000) := by
  exact
    packedTile32768 605395200 605460736 13 3201 24604 29 _ _ (1011069 / 50000) (2022141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605460736 :
    ThetaLowerSegment 605460736 605526272 (30272000048799 / 50000) (60550485129441 / 100000) := by
  exact
    packedTile32768 605460736 605526272 13 3207 24606 29 _ _ (2022149 / 100000) (252769 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605526272 :
    ThetaLowerSegment 605526272 605591808 (60550485129441 / 100000) (15139265803167 / 25000) := by
  exact
    packedTile32768 605526272 605591808 13 3253 24607 29 _ _ (2022159 / 100000) (1011081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605591808 :
    ThetaLowerSegment 605591808 605657344 (15139265803167 / 25000) (30281772133759 / 50000) := by
  exact
    packedTile32768 605591808 605657344 13 3205 24608 29 _ _ (202217 / 10000) (2022173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605657344 :
    ThetaLowerSegment 605657344 605722880 (30281772133759 / 50000) (60570098156139 / 100000) := by
  exact
    packedTile32768 605657344 605722880 13 3241 24610 29 _ _ (2022181 / 100000) (252773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605722880 :
    ThetaLowerSegment 605722880 605788416 (60570098156139 / 100000) (60576528726699 / 100000) := by
  exact
    packedTile32768 605722880 605788416 13 3180 24611 29 _ _ (126387 / 6250) (404439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605788416 :
    ThetaLowerSegment 605788416 605853952 (60576528726699 / 100000) (12116604808547 / 20000) := by
  exact
    packedTile32768 605788416 605853952 13 3212 24612 29 _ _ (2022203 / 100000) (1011103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605853952 :
    ThetaLowerSegment 605853952 605919488 (12116604808547 / 20000) (60589612412689 / 100000) := by
  exact
    packedTile32768 605853952 605919488 13 3258 24614 29 _ _ (2022213 / 100000) (252777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605919488 :
    ThetaLowerSegment 605919488 605985024 (60589612412689 / 100000) (60596198796257 / 100000) := by
  exact
    packedTile32768 605919488 605985024 13 3257 24615 29 _ _ (126389 / 6250) (2022227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell605985024 :
    ThetaLowerSegment 605985024 606050560 (60596198796257 / 100000) (60602722526367 / 100000) := by
  exact
    packedTile32768 605985024 606050560 13 3226 24616 29 _ _ (404447 / 20000) (1011119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606050560 :
    ThetaLowerSegment 606050560 606116096 (60602722526367 / 100000) (60609365604477 / 100000) := by
  exact
    packedTile32768 606050560 606116096 13 3285 24618 29 _ _ (1011123 / 50000) (2022249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606116096 :
    ThetaLowerSegment 606116096 606181632 (60609365604477 / 100000) (2424638650053 / 4000) := by
  exact
    packedTile32768 606116096 606181632 13 3264 24619 29 _ _ (2022257 / 100000) (101113 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606181632 :
    ThetaLowerSegment 606181632 606247168 (2424638650053 / 4000) (60622601312633 / 100000) := by
  exact
    packedTile32768 606181632 606247168 13 3281 24620 29 _ _ (505567 / 25000) (2022271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606247168 :
    ThetaLowerSegment 606247168 606312704 (60622601312633 / 100000) (60628920931383 / 100000) := by
  exact
    packedTile32768 606247168 606312704 13 3125 24622 29 _ _ (1011139 / 50000) (2022281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606312704 :
    ThetaLowerSegment 606312704 606378240 (60628920931383 / 100000) (30317707250681 / 50000) := by
  exact
    packedTile32768 606312704 606378240 13 3211 24623 29 _ _ (2022289 / 100000) (505573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606378240 :
    ThetaLowerSegment 606378240 606443776 (30317707250681 / 50000) (30321014722331 / 50000) := by
  exact
    packedTile32768 606378240 606443776 13 3271 24624 29 _ _ (20223 / 1000) (2022303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606443776 :
    ThetaLowerSegment 606443776 606509312 (30321014722331 / 50000) (3790538127791 / 6250) := by
  exact
    packedTile32768 606443776 606509312 13 3254 24626 29 _ _ (2022311 / 100000) (1011157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606509312 :
    ThetaLowerSegment 606509312 606574848 (3790538127791 / 6250) (15163803737077 / 25000) := by
  exact
    packedTile32768 606509312 606574848 13 3266 24627 29 _ _ (1011161 / 50000) (80893 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606574848 :
    ThetaLowerSegment 606574848 606640384 (15163803737077 / 25000) (15165450926491 / 25000) := by
  exact
    packedTile32768 606574848 606640384 13 3258 24628 29 _ _ (505583 / 25000) (404467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606640384 :
    ThetaLowerSegment 606640384 606705920 (15165450926491 / 25000) (60668394521801 / 100000) := by
  exact
    packedTile32768 606640384 606705920 13 3259 24630 29 _ _ (2022343 / 100000) (1011173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606705920 :
    ThetaLowerSegment 606705920 606771456 (60668394521801 / 100000) (60674991440549 / 100000) := by
  exact
    packedTile32768 606705920 606771456 13 3262 24631 29 _ _ (1011177 / 50000) (2022357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606771456 :
    ThetaLowerSegment 606771456 606836992 (60674991440549 / 100000) (30340728470727 / 50000) := by
  exact
    packedTile32768 606771456 606836992 13 3197 24632 29 _ _ (404473 / 20000) (63199 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606836992 :
    ThetaLowerSegment 606836992 606902528 (30340728470727 / 50000) (30344044156179 / 50000) := by
  exact
    packedTile32768 606836992 606902528 13 3279 24634 29 _ _ (252797 / 12500) (2022379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606902528 :
    ThetaLowerSegment 606902528 606968064 (30344044156179 / 50000) (7586816201471 / 12500) := by
  exact
    packedTile32768 606902528 606968064 13 3185 24635 29 _ _ (1011193 / 50000) (2022389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell606968064 :
    ThetaLowerSegment 606968064 607033600 (7586816201471 / 12500) (3793815613731 / 6250) := by
  exact
    packedTile32768 606968064 607033600 13 3224 24636 29 _ _ (2022397 / 100000) (2528 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607033600 :
    ThetaLowerSegment 607033600 607099136 (3793815613731 / 6250) (7588457128329 / 12500) := by
  exact
    packedTile32768 607033600 607099136 13 3267 24638 29 _ _ (252801 / 12500) (2022411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607099136 :
    ThetaLowerSegment 607099136 607164672 (7588457128329 / 12500) (30357090675163 / 50000) := by
  exact
    packedTile32768 607099136 607164672 13 3226 24639 29 _ _ (2022419 / 100000) (1011211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607164672 :
    ThetaLowerSegment 607164672 607230208 (30357090675163 / 50000) (30360381168773 / 50000) := by
  exact
    packedTile32768 607164672 607230208 13 3254 24640 29 _ _ (202243 / 10000) (2022433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607230208 :
    ThetaLowerSegment 607230208 607295744 (30360381168773 / 50000) (30363645386933 / 50000) := by
  exact
    packedTile32768 607230208 607295744 13 3228 24642 29 _ _ (50561 / 2500) (2022443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607295744 :
    ThetaLowerSegment 607295744 607361280 (30363645386933 / 50000) (6073385160491 / 10000) := by
  exact
    packedTile32768 607295744 607361280 13 3244 24643 29 _ _ (2022451 / 100000) (1011227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607361280 :
    ThetaLowerSegment 607361280 607426816 (6073385160491 / 10000) (30370220393053 / 50000) := by
  exact
    packedTile32768 607361280 607426816 13 3258 24644 29 _ _ (1011231 / 50000) (404493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607426816 :
    ThetaLowerSegment 607426816 607492352 (30370220393053 / 50000) (759337369421 / 1250) := by
  exact
    packedTile32768 607426816 607492352 13 3238 24646 29 _ _ (2022473 / 100000) (505619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607492352 :
    ThetaLowerSegment 607492352 607557888 (759337369421 / 1250) (15188374982419 / 25000) := by
  exact
    packedTile32768 607492352 607557888 13 3219 24647 29 _ _ (505621 / 25000) (2022487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607557888 :
    ThetaLowerSegment 607557888 607623424 (15188374982419 / 25000) (30380025393871 / 50000) := by
  exact
    packedTile32768 607557888 607623424 13 3239 24648 29 _ _ (1011247 / 50000) (2022497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607623424 :
    ThetaLowerSegment 607623424 607688960 (30380025393871 / 50000) (30383305896981 / 50000) := by
  exact
    packedTile32768 607623424 607688960 13 3244 24650 29 _ _ (404501 / 20000) (505627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607688960 :
    ThetaLowerSegment 607688960 607754496 (30383305896981 / 50000) (30386567204031 / 50000) := by
  exact
    packedTile32768 607688960 607754496 13 3225 24651 29 _ _ (505629 / 25000) (2022519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607754496 :
    ThetaLowerSegment 607754496 607820032 (30386567204031 / 50000) (7597468508919 / 12500) := by
  exact
    packedTile32768 607754496 607820032 13 3270 24652 29 _ _ (2022527 / 100000) (202253 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607820032 :
    ThetaLowerSegment 607820032 607885568 (7597468508919 / 12500) (60786169626327 / 100000) := by
  exact
    packedTile32768 607820032 607885568 13 3175 24654 29 _ _ (2022537 / 100000) (101127 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607885568 :
    ThetaLowerSegment 607885568 607951104 (60786169626327 / 100000) (60792821786699 / 100000) := by
  exact
    packedTile32768 607885568 607951104 13 3289 24655 29 _ _ (505637 / 25000) (2022551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell607951104 :
    ThetaLowerSegment 607951104 608016640 (60792821786699 / 100000) (60799407238803 / 100000) := by
  exact
    packedTile32768 607951104 608016640 13 3256 24656 29 _ _ (2022559 / 100000) (1011281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608016640 :
    ThetaLowerSegment 608016640 608082176 (60799407238803 / 100000) (60806031155553 / 100000) := by
  exact
    packedTile32768 608016640 608082176 13 3275 24657 29 _ _ (202257 / 10000) (2022573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608082176 :
    ThetaLowerSegment 608082176 608147712 (60806031155553 / 100000) (12162529808117 / 20000) := by
  exact
    packedTile32768 608082176 608147712 13 3272 24659 29 _ _ (2022581 / 100000) (252823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608147712 :
    ThetaLowerSegment 608147712 608213248 (12162529808117 / 20000) (60819093015511 / 100000) := by
  exact
    packedTile32768 608147712 608213248 13 3186 24660 29 _ _ (2022591 / 100000) (1011297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608213248 :
    ThetaLowerSegment 608213248 608278784 (60819093015511 / 100000) (60825733217877 / 100000) := by
  exact
    packedTile32768 608213248 608278784 13 3283 24661 29 _ _ (1011301 / 50000) (404521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608278784 :
    ThetaLowerSegment 608278784 608344320 (60825733217877 / 100000) (60832294574449 / 100000) := by
  exact
    packedTile32768 608278784 608344320 13 3244 24663 29 _ _ (2022613 / 100000) (252827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608344320 :
    ThetaLowerSegment 608344320 608409856 (60832294574449 / 100000) (60838884283441 / 100000) := by
  exact
    packedTile32768 608344320 608409856 13 3258 24664 29 _ _ (63207 / 3125) (2022627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608409856 :
    ThetaLowerSegment 608409856 608475392 (60838884283441 / 100000) (60845476047647 / 100000) := by
  exact
    packedTile32768 608409856 608475392 13 3259 24665 29 _ _ (1011317 / 50000) (2022637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608475392 :
    ThetaLowerSegment 608475392 608540928 (60845476047647 / 100000) (60851948511647 / 100000) := by
  exact
    packedTile32768 608475392 608540928 13 3200 24667 29 _ _ (404529 / 20000) (252831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608540928 :
    ThetaLowerSegment 608540928 608606464 (60851948511647 / 100000) (60858483713183 / 100000) := by
  exact
    packedTile32768 608540928 608606464 13 3231 24668 29 _ _ (63208 / 3125) (2022659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608606464 :
    ThetaLowerSegment 608606464 608672000 (60858483713183 / 100000) (60864931975579 / 100000) := by
  exact
    packedTile32768 608606464 608672000 13 3188 24669 29 _ _ (2022667 / 100000) (202267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608672000 :
    ThetaLowerSegment 608672000 608737536 (60864931975579 / 100000) (12174310035599 / 20000) := by
  exact
    packedTile32768 608672000 608737536 13 3272 24671 29 _ _ (1011339 / 50000) (2022681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608737536 :
    ThetaLowerSegment 608737536 608803072 (12174310035599 / 20000) (60877994461963 / 100000) := by
  exact
    packedTile32768 608737536 608803072 13 3186 24672 29 _ _ (63209 / 3125) (2022691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608803072 :
    ThetaLowerSegment 608803072 608868608 (60877994461963 / 100000) (60884628914683 / 100000) := by
  exact
    packedTile32768 608803072 608868608 13 3280 24673 29 _ _ (2022699 / 100000) (1011351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608868608 :
    ThetaLowerSegment 608868608 608934144 (60884628914683 / 100000) (60891115745653 / 100000) := by
  exact
    packedTile32768 608868608 608934144 13 3207 24675 29 _ _ (202271 / 10000) (2022713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608934144 :
    ThetaLowerSegment 608934144 608999680 (60891115745653 / 100000) (1903050334462 / 3125) := by
  exact
    packedTile32768 608934144 608999680 13 3211 24676 29 _ _ (2022721 / 100000) (505681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell608999680 :
    ThetaLowerSegment 608999680 609065216 (1903050334462 / 3125) (60904121873873 / 100000) := by
  exact
    packedTile32768 608999680 609065216 13 3219 24677 29 _ _ (2022731 / 100000) (1011367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609065216 :
    ThetaLowerSegment 609065216 609130752 (60904121873873 / 100000) (60910592625531 / 100000) := by
  exact
    packedTile32768 609065216 609130752 13 3199 24679 29 _ _ (1011371 / 50000) (404549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609130752 :
    ThetaLowerSegment 609130752 609196288 (60910592625531 / 100000) (60917146345251 / 100000) := by
  exact
    packedTile32768 609130752 609196288 13 3240 24680 29 _ _ (2022753 / 100000) (505689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609196288 :
    ThetaLowerSegment 609196288 609261824 (60917146345251 / 100000) (60923720328251 / 100000) := by
  exact
    packedTile32768 609196288 609261824 13 3250 24681 29 _ _ (505691 / 25000) (2022767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609261824 :
    ThetaLowerSegment 609261824 609327360 (60923720328251 / 100000) (60930203318921 / 100000) := by
  exact
    packedTile32768 609261824 609327360 13 3205 24683 29 _ _ (1011387 / 50000) (2022777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609327360 :
    ThetaLowerSegment 609327360 609392896 (60930203318921 / 100000) (60936765233461 / 100000) := by
  exact
    packedTile32768 609327360 609392896 13 3244 24684 29 _ _ (404557 / 20000) (505697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609392896 :
    ThetaLowerSegment 609392896 609458432 (60936765233461 / 100000) (60943422255097 / 100000) := by
  exact
    packedTile32768 609392896 609458432 13 3291 24685 29 _ _ (505699 / 25000) (2022799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609458432 :
    ThetaLowerSegment 609458432 609523968 (60943422255097 / 100000) (60949895237497 / 100000) := by
  exact
    packedTile32768 609458432 609523968 13 3200 24687 29 _ _ (2022807 / 100000) (202281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609523968 :
    ThetaLowerSegment 609523968 609589504 (60949895237497 / 100000) (6095654828261 / 10000) := by
  exact
    packedTile32768 609523968 609589504 13 3289 24688 29 _ _ (2022817 / 100000) (101141 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609589504 :
    ThetaLowerSegment 609589504 609655040 (6095654828261 / 10000) (30481509654691 / 50000) := by
  exact
    packedTile32768 609589504 609655040 13 3199 24689 29 _ _ (505707 / 25000) (2022831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609655040 :
    ThetaLowerSegment 609655040 609720576 (30481509654691 / 50000) (3810594033201 / 6250) := by
  exact
    packedTile32768 609655040 609720576 13 3206 24691 29 _ _ (2022839 / 100000) (1011421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609720576 :
    ThetaLowerSegment 609720576 609786112 (3810594033201 / 6250) (15244048018329 / 25000) := by
  exact
    packedTile32768 609720576 609786112 13 3306 24692 29 _ _ (40457 / 2000) (2022853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609786112 :
    ThetaLowerSegment 609786112 609851648 (15244048018329 / 25000) (7622846048897 / 12500) := by
  exact
    packedTile32768 609786112 609851648 13 3251 24693 29 _ _ (101143 / 5000) (2022863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609851648 :
    ThetaLowerSegment 609851648 609917184 (7622846048897 / 12500) (60989324516087 / 100000) := by
  exact
    packedTile32768 609851648 609917184 13 3241 24695 29 _ _ (2022871 / 100000) (1011437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609917184 :
    ThetaLowerSegment 609917184 609982720 (60989324516087 / 100000) (60995809875779 / 100000) := by
  exact
    packedTile32768 609917184 609982720 13 3206 24696 29 _ _ (1011441 / 50000) (404577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell609982720 :
    ThetaLowerSegment 609982720 610048256 (60995809875779 / 100000) (3812650913839 / 6250) := by
  exact
    packedTile32768 609982720 610048256 13 3265 24697 29 _ _ (2022893 / 100000) (126431 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610048256 :
    ThetaLowerSegment 610048256 610113792 (3812650913839 / 6250) (61008995124883 / 100000) := by
  exact
    packedTile32768 610048256 610113792 13 3253 24699 29 _ _ (2022903 / 100000) (1011453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610113792 :
    ThetaLowerSegment 610113792 610179328 (61008995124883 / 100000) (61015456312199 / 100000) := by
  exact
    packedTile32768 610113792 610179328 13 3194 24700 29 _ _ (1011457 / 50000) (2022917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610179328 :
    ThetaLowerSegment 610179328 610244864 (61015456312199 / 100000) (1906939158457 / 3125) := by
  exact
    packedTile32768 610179328 610244864 13 3261 24701 29 _ _ (80917 / 4000) (126433 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610244864 :
    ThetaLowerSegment 610244864 610310400 (1906939158457 / 3125) (3814290237257 / 6250) := by
  exact
    packedTile32768 610244864 610310400 13 3258 24703 29 _ _ (252867 / 12500) (2022939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610310400 :
    ThetaLowerSegment 610310400 610375936 (3814290237257 / 6250) (15258814707383 / 25000) := by
  exact
    packedTile32768 610310400 610375936 13 3270 24704 29 _ _ (1011473 / 50000) (2022949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610375936 :
    ThetaLowerSegment 610375936 610441472 (15258814707383 / 25000) (61041863784137 / 100000) := by
  exact
    packedTile32768 610375936 610441472 13 3265 24705 29 _ _ (2022957 / 100000) (25287 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610441472 :
    ThetaLowerSegment 610441472 610507008 (61041863784137 / 100000) (61048482935433 / 100000) := by
  exact
    packedTile32768 610441472 610507008 13 3272 24707 29 _ _ (252871 / 12500) (2022971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610507008 :
    ThetaLowerSegment 610507008 610572544 (61048482935433 / 100000) (61055017157603 / 100000) := by
  exact
    packedTile32768 610507008 610572544 13 3230 24708 29 _ _ (2022979 / 100000) (1011491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610572544 :
    ThetaLowerSegment 610572544 610638080 (61055017157603 / 100000) (30530764579597 / 50000) := by
  exact
    packedTile32768 610572544 610638080 13 3219 24709 29 _ _ (2022989 / 100000) (126437 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610638080 :
    ThetaLowerSegment 610638080 610703616 (30530764579597 / 50000) (30534046897097 / 50000) := by
  exact
    packedTile32768 610638080 610703616 13 3245 24711 29 _ _ (2023 / 100) (2023003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610703616 :
    ThetaLowerSegment 610703616 610769152 (30534046897097 / 50000) (3053724932351 / 5000) := by
  exact
    packedTile32768 610703616 610769152 13 3166 24712 29 _ _ (2023011 / 100000) (1011507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610769152 :
    ThetaLowerSegment 610769152 610834688 (3053724932351 / 5000) (61081119994753 / 100000) := by
  exact
    packedTile32768 610769152 610834688 13 3273 24713 29 _ _ (2023021 / 100000) (126439 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610834688 :
    ThetaLowerSegment 610834688 610900224 (61081119994753 / 100000) (61087528960129 / 100000) := by
  exact
    packedTile32768 610834688 610900224 13 3168 24715 29 _ _ (252879 / 12500) (404607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610900224 :
    ThetaLowerSegment 610900224 610965760 (61087528960129 / 100000) (6109417870247 / 10000) := by
  exact
    packedTile32768 610900224 610965760 13 3287 24716 29 _ _ (2023043 / 100000) (1011523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell610965760 :
    ThetaLowerSegment 610965760 611031296 (6109417870247 / 10000) (7637579283473 / 12500) := by
  exact
    packedTile32768 610965760 611031296 13 3191 24717 29 _ _ (1011527 / 50000) (2023057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611031296 :
    ThetaLowerSegment 611031296 611096832 (7637579283473 / 12500) (7638404187819 / 12500) := by
  exact
    packedTile32768 611031296 611096832 13 3262 24719 29 _ _ (252883 / 12500) (2023067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611096832 :
    ThetaLowerSegment 611096832 611162368 (7638404187819 / 12500) (30556928525051 / 50000) := by
  exact
    packedTile32768 611096832 611162368 13 3274 24720 29 _ _ (80923 / 4000) (1011539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611162368 :
    ThetaLowerSegment 611162368 611227904 (30556928525051 / 50000) (1910007496451 / 3125) := by
  exact
    packedTile32768 611162368 611227904 13 3155 24721 29 _ _ (1011543 / 50000) (2023089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611227904 :
    ThetaLowerSegment 611227904 611293440 (1910007496451 / 3125) (12225342354747 / 20000) := by
  exact
    packedTile32768 611227904 611293440 13 3199 24723 29 _ _ (2023097 / 100000) (20231 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611293440 :
    ThetaLowerSegment 611293440 611358976 (12225342354747 / 20000) (61133234270703 / 100000) := by
  exact
    packedTile32768 611293440 611358976 13 3224 24724 29 _ _ (2023107 / 100000) (202311 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611358976 :
    ThetaLowerSegment 611358976 611424512 (61133234270703 / 100000) (61139845820327 / 100000) := by
  exact
    packedTile32768 611358976 611424512 13 3268 24725 29 _ _ (1011559 / 50000) (2023121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611424512 :
    ThetaLowerSegment 611424512 611490048 (61139845820327 / 100000) (30573219598869 / 50000) := by
  exact
    packedTile32768 611424512 611490048 13 3259 24726 29 _ _ (2023129 / 100000) (505783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611490048 :
    ThetaLowerSegment 611490048 611555584 (30573219598869 / 50000) (30576553731941 / 50000) := by
  exact
    packedTile32768 611490048 611555584 13 3296 24728 29 _ _ (2023139 / 100000) (1011571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611555584 :
    ThetaLowerSegment 611555584 611621120 (30576553731941 / 50000) (30579806957141 / 50000) := by
  exact
    packedTile32768 611555584 611621120 13 3216 24729 29 _ _ (40463 / 2000) (2023153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611621120 :
    ThetaLowerSegment 611621120 611686656 (30579806957141 / 50000) (12233214773471 / 20000) := by
  exact
    packedTile32768 611621120 611686656 13 3193 24730 29 _ _ (2023161 / 100000) (505791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611686656 :
    ThetaLowerSegment 611686656 611752192 (12233214773471 / 20000) (61172584434851 / 100000) := by
  exact
    packedTile32768 611686656 611752192 13 3218 24732 29 _ _ (505793 / 25000) (80927 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611752192 :
    ThetaLowerSegment 611752192 611817728 (61172584434851 / 100000) (61179145614077 / 100000) := by
  exact
    packedTile32768 611752192 611817728 13 3243 24733 29 _ _ (1011591 / 50000) (404637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611817728 :
    ThetaLowerSegment 611817728 611883264 (61179145614077 / 100000) (1912052326809 / 3125) := by
  exact
    packedTile32768 611817728 611883264 13 3227 24734 29 _ _ (2023193 / 100000) (505799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611883264 :
    ThetaLowerSegment 611883264 611948800 (1912052326809 / 3125) (15298059938717 / 25000) := by
  exact
    packedTile32768 611883264 611948800 13 3245 24736 29 _ _ (505801 / 25000) (2023207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell611948800 :
    ThetaLowerSegment 611948800 612014336 (15298059938717 / 25000) (30599388379651 / 50000) := by
  exact
    packedTile32768 611948800 612014336 13 3231 24737 29 _ _ (1011607 / 50000) (2023217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612014336 :
    ThetaLowerSegment 612014336 612079872 (30599388379651 / 50000) (3825331480197 / 6250) := by
  exact
    packedTile32768 612014336 612079872 13 3226 24738 29 _ _ (80929 / 4000) (505807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612079872 :
    ThetaLowerSegment 612079872 612145408 (3825331480197 / 6250) (7651482876783 / 12500) := by
  exact
    packedTile32768 612079872 612145408 13 3242 24740 29 _ _ (505809 / 25000) (2023239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612145408 :
    ThetaLowerSegment 612145408 612210944 (7651482876783 / 12500) (61218529613129 / 100000) := by
  exact
    packedTile32768 612145408 612210944 13 3295 24741 29 _ _ (2023247 / 100000) (8093 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612210944 :
    ThetaLowerSegment 612210944 612276480 (61218529613129 / 100000) (15306284898437 / 25000) := by
  exact
    packedTile32768 612210944 612276480 13 3267 24742 29 _ _ (2023257 / 100000) (101163 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612276480 :
    ThetaLowerSegment 612276480 612342016 (15306284898437 / 25000) (15307959152707 / 25000) := by
  exact
    packedTile32768 612276480 612342016 13 3310 24744 29 _ _ (505817 / 25000) (2023271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612342016 :
    ThetaLowerSegment 612342016 612407552 (15307959152707 / 25000) (61238385964951 / 100000) := by
  exact
    packedTile32768 612342016 612407552 13 3237 24745 29 _ _ (2023279 / 100000) (1011641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612407552 :
    ThetaLowerSegment 612407552 612473088 (61238385964951 / 100000) (30622498025057 / 50000) := by
  exact
    packedTile32768 612407552 612473088 13 3267 24746 29 _ _ (2023289 / 100000) (505823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612473088 :
    ThetaLowerSegment 612473088 612538624 (30622498025057 / 50000) (30625802073957 / 50000) := by
  exact
    packedTile32768 612473088 612538624 13 3266 24748 29 _ _ (20233 / 1000) (2023303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612538624 :
    ThetaLowerSegment 612538624 612604160 (30625802073957 / 50000) (15314518674123 / 25000) := by
  exact
    packedTile32768 612538624 612604160 13 3198 24749 29 _ _ (2023311 / 100000) (1011657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612604160 :
    ThetaLowerSegment 612604160 612669696 (15314518674123 / 25000) (61264692979483 / 100000) := by
  exact
    packedTile32768 612604160 612669696 13 3271 24750 29 _ _ (2023321 / 100000) (505831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612669696 :
    ThetaLowerSegment 612669696 612735232 (61264692979483 / 100000) (61271123128579 / 100000) := by
  exact
    packedTile32768 612669696 612735232 13 3178 24752 29 _ _ (505833 / 25000) (404667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612735232 :
    ThetaLowerSegment 612735232 612800768 (61271123128579 / 100000) (30638812064819 / 50000) := by
  exact
    packedTile32768 612735232 612800768 13 3213 24753 29 _ _ (2023343 / 100000) (1011673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612800768 :
    ThetaLowerSegment 612800768 612866304 (30638812064819 / 50000) (15321044443311 / 25000) := by
  exact
    packedTile32768 612800768 612866304 13 3239 24754 29 _ _ (1011677 / 50000) (2023357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612866304 :
    ThetaLowerSegment 612866304 612931840 (15321044443311 / 25000) (7661355594703 / 12500) := by
  exact
    packedTile32768 612866304 612931840 13 3295 24756 29 _ _ (505841 / 25000) (2023367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612931840 :
    ThetaLowerSegment 612931840 612997376 (7661355594703 / 12500) (3831095624289 / 6250) := by
  exact
    packedTile32768 612931840 612997376 13 3304 24757 29 _ _ (16187 / 800) (1011689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell612997376 :
    ThetaLowerSegment 612997376 613062912 (3831095624289 / 6250) (30652007470377 / 50000) := by
  exact
    packedTile32768 612997376 613062912 13 3205 24758 29 _ _ (1011693 / 50000) (2023389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613062912 :
    ThetaLowerSegment 613062912 613128448 (30652007470377 / 50000) (30655356190757 / 50000) := by
  exact
    packedTile32768 613062912 613128448 13 3310 24760 29 _ _ (505849 / 25000) (2023399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613128448 :
    ThetaLowerSegment 613128448 613193984 (30655356190757 / 50000) (3065863208669 / 5000) := by
  exact
    packedTile32768 613128448 613193984 13 3238 24761 29 _ _ (2023407 / 100000) (202341 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613193984 :
    ThetaLowerSegment 613193984 613259520 (3065863208669 / 5000) (6132395156987 / 10000) := by
  exact
    packedTile32768 613193984 613259520 13 3305 24762 29 _ _ (1011709 / 50000) (2023421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613259520 :
    ThetaLowerSegment 613259520 613325056 (6132395156987 / 10000) (30665224398589 / 50000) := by
  exact
    packedTile32768 613259520 613325056 13 3211 24764 29 _ _ (505857 / 25000) (2023431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613325056 :
    ThetaLowerSegment 613325056 613390592 (30665224398589 / 50000) (30668494276013 / 50000) := by
  exact
    packedTile32768 613325056 613390592 13 3232 24765 29 _ _ (2023439 / 100000) (1011721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613390592 :
    ThetaLowerSegment 613390592 613456128 (30668494276013 / 50000) (30671770241563 / 50000) := by
  exact
    packedTile32768 613390592 613456128 13 3238 24766 29 _ _ (40469 / 2000) (2023453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613456128 :
    ThetaLowerSegment 613456128 613521664 (30671770241563 / 50000) (30675048246763 / 50000) := by
  exact
    packedTile32768 613456128 613521664 13 3240 24768 29 _ _ (101173 / 5000) (2023463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613521664 :
    ThetaLowerSegment 613521664 613587200 (30675048246763 / 50000) (15339147958859 / 25000) := by
  exact
    packedTile32768 613521664 613587200 13 3210 24769 29 _ _ (2023471 / 100000) (1011737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613587200 :
    ThetaLowerSegment 613587200 613652736 (15339147958859 / 25000) (6136300020293 / 10000) := by
  exact
    packedTile32768 613587200 613652736 13 3167 24770 29 _ _ (1011741 / 50000) (404697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613652736 :
    ThetaLowerSegment 613652736 613718272 (6136300020293 / 10000) (30684802440409 / 50000) := by
  exact
    packedTile32768 613652736 613718272 13 3264 24772 29 _ _ (505873 / 25000) (404699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613718272 :
    ThetaLowerSegment 613718272 613783808 (30684802440409 / 50000) (61376167101047 / 100000) := by
  exact
    packedTile32768 613718272 613783808 13 3243 24773 29 _ _ (2023503 / 100000) (1011753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613783808 :
    ThetaLowerSegment 613783808 613849344 (61376167101047 / 100000) (61382680792613 / 100000) := by
  exact
    packedTile32768 613783808 613849344 13 3219 24774 29 _ _ (1011757 / 50000) (2023517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613849344 :
    ThetaLowerSegment 613849344 613914880 (61382680792613 / 100000) (61389285578213 / 100000) := by
  exact
    packedTile32768 613849344 613914880 13 3264 24775 29 _ _ (80941 / 4000) (252941 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613914880 :
    ThetaLowerSegment 613914880 613980416 (61389285578213 / 100000) (30697855150919 / 50000) := by
  exact
    packedTile32768 613914880 613980416 13 3175 24777 29 _ _ (404707 / 20000) (1011769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell613980416 :
    ThetaLowerSegment 613980416 614045952 (30697855150919 / 50000) (15350562094741 / 25000) := by
  exact
    packedTile32768 613980416 614045952 13 3231 24778 29 _ _ (1011773 / 50000) (2023549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614045952 :
    ThetaLowerSegment 614045952 614111488 (15350562094741 / 25000) (15352193081683 / 25000) := by
  exact
    packedTile32768 614045952 614111488 13 3224 24779 29 _ _ (2023557 / 100000) (50589 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614111488 :
    ThetaLowerSegment 614111488 614177024 (15352193081683 / 25000) (15353848359489 / 25000) := by
  exact
    packedTile32768 614111488 614177024 13 3272 24781 29 _ _ (2023567 / 100000) (202357 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614177024 :
    ThetaLowerSegment 614177024 614242560 (15353848359489 / 25000) (6142193566563 / 10000) := by
  exact
    packedTile32768 614177024 614242560 13 3233 24782 29 _ _ (1011789 / 50000) (2023581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614242560 :
    ThetaLowerSegment 614242560 614308096 (6142193566563 / 10000) (1919641516206 / 3125) := by
  exact
    packedTile32768 614242560 614308096 13 3258 24783 29 _ _ (2023589 / 100000) (252949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614308096 :
    ThetaLowerSegment 614308096 614373632 (1919641516206 / 3125) (61435030342179 / 100000) := by
  exact
    packedTile32768 614308096 614373632 13 3213 24785 29 _ _ (2023599 / 100000) (1011801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614373632 :
    ThetaLowerSegment 614373632 614439168 (61435030342179 / 100000) (61441485658079 / 100000) := by
  exact
    packedTile32768 614373632 614439168 13 3190 24786 29 _ _ (202361 / 10000) (2023613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614439168 :
    ThetaLowerSegment 614439168 614504704 (61441485658079 / 100000) (61448038142877 / 100000) := by
  exact
    packedTile32768 614439168 614504704 13 3238 24787 29 _ _ (2023621 / 100000) (252953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614504704 :
    ThetaLowerSegment 614504704 614570240 (61448038142877 / 100000) (15363628946427 / 25000) := by
  exact
    packedTile32768 614504704 614570240 13 3201 24789 29 _ _ (2023631 / 100000) (1011817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614570240 :
    ThetaLowerSegment 614570240 614635776 (15363628946427 / 25000) (15365264049163 / 25000) := by
  exact
    packedTile32768 614570240 614635776 13 3232 24790 29 _ _ (1011821 / 50000) (404729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614635776 :
    ThetaLowerSegment 614635776 614701312 (15365264049163 / 25000) (2458704594241 / 4000) := by
  exact
    packedTile32768 614635776 614701312 13 3241 24791 29 _ _ (2023653 / 100000) (252957 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614701312 :
    ThetaLowerSegment 614701312 614766848 (2458704594241 / 4000) (15368577789223 / 25000) := by
  exact
    packedTile32768 614701312 614766848 13 3309 24793 29 _ _ (2023663 / 100000) (1011833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614766848 :
    ThetaLowerSegment 614766848 614832384 (15368577789223 / 25000) (30740457202577 / 50000) := by
  exact
    packedTile32768 614766848 614832384 13 3263 24794 29 _ _ (1011837 / 50000) (2023677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614832384 :
    ThetaLowerSegment 614832384 614897920 (30740457202577 / 50000) (30743771998607 / 50000) := by
  exact
    packedTile32768 614832384 614897920 13 3276 24795 29 _ _ (404737 / 20000) (252961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614897920 :
    ThetaLowerSegment 614897920 614963456 (30743771998607 / 50000) (61494135171829 / 100000) := by
  exact
    packedTile32768 614897920 614963456 13 3257 24797 29 _ _ (404739 / 20000) (1011849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell614963456 :
    ThetaLowerSegment 614963456 615028992 (61494135171829 / 100000) (12300140824301 / 20000) := by
  exact
    packedTile32768 614963456 615028992 13 3246 24798 29 _ _ (1011853 / 50000) (2023709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615028992 :
    ThetaLowerSegment 615028992 615094528 (12300140824301 / 20000) (2460290843197 / 4000) := by
  exact
    packedTile32768 615028992 615094528 13 3245 24799 29 _ _ (505929 / 25000) (2023719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615094528 :
    ThetaLowerSegment 615094528 615160064 (2460290843197 / 4000) (7689241901617 / 12500) := by
  exact
    packedTile32768 615094528 615160064 13 3293 24801 29 _ _ (2023727 / 100000) (202373 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615160064 :
    ThetaLowerSegment 615160064 615225600 (7689241901617 / 12500) (1538012707849 / 2500) := by
  exact
    packedTile32768 615160064 615225600 13 3248 24802 29 _ _ (1011869 / 50000) (2023741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615225600 :
    ThetaLowerSegment 615225600 615291136 (1538012707849 / 2500) (15381731404717 / 25000) := by
  exact
    packedTile32768 615225600 615291136 13 3171 24803 29 _ _ (505937 / 25000) (2023751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615291136 :
    ThetaLowerSegment 615291136 615356672 (15381731404717 / 25000) (1538336457823 / 2500) := by
  exact
    packedTile32768 615291136 615356672 13 3228 24805 29 _ _ (2023759 / 100000) (1011881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615356672 :
    ThetaLowerSegment 615356672 615422208 (1538336457823 / 2500) (6153998092363 / 10000) := by
  exact
    packedTile32768 615356672 615422208 13 3223 24806 29 _ _ (202377 / 10000) (2023773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615422208 :
    ThetaLowerSegment 615422208 615487744 (6153998092363 / 10000) (6154659463667 / 10000) := by
  exact
    packedTile32768 615422208 615487744 13 3268 24807 29 _ _ (101189 / 5000) (2023783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615487744 :
    ThetaLowerSegment 615487744 615553280 (6154659463667 / 10000) (12310624272529 / 20000) := by
  exact
    packedTile32768 615487744 615553280 13 3225 24809 29 _ _ (2023791 / 100000) (1011897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615553280 :
    ThetaLowerSegment 615553280 615618816 (12310624272529 / 20000) (61559846456691 / 100000) := by
  exact
    packedTile32768 615553280 615618816 13 3323 24810 29 _ _ (1011901 / 50000) (404761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615618816 :
    ThetaLowerSegment 615618816 615684352 (61559846456691 / 100000) (61566249797859 / 100000) := by
  exact
    packedTile32768 615618816 615684352 13 3164 24811 29 _ _ (505953 / 25000) (404763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615684352 :
    ThetaLowerSegment 615684352 615749888 (61566249797859 / 100000) (30786449028207 / 50000) := by
  exact
    packedTile32768 615684352 615749888 13 3285 24812 29 _ _ (2023823 / 100000) (1011913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615749888 :
    ThetaLowerSegment 615749888 615815424 (30786449028207 / 50000) (30789703353279 / 50000) := by
  exact
    packedTile32768 615749888 615815424 13 3216 24814 29 _ _ (1011917 / 50000) (2023837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615815424 :
    ThetaLowerSegment 615815424 615880960 (30789703353279 / 50000) (30792962754041 / 50000) := by
  exact
    packedTile32768 615815424 615880960 13 3221 24815 29 _ _ (505961 / 25000) (2023847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615880960 :
    ThetaLowerSegment 615880960 615946496 (30792962754041 / 50000) (61592533394657 / 100000) := by
  exact
    packedTile32768 615880960 615946496 13 3265 24816 29 _ _ (404771 / 20000) (1011929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell615946496 :
    ThetaLowerSegment 615946496 616012032 (61592533394657 / 100000) (61599023932919 / 100000) := by
  exact
    packedTile32768 615946496 616012032 13 3207 24818 29 _ _ (1011933 / 50000) (2023869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616012032 :
    ThetaLowerSegment 616012032 616077568 (61599023932919 / 100000) (61605433548211 / 100000) := by
  exact
    packedTile32768 616012032 616077568 13 3167 24819 29 _ _ (505969 / 25000) (2023879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616077568 :
    ThetaLowerSegment 616077568 616143104 (61605433548211 / 100000) (7701487483397 / 12500) := by
  exact
    packedTile32768 616077568 616143104 13 3195 24820 29 _ _ (2023887 / 100000) (202389 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616143104 :
    ThetaLowerSegment 616143104 616208640 (7701487483397 / 12500) (61618447173971 / 100000) := by
  exact
    packedTile32768 616143104 616208640 13 3235 24822 29 _ _ (2023897 / 100000) (20239 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616208640 :
    ThetaLowerSegment 616208640 616274176 (61618447173971 / 100000) (61625124046463 / 100000) := by
  exact
    packedTile32768 616208640 616274176 13 3299 24823 29 _ _ (505977 / 25000) (2023911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616274176 :
    ThetaLowerSegment 616274176 616339712 (61625124046463 / 100000) (15407909760431 / 25000) := by
  exact
    packedTile32768 616274176 616339712 13 3219 24824 29 _ _ (2023919 / 100000) (1011961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616339712 :
    ThetaLowerSegment 616339712 616405248 (15407909760431 / 25000) (61638145973459 / 100000) := by
  exact
    packedTile32768 616339712 616405248 13 3215 24826 29 _ _ (2023929 / 100000) (505983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616405248 :
    ThetaLowerSegment 616405248 616470784 (61638145973459 / 100000) (61644790568479 / 100000) := by
  exact
    packedTile32768 616405248 616470784 13 3283 24827 29 _ _ (101197 / 5000) (2023943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616470784 :
    ThetaLowerSegment 616470784 616536320 (61644790568479 / 100000) (30825671048933 / 50000) := by
  exact
    packedTile32768 616470784 616536320 13 3237 24828 29 _ _ (2023951 / 100000) (1011977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616536320 :
    ThetaLowerSegment 616536320 616601856 (30825671048933 / 50000) (61657954378453 / 100000) := by
  exact
    packedTile32768 616536320 616601856 13 3267 24830 29 _ _ (2023961 / 100000) (505991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616601856 :
    ThetaLowerSegment 616601856 616667392 (61657954378453 / 100000) (493315869697 / 800) := by
  exact
    packedTile32768 616601856 616667392 13 3226 24831 29 _ _ (505993 / 25000) (80959 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616667392 :
    ThetaLowerSegment 616667392 616732928 (493315869697 / 800) (12334196139511 / 20000) := by
  exact
    packedTile32768 616667392 616732928 13 3210 24832 29 _ _ (2023983 / 100000) (1011993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616732928 :
    ThetaLowerSegment 616732928 616798464 (12334196139511 / 20000) (6167752831491 / 10000) := by
  exact
    packedTile32768 616732928 616798464 13 3235 24834 29 _ _ (2023993 / 100000) (505999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616798464 :
    ThetaLowerSegment 616798464 616864000 (6167752831491 / 10000) (6168399500769 / 10000) := by
  exact
    packedTile32768 616798464 616864000 13 3195 24835 29 _ _ (506001 / 25000) (2024007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616864000 :
    ThetaLowerSegment 616864000 616929536 (6168399500769 / 10000) (15422647817329 / 25000) := by
  exact
    packedTile32768 616864000 616929536 13 3259 24836 29 _ _ (1012007 / 50000) (2024017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616929536 :
    ThetaLowerSegment 616929536 616995072 (15422647817329 / 25000) (7712134530677 / 12500) := by
  exact
    packedTile32768 616929536 616995072 13 3204 24838 29 _ _ (80961 / 4000) (506007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell616995072 :
    ThetaLowerSegment 616995072 617060608 (7712134530677 / 12500) (15425900940379 / 25000) := by
  exact
    packedTile32768 616995072 617060608 13 3225 24839 29 _ _ (506009 / 25000) (2024039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617060608 :
    ThetaLowerSegment 617060608 617126144 (15425900940379 / 25000) (15427510056949 / 25000) := by
  exact
    packedTile32768 617060608 617126144 13 3180 24840 29 _ _ (1012023 / 50000) (2024049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617126144 :
    ThetaLowerSegment 617126144 617191680 (15427510056949 / 25000) (61716535426709 / 100000) := by
  exact
    packedTile32768 617126144 617191680 13 3209 24842 29 _ _ (2024057 / 100000) (101203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617191680 :
    ThetaLowerSegment 617191680 617257216 (61716535426709 / 100000) (61723093407029 / 100000) := by
  exact
    packedTile32768 617191680 617257216 13 3240 24843 29 _ _ (506017 / 25000) (2024071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617257216 :
    ThetaLowerSegment 617257216 617322752 (61723093407029 / 100000) (61729693925387 / 100000) := by
  exact
    packedTile32768 617257216 617322752 13 3261 24844 29 _ _ (1012039 / 50000) (2024081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617322752 :
    ThetaLowerSegment 617322752 617339136 (61729693925387 / 100000) (30865667730783 / 50000) := by
  exact
    packedTile32768 617322752 617339136 11 811 24845 29 _ _ (2024089 / 100000) (506023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell617339136 :
    ThetaLowerSegment 617339136 617341184 (30865667730783 / 50000) (1929110684964 / 3125) := by
  exact
    packedTile32768 617339136 617341184 8 102 24846 29 _ _ (2024091 / 100000) (1012047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_585341184_617341184 :
    ThetaLowerSegment 585341184 617341184 (5853077896789 / 10000) (1929110684964 / 3125) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell585341184 cell585406720)
                    (ThetaLowerSegment.join cell585472256 cell585537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell585603328 cell585668864)
                    (ThetaLowerSegment.join cell585734400 cell585799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell585865472 cell585931008)
                    (ThetaLowerSegment.join cell585996544 cell586062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell586127616 cell586193152)
                    (ThetaLowerSegment.join cell586258688 cell586324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell586389760 cell586455296)
                    (ThetaLowerSegment.join cell586520832 cell586586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell586651904 cell586717440)
                    (ThetaLowerSegment.join cell586782976 cell586848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell586914048 cell586979584)
                    (ThetaLowerSegment.join cell587045120 cell587110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell587176192 cell587241728)
                    (ThetaLowerSegment.join cell587307264 cell587372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell587438336 cell587503872)
                    (ThetaLowerSegment.join cell587569408 cell587634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell587700480 cell587766016)
                    (ThetaLowerSegment.join cell587831552 cell587897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell587962624 cell588028160)
                    (ThetaLowerSegment.join cell588093696 cell588159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell588224768 cell588290304)
                    (ThetaLowerSegment.join cell588355840 cell588421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell588486912 cell588552448)
                    (ThetaLowerSegment.join cell588617984 cell588683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell588749056 cell588814592)
                    (ThetaLowerSegment.join cell588880128 cell588945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell589011200 cell589076736)
                    (ThetaLowerSegment.join cell589142272 cell589207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell589273344 cell589338880)
                    (ThetaLowerSegment.join cell589404416 cell589469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell589535488 cell589601024)
                    (ThetaLowerSegment.join cell589666560 cell589732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell589797632 cell589863168)
                    (ThetaLowerSegment.join cell589928704 cell589994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell590059776 cell590125312)
                    (ThetaLowerSegment.join cell590190848 cell590256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell590321920 cell590387456)
                    (ThetaLowerSegment.join cell590452992 cell590518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell590584064 cell590649600)
                    (ThetaLowerSegment.join cell590715136 cell590780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell590846208 cell590911744)
                    (ThetaLowerSegment.join cell590977280 cell591042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell591108352 cell591173888)
                    (ThetaLowerSegment.join cell591239424 cell591304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell591370496 cell591436032)
                    (ThetaLowerSegment.join cell591501568 cell591567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell591632640 cell591698176)
                    (ThetaLowerSegment.join cell591763712 cell591829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell591894784 cell591960320)
                    (ThetaLowerSegment.join cell592025856 cell592091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell592156928 cell592222464)
                    (ThetaLowerSegment.join cell592288000 cell592353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell592419072 cell592484608)
                    (ThetaLowerSegment.join cell592550144 cell592615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell592681216 cell592746752)
                    (ThetaLowerSegment.join cell592812288 cell592877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell592943360 cell593008896)
                    (ThetaLowerSegment.join cell593074432 cell593139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell593205504 cell593271040)
                    (ThetaLowerSegment.join cell593336576 cell593402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell593467648 cell593533184)
                    (ThetaLowerSegment.join cell593598720 cell593664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell593729792 cell593795328)
                    (ThetaLowerSegment.join cell593860864 cell593926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell593991936 cell594057472)
                    (ThetaLowerSegment.join cell594123008 cell594188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell594254080 cell594319616)
                    (ThetaLowerSegment.join cell594385152 cell594450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell594516224 cell594581760)
                    (ThetaLowerSegment.join cell594647296 cell594712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell594778368 cell594843904)
                    (ThetaLowerSegment.join cell594909440 cell594974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell595040512 cell595106048)
                    (ThetaLowerSegment.join cell595171584 cell595237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell595302656 cell595368192)
                    (ThetaLowerSegment.join cell595433728 cell595499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell595564800 cell595630336)
                    (ThetaLowerSegment.join cell595695872 cell595761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell595826944 cell595892480)
                    (ThetaLowerSegment.join cell595958016 cell596023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell596089088 cell596154624)
                    (ThetaLowerSegment.join cell596220160 cell596285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell596351232 cell596416768)
                    (ThetaLowerSegment.join cell596482304 cell596547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell596613376 cell596678912)
                    (ThetaLowerSegment.join cell596744448 cell596809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell596875520 cell596941056)
                    (ThetaLowerSegment.join cell597006592 cell597072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell597137664 cell597203200)
                    (ThetaLowerSegment.join cell597268736 cell597334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell597399808 cell597465344)
                    (ThetaLowerSegment.join cell597530880 cell597596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell597661952 cell597727488)
                    (ThetaLowerSegment.join cell597793024 cell597858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell597924096 cell597989632)
                    (ThetaLowerSegment.join cell598055168 cell598120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell598186240 cell598251776)
                    (ThetaLowerSegment.join cell598317312 cell598382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell598448384 cell598513920)
                    (ThetaLowerSegment.join cell598579456 cell598644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell598710528 cell598776064)
                    (ThetaLowerSegment.join cell598841600 cell598907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell598972672 cell599038208)
                    (ThetaLowerSegment.join cell599103744 cell599169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell599234816 cell599300352)
                    (ThetaLowerSegment.join cell599365888 cell599431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell599496960 cell599562496)
                    (ThetaLowerSegment.join cell599628032 cell599693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell599759104 cell599824640)
                    (ThetaLowerSegment.join cell599890176 cell599955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell600021248 cell600086784)
                    (ThetaLowerSegment.join cell600152320 cell600217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell600283392 cell600348928)
                    (ThetaLowerSegment.join cell600414464 cell600480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell600545536 cell600611072)
                    (ThetaLowerSegment.join cell600676608 cell600742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell600807680 cell600873216)
                    (ThetaLowerSegment.join cell600938752 cell601004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell601069824 cell601135360)
                    (ThetaLowerSegment.join cell601200896 cell601266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell601331968 cell601397504)
                    (ThetaLowerSegment.join cell601463040 cell601528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell601594112 cell601659648)
                    (ThetaLowerSegment.join cell601725184 cell601790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell601856256 cell601921792)
                    (ThetaLowerSegment.join cell601987328 cell602052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell602118400 cell602183936)
                    (ThetaLowerSegment.join cell602249472 cell602315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell602380544 cell602446080)
                    (ThetaLowerSegment.join cell602511616 cell602577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell602642688 cell602708224)
                    (ThetaLowerSegment.join cell602773760 cell602839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell602904832 cell602970368)
                    (ThetaLowerSegment.join cell603035904 cell603101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell603166976 cell603232512)
                    (ThetaLowerSegment.join cell603298048 cell603363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell603429120 cell603494656)
                    (ThetaLowerSegment.join cell603560192 cell603625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell603691264 cell603756800)
                    (ThetaLowerSegment.join cell603822336 cell603887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell603953408 cell604018944)
                    (ThetaLowerSegment.join cell604084480 cell604150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell604215552 cell604281088)
                    (ThetaLowerSegment.join cell604346624 cell604412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell604477696 cell604543232)
                    (ThetaLowerSegment.join cell604608768 cell604674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell604739840 cell604805376)
                    (ThetaLowerSegment.join cell604870912 cell604936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell605001984 cell605067520)
                    (ThetaLowerSegment.join cell605133056 cell605198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell605264128 cell605329664)
                    (ThetaLowerSegment.join cell605395200 cell605460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell605526272 cell605591808)
                    (ThetaLowerSegment.join cell605657344 cell605722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell605788416 cell605853952)
                    (ThetaLowerSegment.join cell605919488 cell605985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell606050560 cell606116096)
                    (ThetaLowerSegment.join cell606181632 cell606247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell606312704 cell606378240)
                    (ThetaLowerSegment.join cell606443776 cell606509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell606574848 cell606640384)
                    (ThetaLowerSegment.join cell606705920 cell606771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell606836992 cell606902528)
                    (ThetaLowerSegment.join cell606968064 cell607033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell607099136 cell607164672)
                    (ThetaLowerSegment.join cell607230208 cell607295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell607361280 cell607426816)
                    (ThetaLowerSegment.join cell607492352 cell607557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell607623424 cell607688960)
                    (ThetaLowerSegment.join cell607754496 cell607820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell607885568 cell607951104)
                    (ThetaLowerSegment.join cell608016640 cell608082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell608147712 cell608213248)
                    (ThetaLowerSegment.join cell608278784 cell608344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell608409856 cell608475392)
                    (ThetaLowerSegment.join cell608540928 cell608606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell608672000 cell608737536)
                    (ThetaLowerSegment.join cell608803072 cell608868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell608934144 cell608999680)
                    (ThetaLowerSegment.join cell609065216 cell609130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell609196288 cell609261824)
                    (ThetaLowerSegment.join cell609327360 cell609392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell609458432 cell609523968)
                    (ThetaLowerSegment.join cell609589504 cell609655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell609720576 cell609786112)
                    (ThetaLowerSegment.join cell609851648 cell609917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell609982720 cell610048256)
                    (ThetaLowerSegment.join cell610113792 cell610179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell610244864 cell610310400)
                    (ThetaLowerSegment.join cell610375936 cell610441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell610507008 cell610572544)
                    (ThetaLowerSegment.join cell610638080 cell610703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell610769152 cell610834688)
                    (ThetaLowerSegment.join cell610900224 cell610965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell611031296 cell611096832)
                    (ThetaLowerSegment.join cell611162368 cell611227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell611293440 cell611358976)
                    (ThetaLowerSegment.join cell611424512 cell611490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell611555584 cell611621120)
                    (ThetaLowerSegment.join cell611686656 cell611752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell611817728 cell611883264)
                    (ThetaLowerSegment.join cell611948800 cell612014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell612079872 cell612145408)
                    (ThetaLowerSegment.join cell612210944 cell612276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell612342016 cell612407552)
                    (ThetaLowerSegment.join cell612473088 cell612538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell612604160 cell612669696)
                    (ThetaLowerSegment.join cell612735232 cell612800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell612866304 cell612931840)
                    (ThetaLowerSegment.join cell612997376 cell613062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell613128448 cell613193984)
                    (ThetaLowerSegment.join cell613259520 cell613325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell613390592 cell613456128)
                    (ThetaLowerSegment.join cell613521664 cell613587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell613652736 cell613718272)
                    (ThetaLowerSegment.join cell613783808 cell613849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell613914880 cell613980416)
                    (ThetaLowerSegment.join cell614045952 cell614111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell614177024 cell614242560)
                    (ThetaLowerSegment.join cell614308096 cell614373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell614439168 cell614504704)
                    (ThetaLowerSegment.join cell614570240 cell614635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell614701312 cell614766848)
                    (ThetaLowerSegment.join cell614832384 cell614897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell614963456 cell615028992)
                    (ThetaLowerSegment.join cell615094528 cell615160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell615225600 cell615291136)
                    (ThetaLowerSegment.join cell615356672 cell615422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell615487744 cell615553280)
                    (ThetaLowerSegment.join cell615618816 cell615684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell615749888 cell615815424)
                    (ThetaLowerSegment.join cell615880960 cell615946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell616012032 cell616077568)
                    (ThetaLowerSegment.join cell616143104 cell616208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell616274176 cell616339712)
                    (ThetaLowerSegment.join cell616405248 cell616470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell616536320 cell616601856)
                    (ThetaLowerSegment.join cell616667392 cell616732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell616798464 cell616864000)
                  (ThetaLowerSegment.join cell616929536 cell616995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell617060608 cell617126144)
                  (ThetaLowerSegment.join cell617191680 cell617257216)))
              (ThetaLowerSegment.join cell617322752 cell617339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
