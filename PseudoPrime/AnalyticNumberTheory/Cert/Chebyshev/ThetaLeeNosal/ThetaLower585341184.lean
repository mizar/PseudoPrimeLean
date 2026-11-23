/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 585341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell553341184 :
    ThetaLowerSegment 553341184 553406720 (55331452530587 / 100000) (55337995258337 / 100000) := by
  exact
    packedTile32768 553341184 553406720 13 3250 23523 29 _ _ (2013147 / 100000) (40263 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553406720 :
    ThetaLowerSegment 553406720 553472256 (55337995258337 / 100000) (55344578288267 / 100000) := by
  exact
    packedTile32768 553406720 553472256 13 3270 23524 29 _ _ (2013159 / 100000) (1006581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553472256 :
    ThetaLowerSegment 553472256 553537792 (55344578288267 / 100000) (55351165383779 / 100000) := by
  exact
    packedTile32768 553472256 553537792 13 3272 23525 29 _ _ (2013171 / 100000) (1006587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553537792 :
    ThetaLowerSegment 553537792 553603328 (55351165383779 / 100000) (2767885109449 / 5000) := by
  exact
    packedTile32768 553537792 553603328 13 3247 23527 29 _ _ (2013183 / 100000) (1006593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553603328 :
    ThetaLowerSegment 553603328 553668864 (2767885109449 / 5000) (6920518554521 / 12500) := by
  exact
    packedTile32768 553603328 553668864 13 3202 23528 29 _ _ (1006597 / 50000) (2013197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553668864 :
    ThetaLowerSegment 553668864 553734400 (6920518554521 / 12500) (27685284275051 / 50000) := by
  exact
    packedTile32768 553668864 553734400 13 3189 23530 29 _ _ (1006603 / 50000) (2013209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553734400 :
    ThetaLowerSegment 553734400 553799936 (27685284275051 / 50000) (13844302539071 / 25000) := by
  exact
    packedTile32768 553734400 553799936 13 3299 23531 29 _ _ (1006609 / 50000) (2013221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553799936 :
    ThetaLowerSegment 553799936 553865472 (13844302539071 / 25000) (27691887649657 / 50000) := by
  exact
    packedTile32768 553799936 553865472 13 3261 23532 29 _ _ (201323 / 10000) (2013233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553865472 :
    ThetaLowerSegment 553865472 553931008 (27691887649657 / 50000) (13847569014433 / 25000) := by
  exact
    packedTile32768 553865472 553931008 13 3229 23534 29 _ _ (1006621 / 50000) (402649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553931008 :
    ThetaLowerSegment 553931008 553996544 (13847569014433 / 25000) (5539689362363 / 10000) := by
  exact
    packedTile32768 553931008 553996544 13 3287 23535 29 _ _ (1006627 / 50000) (2013257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553996544 :
    ThetaLowerSegment 553996544 554062080 (5539689362363 / 10000) (2216137710987 / 4000) := by
  exact
    packedTile32768 553996544 554062080 13 3253 23537 29 _ _ (402653 / 20000) (503317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554062080 :
    ThetaLowerSegment 554062080 554127616 (2216137710987 / 4000) (55410038270127 / 100000) := by
  exact
    packedTile32768 554062080 554127616 13 3276 23538 29 _ _ (2013277 / 100000) (12583 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554127616 :
    ThetaLowerSegment 554127616 554193152 (55410038270127 / 100000) (3463533195447 / 6250) := by
  exact
    packedTile32768 554127616 554193152 13 3225 23539 29 _ _ (2013289 / 100000) (503323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554193152 :
    ThetaLowerSegment 554193152 554258688 (3463533195447 / 6250) (5542305019579 / 10000) := by
  exact
    packedTile32768 554193152 554258688 13 3238 23541 29 _ _ (2013301 / 100000) (251663 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554258688 :
    ThetaLowerSegment 554258688 554324224 (5542305019579 / 10000) (55429611582857 / 100000) := by
  exact
    packedTile32768 554258688 554324224 13 3259 23542 29 _ _ (2013313 / 100000) (503329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554324224 :
    ThetaLowerSegment 554324224 554389760 (55429611582857 / 100000) (55436110595957 / 100000) := by
  exact
    packedTile32768 554324224 554389760 13 3228 23544 29 _ _ (80533 / 4000) (125833 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554389760 :
    ThetaLowerSegment 554389760 554455296 (55436110595957 / 100000) (55442668031309 / 100000) := by
  exact
    packedTile32768 554389760 554455296 13 3257 23545 29 _ _ (251667 / 12500) (2013339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554455296 :
    ThetaLowerSegment 554455296 554520832 (55442668031309 / 100000) (55449163091957 / 100000) := by
  exact
    packedTile32768 554455296 554520832 13 3226 23546 29 _ _ (503337 / 25000) (2013351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554520832 :
    ThetaLowerSegment 554520832 554586368 (55449163091957 / 100000) (55455547456517 / 100000) := by
  exact
    packedTile32768 554520832 554586368 13 3171 23548 29 _ _ (25167 / 1250) (2013363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554586368 :
    ThetaLowerSegment 554586368 554651904 (55455547456517 / 100000) (55462076821913 / 100000) := by
  exact
    packedTile32768 554586368 554651904 13 3243 23549 29 _ _ (503343 / 25000) (16107 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554651904 :
    ThetaLowerSegment 554651904 554717440 (55462076821913 / 100000) (11093735338933 / 20000) := by
  exact
    packedTile32768 554651904 554717440 13 3278 23551 29 _ _ (251673 / 12500) (2013387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554717440 :
    ThetaLowerSegment 554717440 554782976 (11093735338933 / 20000) (5547526250971 / 10000) := by
  exact
    packedTile32768 554717440 554782976 13 3271 23552 29 _ _ (402679 / 20000) (1006699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554782976 :
    ThetaLowerSegment 554782976 554848512 (5547526250971 / 10000) (277409231753 / 500) := by
  exact
    packedTile32768 554782976 554848512 13 3270 23553 29 _ _ (2013407 / 100000) (201341 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554848512 :
    ThetaLowerSegment 554848512 554914048 (277409231753 / 500) (27744182900661 / 50000) := by
  exact
    packedTile32768 554848512 554914048 13 3238 23555 29 _ _ (2013419 / 100000) (1006711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554914048 :
    ThetaLowerSegment 554914048 554979584 (27744182900661 / 50000) (1734214410304 / 3125) := by
  exact
    packedTile32768 554914048 554979584 13 3226 23556 29 _ _ (2013431 / 100000) (1006717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell554979584 :
    ThetaLowerSegment 554979584 555045120 (1734214410304 / 3125) (27750754759257 / 50000) := by
  exact
    packedTile32768 554979584 555045120 13 3302 23558 29 _ _ (2013443 / 100000) (1006723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555045120 :
    ThetaLowerSegment 555045120 555110656 (27750754759257 / 50000) (27754054810363 / 50000) := by
  exact
    packedTile32768 555045120 555110656 13 3278 23559 29 _ _ (1006727 / 50000) (2013457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555110656 :
    ThetaLowerSegment 555110656 555176192 (27754054810363 / 50000) (27757342800341 / 50000) := by
  exact
    packedTile32768 555110656 555176192 13 3266 23560 29 _ _ (1006733 / 50000) (2013469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555176192 :
    ThetaLowerSegment 555176192 555241728 (27757342800341 / 50000) (6940164497967 / 12500) := by
  exact
    packedTile32768 555176192 555241728 13 3293 23562 29 _ _ (1006739 / 50000) (2013481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555241728 :
    ThetaLowerSegment 555241728 555307264 (6940164497967 / 12500) (6940973920947 / 12500) := by
  exact
    packedTile32768 555241728 555307264 13 3216 23563 29 _ _ (201349 / 10000) (2013493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555307264 :
    ThetaLowerSegment 555307264 555372800 (6940973920947 / 12500) (1735443571998 / 3125) := by
  exact
    packedTile32768 555307264 555372800 13 3180 23564 29 _ _ (1006751 / 50000) (402701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555372800 :
    ThetaLowerSegment 555372800 555438336 (1735443571998 / 3125) (27770412402769 / 50000) := by
  exact
    packedTile32768 555372800 555438336 13 3293 23566 29 _ _ (1006757 / 50000) (2013517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555438336 :
    ThetaLowerSegment 555438336 555503872 (27770412402769 / 50000) (55547326477763 / 100000) := by
  exact
    packedTile32768 555438336 555503872 13 3229 23567 29 _ _ (80541 / 4000) (251691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555503872 :
    ThetaLowerSegment 555503872 555569408 (55547326477763 / 100000) (55553894635457 / 100000) := by
  exact
    packedTile32768 555503872 555569408 13 3262 23569 29 _ _ (2013537 / 100000) (100677 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555569408 :
    ThetaLowerSegment 555569408 555634944 (55553894635457 / 100000) (6945055085407 / 12500) := by
  exact
    packedTile32768 555569408 555634944 13 3251 23570 29 _ _ (2013549 / 100000) (125847 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555634944 :
    ThetaLowerSegment 555634944 555700480 (6945055085407 / 12500) (55567047176897 / 100000) := by
  exact
    packedTile32768 555634944 555700480 13 3281 23571 29 _ _ (2013561 / 100000) (503391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555700480 :
    ThetaLowerSegment 555700480 555766016 (55567047176897 / 100000) (13893392284961 / 25000) := by
  exact
    packedTile32768 555700480 555766016 13 3239 23573 29 _ _ (2013573 / 100000) (251697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555766016 :
    ThetaLowerSegment 555766016 555831552 (13893392284961 / 25000) (13895023791397 / 25000) := by
  exact
    packedTile32768 555766016 555831552 13 3241 23574 29 _ _ (125849 / 6250) (2013587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555831552 :
    ThetaLowerSegment 555831552 555897088 (13895023791397 / 25000) (13896654804157 / 25000) := by
  exact
    packedTile32768 555831552 555897088 13 3240 23576 29 _ _ (503399 / 25000) (2013599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555897088 :
    ThetaLowerSegment 555897088 555962624 (13896654804157 / 25000) (555931815651 / 1000) := by
  exact
    packedTile32768 555897088 555962624 13 3259 23577 29 _ _ (251701 / 12500) (2013611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell555962624 :
    ThetaLowerSegment 555962624 556028160 (555931815651 / 1000) (2779983875161 / 5000) := by
  exact
    packedTile32768 555962624 556028160 13 3226 23578 29 _ _ (100681 / 5000) (2013623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556028160 :
    ThetaLowerSegment 556028160 556093696 (2779983875161 / 5000) (27803139092819 / 50000) := by
  exact
    packedTile32768 556028160 556093696 13 3278 23580 29 _ _ (2013631 / 100000) (1006817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556093696 :
    ThetaLowerSegment 556093696 556159232 (27803139092819 / 50000) (3475794863497 / 6250) := by
  exact
    packedTile32768 556093696 556159232 13 3198 23581 29 _ _ (2013643 / 100000) (1006823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556159232 :
    ThetaLowerSegment 556159232 556224768 (3475794863497 / 6250) (27809739834721 / 50000) := by
  exact
    packedTile32768 556159232 556224768 13 3358 23583 29 _ _ (402731 / 20000) (1006829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556224768 :
    ThetaLowerSegment 556224768 556290304 (27809739834721 / 50000) (55625957636181 / 100000) := by
  exact
    packedTile32768 556224768 556290304 13 3217 23584 29 _ _ (2013667 / 100000) (201367 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556290304 :
    ThetaLowerSegment 556290304 556355840 (55625957636181 / 100000) (55632566530659 / 100000) := by
  exact
    packedTile32768 556290304 556355840 13 3282 23585 29 _ _ (2013679 / 100000) (1006841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556355840 :
    ThetaLowerSegment 556355840 556421376 (55632566530659 / 100000) (55639080817809 / 100000) := by
  exact
    packedTile32768 556355840 556421376 13 3235 23587 29 _ _ (201369 / 10000) (2013693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556421376 :
    ThetaLowerSegment 556421376 556486912 (55639080817809 / 100000) (55645693815177 / 100000) := by
  exact
    packedTile32768 556421376 556486912 13 3284 23588 29 _ _ (1006851 / 50000) (402741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556486912 :
    ThetaLowerSegment 556486912 556552448 (55645693815177 / 100000) (55652234358249 / 100000) := by
  exact
    packedTile32768 556486912 556552448 13 3248 23589 29 _ _ (1006857 / 50000) (2013717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556552448 :
    ThetaLowerSegment 556552448 556617984 (55652234358249 / 100000) (55658813201091 / 100000) := by
  exact
    packedTile32768 556552448 556617984 13 3267 23591 29 _ _ (1006863 / 50000) (2013729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556617984 :
    ThetaLowerSegment 556617984 556683520 (55658813201091 / 100000) (55665373956237 / 100000) := by
  exact
    packedTile32768 556617984 556683520 13 3258 23592 29 _ _ (2013737 / 100000) (100687 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556683520 :
    ThetaLowerSegment 556683520 556749056 (55665373956237 / 100000) (347948950308 / 625) := by
  exact
    packedTile32768 556683520 556749056 13 3207 23594 29 _ _ (2013749 / 100000) (251719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556749056 :
    ThetaLowerSegment 556749056 556814592 (347948950308 / 625) (1739948141401 / 3125) := by
  exact
    packedTile32768 556749056 556814592 13 3232 23595 29 _ _ (2013761 / 100000) (503441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556814592 :
    ThetaLowerSegment 556814592 556880128 (1739948141401 / 3125) (55684911466131 / 100000) := by
  exact
    packedTile32768 556814592 556880128 13 3263 23596 29 _ _ (2013773 / 100000) (125861 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556880128 :
    ThetaLowerSegment 556880128 556945664 (55684911466131 / 100000) (55691415991681 / 100000) := by
  exact
    packedTile32768 556880128 556945664 13 3230 23598 29 _ _ (402757 / 20000) (503447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell556945664 :
    ThetaLowerSegment 556945664 557011200 (55691415991681 / 100000) (55697946732109 / 100000) := by
  exact
    packedTile32768 556945664 557011200 13 3243 23599 29 _ _ (503449 / 25000) (2013799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557011200 :
    ThetaLowerSegment 557011200 557076736 (55697946732109 / 100000) (55704471470029 / 100000) := by
  exact
    packedTile32768 557011200 557076736 13 3240 23601 29 _ _ (125863 / 6250) (2013811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557076736 :
    ThetaLowerSegment 557076736 557142272 (55704471470029 / 100000) (55710992219189 / 100000) := by
  exact
    packedTile32768 557076736 557142272 13 3238 23602 29 _ _ (100691 / 5000) (2013823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557142272 :
    ThetaLowerSegment 557142272 557207808 (55710992219189 / 100000) (55717547242349 / 100000) := by
  exact
    packedTile32768 557142272 557207808 13 3255 23603 29 _ _ (251729 / 12500) (402767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557207808 :
    ThetaLowerSegment 557207808 557273344 (55717547242349 / 100000) (11144859528817 / 20000) := by
  exact
    packedTile32768 557207808 557273344 13 3352 23605 29 _ _ (2013843 / 100000) (1006923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557273344 :
    ThetaLowerSegment 557273344 557338880 (11144859528817 / 20000) (11146180617697 / 20000) := by
  exact
    packedTile32768 557273344 557338880 13 3280 23606 29 _ _ (402771 / 20000) (1006929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557338880 :
    ThetaLowerSegment 557338880 557404416 (11146180617697 / 20000) (11147473520311 / 20000) := by
  exact
    packedTile32768 557338880 557404416 13 3210 23608 29 _ _ (2013867 / 100000) (201387 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557404416 :
    ThetaLowerSegment 557404416 557469952 (11147473520311 / 20000) (13935964583393 / 25000) := by
  exact
    packedTile32768 557404416 557469952 13 3223 23609 29 _ _ (2013879 / 100000) (1006941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557469952 :
    ThetaLowerSegment 557469952 557535488 (13935964583393 / 25000) (27875224897771 / 50000) := by
  exact
    packedTile32768 557469952 557535488 13 3273 23610 29 _ _ (201389 / 10000) (2013893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557535488 :
    ThetaLowerSegment 557535488 557601024 (27875224897771 / 50000) (27878467279991 / 50000) := by
  exact
    packedTile32768 557535488 557601024 13 3220 23612 29 _ _ (1006951 / 50000) (402781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557601024 :
    ThetaLowerSegment 557601024 557666560 (27878467279991 / 50000) (5576342339089 / 10000) := by
  exact
    packedTile32768 557601024 557666560 13 3222 23613 29 _ _ (1006957 / 50000) (2013917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557666560 :
    ThetaLowerSegment 557666560 557732096 (5576342339089 / 10000) (27884996408751 / 50000) := by
  exact
    packedTile32768 557666560 557732096 13 3262 23614 29 _ _ (1006963 / 50000) (2013929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557732096 :
    ThetaLowerSegment 557732096 557797632 (27884996408751 / 50000) (2231059832803 / 4000) := by
  exact
    packedTile32768 557732096 557797632 13 3229 23616 29 _ _ (2013937 / 100000) (100697 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557797632 :
    ThetaLowerSegment 557797632 557863168 (2231059832803 / 4000) (13945789994329 / 25000) := by
  exact
    packedTile32768 557797632 557863168 13 3309 23617 29 _ _ (2013949 / 100000) (62936 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557863168 :
    ThetaLowerSegment 557863168 557928704 (13945789994329 / 25000) (2789490705223 / 5000) := by
  exact
    packedTile32768 557863168 557928704 13 3304 23619 29 _ _ (2013961 / 100000) (503491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557928704 :
    ThetaLowerSegment 557928704 557994240 (2789490705223 / 5000) (55796397782197 / 100000) := by
  exact
    packedTile32768 557928704 557994240 13 3269 23620 29 _ _ (2013973 / 100000) (251747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell557994240 :
    ThetaLowerSegment 557994240 558059776 (55796397782197 / 100000) (55802949272149 / 100000) := by
  exact
    packedTile32768 557994240 558059776 13 3253 23621 29 _ _ (62937 / 3125) (2013987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558059776 :
    ThetaLowerSegment 558059776 558125312 (55802949272149 / 100000) (55809482675173 / 100000) := by
  exact
    packedTile32768 558059776 558125312 13 3244 23623 29 _ _ (503499 / 25000) (2013999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558125312 :
    ThetaLowerSegment 558125312 558190848 (55809482675173 / 100000) (55816078551373 / 100000) := by
  exact
    packedTile32768 558125312 558190848 13 3275 23624 29 _ _ (251751 / 12500) (2014011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558190848 :
    ThetaLowerSegment 558190848 558256384 (55816078551373 / 100000) (55822620088333 / 100000) := by
  exact
    packedTile32768 558190848 558256384 13 3248 23626 29 _ _ (100701 / 5000) (2014023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558256384 :
    ThetaLowerSegment 558256384 558321920 (55822620088333 / 100000) (27914583851557 / 50000) := by
  exact
    packedTile32768 558256384 558321920 13 3251 23627 29 _ _ (2014031 / 100000) (1007017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558321920 :
    ThetaLowerSegment 558321920 558387456 (27914583851557 / 50000) (11167161600577 / 20000) := by
  exact
    packedTile32768 558321920 558387456 13 3297 23628 29 _ _ (2014043 / 100000) (1007023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558387456 :
    ThetaLowerSegment 558387456 558452992 (11167161600577 / 20000) (11168488460011 / 20000) := by
  exact
    packedTile32768 558387456 558452992 13 3294 23630 29 _ _ (402811 / 20000) (1007029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558452992 :
    ThetaLowerSegment 558452992 558518528 (11168488460011 / 20000) (27924444664261 / 50000) := by
  exact
    packedTile32768 558452992 558518528 13 3201 23631 29 _ _ (2014067 / 100000) (201407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558518528 :
    ThetaLowerSegment 558518528 558584064 (27924444664261 / 50000) (27927661146827 / 50000) := by
  exact
    packedTile32768 558518528 558584064 13 3194 23632 29 _ _ (1007039 / 50000) (2014081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558584064 :
    ThetaLowerSegment 558584064 558649600 (27927661146827 / 50000) (27930901817637 / 50000) := by
  exact
    packedTile32768 558584064 558649600 13 3218 23634 29 _ _ (201409 / 10000) (2014093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558649600 :
    ThetaLowerSegment 558649600 558715136 (27930901817637 / 50000) (27934166676979 / 50000) := by
  exact
    packedTile32768 558649600 558715136 13 3242 23635 29 _ _ (1007051 / 50000) (402821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558715136 :
    ThetaLowerSegment 558715136 558780672 (27934166676979 / 50000) (3492186371517 / 6250) := by
  exact
    packedTile32768 558715136 558780672 13 3301 23637 29 _ _ (1007057 / 50000) (2014117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558780672 :
    ThetaLowerSegment 558780672 558846208 (3492186371517 / 6250) (55881545977647 / 100000) := by
  exact
    packedTile32768 558780672 558846208 13 3259 23638 29 _ _ (16113 / 800) (125883 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558846208 :
    ThetaLowerSegment 558846208 558911744 (55881545977647 / 100000) (55888176516651 / 100000) := by
  exact
    packedTile32768 558846208 558911744 13 3292 23639 29 _ _ (2014137 / 100000) (100707 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558911744 :
    ThetaLowerSegment 558911744 558977280 (55888176516651 / 100000) (13973694220731 / 25000) := by
  exact
    packedTile32768 558911744 558977280 13 3277 23641 29 _ _ (2014149 / 100000) (251769 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell558977280 :
    ThetaLowerSegment 558977280 559042816 (13973694220731 / 25000) (13975328711571 / 25000) := by
  exact
    packedTile32768 558977280 559042816 13 3246 23642 29 _ _ (25177 / 1250) (2014163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559042816 :
    ThetaLowerSegment 559042816 559108352 (13975328711571 / 25000) (13976935013741 / 25000) := by
  exact
    packedTile32768 559042816 559108352 13 3190 23644 29 _ _ (503543 / 25000) (80567 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559108352 :
    ThetaLowerSegment 559108352 559173888 (13976935013741 / 25000) (13978558949591 / 25000) := by
  exact
    packedTile32768 559108352 559173888 13 3225 23645 29 _ _ (251773 / 12500) (2014187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559173888 :
    ThetaLowerSegment 559173888 559239424 (13978558949591 / 25000) (13980182391567 / 25000) := by
  exact
    packedTile32768 559173888 559239424 13 3224 23646 29 _ _ (503549 / 25000) (2014199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559239424 :
    ThetaLowerSegment 559239424 559304960 (13980182391567 / 25000) (27963666068407 / 50000) := by
  exact
    packedTile32768 559239424 559304960 13 3278 23648 29 _ _ (2014207 / 100000) (201421 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559304960 :
    ThetaLowerSegment 559304960 559370496 (27963666068407 / 50000) (5593378569449 / 10000) := by
  exact
    packedTile32768 559304960 559370496 13 3204 23649 29 _ _ (2014219 / 100000) (1007111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559370496 :
    ThetaLowerSegment 559370496 559436032 (5593378569449 / 10000) (13985105142851 / 25000) := by
  exact
    packedTile32768 559370496 559436032 13 3294 23651 29 _ _ (2014231 / 100000) (1007117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559436032 :
    ThetaLowerSegment 559436032 559501568 (13985105142851 / 25000) (5594691247337 / 10000) := by
  exact
    packedTile32768 559436032 559501568 13 3223 23652 29 _ _ (1007121 / 50000) (402849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559501568 :
    ThetaLowerSegment 559501568 559567104 (5594691247337 / 10000) (27976783784293 / 50000) := by
  exact
    packedTile32768 559501568 559567104 13 3304 23653 29 _ _ (1007127 / 50000) (2014257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559567104 :
    ThetaLowerSegment 559567104 559632640 (27976783784293 / 50000) (27980052938011 / 50000) := by
  exact
    packedTile32768 559567104 559632640 13 3246 23655 29 _ _ (1007133 / 50000) (2014269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559632640 :
    ThetaLowerSegment 559632640 559698176 (27980052938011 / 50000) (27983360382487 / 50000) := by
  exact
    packedTile32768 559632640 559698176 13 3284 23656 29 _ _ (1007139 / 50000) (2014281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559698176 :
    ThetaLowerSegment 559698176 559763712 (27983360382487 / 50000) (55973333675761 / 100000) := by
  exact
    packedTile32768 559698176 559763712 13 3283 23657 29 _ _ (2014289 / 100000) (503573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559763712 :
    ThetaLowerSegment 559763712 559829248 (55973333675761 / 100000) (13994936298961 / 25000) := by
  exact
    packedTile32768 559763712 559829248 13 3183 23659 29 _ _ (2014301 / 100000) (62947 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559829248 :
    ThetaLowerSegment 559829248 559894784 (13994936298961 / 25000) (1749572245507 / 3125) := by
  exact
    packedTile32768 559829248 559894784 13 3260 23660 29 _ _ (2014313 / 100000) (503579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559894784 :
    ThetaLowerSegment 559894784 559960320 (1749572245507 / 3125) (69991007546 / 125) := by
  exact
    packedTile32768 559894784 559960320 13 3224 23662 29 _ _ (503581 / 25000) (2014327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell559960320 :
    ThetaLowerSegment 559960320 560025856 (69991007546 / 125) (1749978951326 / 3125) := by
  exact
    packedTile32768 559960320 560025856 13 3237 23663 29 _ _ (62948 / 3125) (2014339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560025856 :
    ThetaLowerSegment 560025856 560091392 (1749978951326 / 3125) (3500361275839 / 6250) := by
  exact
    packedTile32768 560025856 560091392 13 3204 23664 29 _ _ (503587 / 25000) (2014351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560091392 :
    ThetaLowerSegment 560091392 560156928 (3500361275839 / 6250) (7001536604913 / 12500) := by
  exact
    packedTile32768 560091392 560156928 13 3233 23666 29 _ _ (50359 / 2500) (2014363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560156928 :
    ThetaLowerSegment 560156928 560222464 (7001536604913 / 12500) (11203804570563 / 20000) := by
  exact
    packedTile32768 560156928 560222464 13 3341 23667 29 _ _ (2014371 / 100000) (1007187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560222464 :
    ThetaLowerSegment 560222464 560288000 (11203804570563 / 20000) (11205117948279 / 20000) := by
  exact
    packedTile32768 560222464 560288000 13 3260 23669 29 _ _ (2014383 / 100000) (1007193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560288000 :
    ThetaLowerSegment 560288000 560353536 (11205117948279 / 20000) (11206444225947 / 20000) := by
  exact
    packedTile32768 560288000 560353536 13 3292 23670 29 _ _ (402879 / 20000) (1007199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560353536 :
    ThetaLowerSegment 560353536 560419072 (11206444225947 / 20000) (56038701473837 / 100000) := by
  exact
    packedTile32768 560353536 560419072 13 3217 23671 29 _ _ (1007203 / 50000) (2014409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560419072 :
    ThetaLowerSegment 560419072 560484608 (56038701473837 / 100000) (56045304736041 / 100000) := by
  exact
    packedTile32768 560419072 560484608 13 3278 23673 29 _ _ (1007209 / 50000) (2014421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560484608 :
    ThetaLowerSegment 560484608 560550144 (56045304736041 / 100000) (56051889907711 / 100000) := by
  exact
    packedTile32768 560484608 560550144 13 3269 23674 29 _ _ (201443 / 10000) (2014433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560550144 :
    ThetaLowerSegment 560550144 560615680 (56051889907711 / 100000) (28029158994471 / 50000) := by
  exact
    packedTile32768 560550144 560615680 13 3191 23675 29 _ _ (2014441 / 100000) (503611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560615680 :
    ThetaLowerSegment 560615680 560681216 (28029158994471 / 50000) (56064899206893 / 100000) := by
  exact
    packedTile32768 560615680 560681216 13 3267 23677 29 _ _ (2014453 / 100000) (251807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560681216 :
    ThetaLowerSegment 560681216 560746752 (56064899206893 / 100000) (56071518738883 / 100000) := by
  exact
    packedTile32768 560681216 560746752 13 3286 23678 29 _ _ (402893 / 20000) (503617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560746752 :
    ThetaLowerSegment 560746752 560812288 (56071518738883 / 100000) (56078176582063 / 100000) := by
  exact
    packedTile32768 560746752 560812288 13 3305 23680 29 _ _ (503619 / 25000) (2014479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560812288 :
    ThetaLowerSegment 560812288 560877824 (56078176582063 / 100000) (56084677334839 / 100000) := by
  exact
    packedTile32768 560812288 560877824 13 3227 23681 29 _ _ (251811 / 12500) (2014491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560877824 :
    ThetaLowerSegment 560877824 560943360 (56084677334839 / 100000) (56091188198839 / 100000) := by
  exact
    packedTile32768 560877824 560943360 13 3232 23682 29 _ _ (4029 / 200) (2014503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell560943360 :
    ThetaLowerSegment 560943360 561008896 (56091188198839 / 100000) (2243903612719 / 4000) := by
  exact
    packedTile32768 560943360 561008896 13 3178 23684 29 _ _ (125907 / 6250) (402903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561008896 :
    ThetaLowerSegment 561008896 561074432 (2243903612719 / 4000) (56104081111081 / 100000) := by
  exact
    packedTile32768 561008896 561074432 13 3222 23685 29 _ _ (2014523 / 100000) (1007263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561074432 :
    ThetaLowerSegment 561074432 561139968 (56104081111081 / 100000) (28055331298463 / 50000) := by
  exact
    packedTile32768 561074432 561139968 13 3267 23687 29 _ _ (402907 / 20000) (1007269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561139968 :
    ThetaLowerSegment 561139968 561205504 (28055331298463 / 50000) (56117195772847 / 100000) := by
  exact
    packedTile32768 561139968 561205504 13 3243 23688 29 _ _ (2014547 / 100000) (40291 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561205504 :
    ThetaLowerSegment 561205504 561271040 (56117195772847 / 100000) (56123656460353 / 100000) := by
  exact
    packedTile32768 561205504 561271040 13 3207 23689 29 _ _ (1007279 / 50000) (2014561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561271040 :
    ThetaLowerSegment 561271040 561336576 (56123656460353 / 100000) (56130221943983 / 100000) := by
  exact
    packedTile32768 561271040 561336576 13 3259 23691 29 _ _ (201457 / 10000) (2014573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561336576 :
    ThetaLowerSegment 561336576 561402112 (56130221943983 / 100000) (449093445551 / 800) := by
  exact
    packedTile32768 561336576 561402112 13 3206 23692 29 _ _ (1007291 / 50000) (402917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561402112 :
    ThetaLowerSegment 561402112 561467648 (449093445551 / 800) (56143240208683 / 100000) := by
  exact
    packedTile32768 561402112 561467648 13 3256 23693 29 _ _ (2014593 / 100000) (503649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561467648 :
    ThetaLowerSegment 561467648 561533184 (56143240208683 / 100000) (56149831996243 / 100000) := by
  exact
    packedTile32768 561467648 561533184 13 3272 23695 29 _ _ (402921 / 20000) (125913 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561533184 :
    ThetaLowerSegment 561533184 561598720 (56149831996243 / 100000) (56156460086173 / 100000) := by
  exact
    packedTile32768 561533184 561598720 13 3290 23696 29 _ _ (2014617 / 100000) (100731 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561598720 :
    ThetaLowerSegment 561598720 561664256 (56156460086173 / 100000) (11232611195649 / 20000) := by
  exact
    packedTile32768 561598720 561664256 13 3274 23698 29 _ _ (503657 / 25000) (2014631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561664256 :
    ThetaLowerSegment 561664256 561729792 (11232611195649 / 20000) (11233922726289 / 20000) := by
  exact
    packedTile32768 561664256 561729792 13 3255 23699 29 _ _ (25183 / 1250) (2014643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561729792 :
    ThetaLowerSegment 561729792 561795328 (11233922726289 / 20000) (11235240308697 / 20000) := by
  exact
    packedTile32768 561729792 561795328 13 3270 23700 29 _ _ (503663 / 25000) (402931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561795328 :
    ThetaLowerSegment 561795328 561860864 (11235240308697 / 20000) (56182692787671 / 100000) := by
  exact
    packedTile32768 561795328 561860864 13 3222 23702 29 _ _ (2014663 / 100000) (1007333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561860864 :
    ThetaLowerSegment 561860864 561926400 (56182692787671 / 100000) (56189308980371 / 100000) := by
  exact
    packedTile32768 561860864 561926400 13 3284 23703 29 _ _ (80587 / 4000) (1007339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561926400 :
    ThetaLowerSegment 561926400 561991936 (56189308980371 / 100000) (28098020024819 / 50000) := by
  exact
    packedTile32768 561926400 561991936 13 3341 23704 29 _ _ (2014687 / 100000) (201469 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell561991936 :
    ThetaLowerSegment 561991936 562057472 (28098020024819 / 50000) (14050637384719 / 25000) := by
  exact
    packedTile32768 561991936 562057472 13 3231 23706 29 _ _ (1007349 / 50000) (2014701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562057472 :
    ThetaLowerSegment 562057472 562123008 (14050637384719 / 25000) (7026155300687 / 12500) := by
  exact
    packedTile32768 562057472 562123008 13 3322 23707 29 _ _ (201471 / 10000) (2014713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562123008 :
    ThetaLowerSegment 562123008 562188544 (7026155300687 / 12500) (28107875986139 / 50000) := by
  exact
    packedTile32768 562123008 562188544 13 3231 23709 29 _ _ (1007361 / 50000) (80589 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562188544 :
    ThetaLowerSegment 562188544 562254080 (28107875986139 / 50000) (56222354252319 / 100000) := by
  exact
    packedTile32768 562188544 562254080 13 3277 23710 29 _ _ (2014733 / 100000) (125921 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562254080 :
    ThetaLowerSegment 562254080 562319616 (56222354252319 / 100000) (56228829642749 / 100000) := by
  exact
    packedTile32768 562254080 562319616 13 3214 23711 29 _ _ (402949 / 20000) (503687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562319616 :
    ThetaLowerSegment 562319616 562385152 (56228829642749 / 100000) (28117679735093 / 50000) := by
  exact
    packedTile32768 562319616 562385152 13 3241 23713 29 _ _ (2014757 / 100000) (50369 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562385152 :
    ThetaLowerSegment 562385152 562450688 (28117679735093 / 50000) (5624198402737 / 10000) := by
  exact
    packedTile32768 562385152 562450688 13 3288 23714 29 _ _ (125923 / 6250) (2014771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562450688 :
    ThetaLowerSegment 562450688 562516224 (5624198402737 / 10000) (5624854616583 / 10000) := by
  exact
    packedTile32768 562450688 562516224 13 3257 23716 29 _ _ (100739 / 5000) (2014783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562516224 :
    ThetaLowerSegment 562516224 562581760 (5624854616583 / 10000) (28127551149499 / 50000) := by
  exact
    packedTile32768 562516224 562581760 13 3254 23717 29 _ _ (251849 / 12500) (402959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562581760 :
    ThetaLowerSegment 562581760 562647296 (28127551149499 / 50000) (28130847367207 / 50000) := by
  exact
    packedTile32768 562581760 562647296 13 3272 23718 29 _ _ (2014803 / 100000) (1007403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562647296 :
    ThetaLowerSegment 562647296 562712832 (28130847367207 / 50000) (56268216690569 / 100000) := by
  exact
    packedTile32768 562647296 562712832 13 3237 23720 29 _ _ (402963 / 20000) (1007409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562712832 :
    ThetaLowerSegment 562712832 562778368 (56268216690569 / 100000) (56274690326507 / 100000) := by
  exact
    packedTile32768 562712832 562778368 13 3213 23721 29 _ _ (1007413 / 50000) (2014829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562778368 :
    ThetaLowerSegment 562778368 562843904 (56274690326507 / 100000) (56281097511347 / 100000) := by
  exact
    packedTile32768 562778368 562843904 13 3180 23722 29 _ _ (1007419 / 50000) (2014841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562843904 :
    ThetaLowerSegment 562843904 562909440 (56281097511347 / 100000) (56287718308447 / 100000) := by
  exact
    packedTile32768 562843904 562909440 13 3286 23724 29 _ _ (40297 / 2000) (2014853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562909440 :
    ThetaLowerSegment 562909440 562974976 (56287718308447 / 100000) (14073590326291 / 25000) := by
  exact
    packedTile32768 562909440 562974976 13 3297 23725 29 _ _ (2014861 / 100000) (125929 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell562974976 :
    ThetaLowerSegment 562974976 563040512 (14073590326291 / 25000) (56300960014239 / 100000) := by
  exact
    packedTile32768 562974976 563040512 13 3275 23727 29 _ _ (2014873 / 100000) (503719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563040512 :
    ThetaLowerSegment 563040512 563106048 (56300960014239 / 100000) (56307476152329 / 100000) := by
  exact
    packedTile32768 563040512 563106048 13 3234 23728 29 _ _ (402977 / 20000) (251861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563106048 :
    ThetaLowerSegment 563106048 563171584 (56307476152329 / 100000) (11262803300949 / 20000) := by
  exact
    packedTile32768 563106048 563171584 13 3246 23729 29 _ _ (125931 / 6250) (2014899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563171584 :
    ThetaLowerSegment 563171584 563237120 (11262803300949 / 20000) (56320502493597 / 100000) := by
  exact
    packedTile32768 563171584 563237120 13 3219 23731 29 _ _ (503727 / 25000) (2014911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563237120 :
    ThetaLowerSegment 563237120 563302656 (56320502493597 / 100000) (56327107401357 / 100000) := by
  exact
    packedTile32768 563237120 563302656 13 3278 23732 29 _ _ (50373 / 2500) (2014923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563302656 :
    ThetaLowerSegment 563302656 563368192 (56327107401357 / 100000) (56333696225727 / 100000) := by
  exact
    packedTile32768 563302656 563368192 13 3270 23733 29 _ _ (2014931 / 100000) (1007467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563368192 :
    ThetaLowerSegment 563368192 563433728 (56333696225727 / 100000) (56340248820363 / 100000) := by
  exact
    packedTile32768 563368192 563433728 13 3252 23735 29 _ _ (2014943 / 100000) (1007473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563433728 :
    ThetaLowerSegment 563433728 563499264 (56340248820363 / 100000) (1760838238079 / 3125) := by
  exact
    packedTile32768 563433728 563499264 13 3263 23736 29 _ _ (402991 / 20000) (1007479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563499264 :
    ThetaLowerSegment 563499264 563564800 (1760838238079 / 3125) (14088341049541 / 25000) := by
  exact
    packedTile32768 563499264 563564800 13 3246 23738 29 _ _ (1007483 / 50000) (2014969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563564800 :
    ThetaLowerSegment 563564800 563630336 (14088341049541 / 25000) (28179909086349 / 50000) := by
  exact
    packedTile32768 563564800 563630336 13 3203 23739 29 _ _ (1007489 / 50000) (2014981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563630336 :
    ThetaLowerSegment 563630336 563695872 (28179909086349 / 50000) (5636648375631 / 10000) := by
  exact
    packedTile32768 563630336 563695872 13 3308 23740 29 _ _ (2014989 / 100000) (125937 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563695872 :
    ThetaLowerSegment 563695872 563761408 (5636648375631 / 10000) (56373026464557 / 100000) := by
  exact
    packedTile32768 563695872 563761408 13 3247 23742 29 _ _ (2015001 / 100000) (503751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563761408 :
    ThetaLowerSegment 563761408 563826944 (56373026464557 / 100000) (3523722068229 / 6250) := by
  exact
    packedTile32768 563761408 563826944 13 3239 23743 29 _ _ (2015013 / 100000) (251877 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563826944 :
    ThetaLowerSegment 563826944 563892480 (3523722068229 / 6250) (5638613013 / 10) := by
  exact
    packedTile32768 563826944 563892480 13 3264 23745 29 _ _ (125939 / 6250) (2015027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563892480 :
    ThetaLowerSegment 563892480 563958016 (5638613013 / 10) (7049091927251 / 12500) := by
  exact
    packedTile32768 563892480 563958016 13 3278 23746 29 _ _ (503759 / 25000) (2015039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell563958016 :
    ThetaLowerSegment 563958016 564023552 (7049091927251 / 12500) (1762476060869 / 3125) := by
  exact
    packedTile32768 563958016 564023552 13 3225 23747 29 _ _ (251881 / 12500) (2015051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564023552 :
    ThetaLowerSegment 564023552 564089088 (1762476060869 / 3125) (56405813115443 / 100000) := by
  exact
    packedTile32768 564023552 564089088 13 3265 23749 29 _ _ (2015059 / 100000) (1007531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564089088 :
    ThetaLowerSegment 564089088 564154624 (56405813115443 / 100000) (2820617802549 / 5000) := by
  exact
    packedTile32768 564089088 564154624 13 3247 23750 29 _ _ (2015071 / 100000) (1007537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564154624 :
    ThetaLowerSegment 564154624 564220160 (2820617802549 / 5000) (28209423315051 / 50000) := by
  exact
    packedTile32768 564154624 564220160 13 3221 23751 29 _ _ (1007541 / 50000) (403017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564220160 :
    ThetaLowerSegment 564220160 564285696 (28209423315051 / 50000) (14106340357251 / 25000) := by
  exact
    packedTile32768 564220160 564285696 13 3233 23753 29 _ _ (1007547 / 50000) (2015097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564285696 :
    ThetaLowerSegment 564285696 564351232 (14106340357251 / 25000) (28215944178669 / 50000) := by
  exact
    packedTile32768 564285696 564351232 13 3239 23754 29 _ _ (1007553 / 50000) (2015109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564351232 :
    ThetaLowerSegment 564351232 564416768 (28215944178669 / 50000) (11287679840073 / 20000) := by
  exact
    packedTile32768 564351232 564416768 13 3231 23756 29 _ _ (2015117 / 100000) (25189 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564416768 :
    ThetaLowerSegment 564416768 564482304 (11287679840073 / 20000) (90311723939 / 160) := by
  exact
    packedTile32768 564416768 564482304 13 3190 23757 29 _ _ (2015129 / 100000) (503783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564482304 :
    ThetaLowerSegment 564482304 564547840 (90311723939 / 160) (11290278960627 / 20000) := by
  exact
    packedTile32768 564482304 564547840 13 3259 23758 29 _ _ (100757 / 5000) (2015143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564547840 :
    ThetaLowerSegment 564547840 564613376 (11290278960627 / 20000) (56457909789551 / 100000) := by
  exact
    packedTile32768 564547840 564613376 13 3233 23760 29 _ _ (125947 / 6250) (403031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564613376 :
    ThetaLowerSegment 564613376 564678912 (56457909789551 / 100000) (56464686786083 / 100000) := by
  exact
    packedTile32768 564613376 564678912 13 3363 23761 29 _ _ (503791 / 25000) (2015167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564678912 :
    ThetaLowerSegment 564678912 564744448 (56464686786083 / 100000) (56471111163983 / 100000) := by
  exact
    packedTile32768 564678912 564744448 13 3188 23762 29 _ _ (80607 / 4000) (1007589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564744448 :
    ThetaLowerSegment 564744448 564809984 (56471111163983 / 100000) (56477725007717 / 100000) := by
  exact
    packedTile32768 564744448 564809984 13 3282 23764 29 _ _ (2015187 / 100000) (201519 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564809984 :
    ThetaLowerSegment 564809984 564875520 (56477725007717 / 100000) (56484258279633 / 100000) := by
  exact
    packedTile32768 564809984 564875520 13 3242 23765 29 _ _ (1007599 / 50000) (2015201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564875520 :
    ThetaLowerSegment 564875520 564941056 (56484258279633 / 100000) (56490856077173 / 100000) := by
  exact
    packedTile32768 564875520 564941056 13 3274 23767 29 _ _ (201521 / 10000) (2015213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell564941056 :
    ThetaLowerSegment 564941056 565006592 (56490856077173 / 100000) (56497463990111 / 100000) := by
  exact
    packedTile32768 564941056 565006592 13 3279 23768 29 _ _ (1007611 / 50000) (80609 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565006592 :
    ThetaLowerSegment 565006592 565072128 (56497463990111 / 100000) (56503944979439 / 100000) := by
  exact
    packedTile32768 565006592 565072128 13 3216 23769 29 _ _ (2015233 / 100000) (503809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565072128 :
    ThetaLowerSegment 565072128 565137664 (56503944979439 / 100000) (14127647310551 / 25000) := by
  exact
    packedTile32768 565072128 565137664 13 3297 23771 29 _ _ (403049 / 20000) (125953 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565137664 :
    ThetaLowerSegment 565137664 565203200 (14127647310551 / 25000) (14129278156469 / 25000) := by
  exact
    packedTile32768 565137664 565203200 13 3237 23772 29 _ _ (251907 / 12500) (2015259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565203200 :
    ThetaLowerSegment 565203200 565268736 (14129278156469 / 25000) (3532731535469 / 6250) := by
  exact
    packedTile32768 565203200 565268736 13 3271 23774 29 _ _ (503817 / 25000) (2015271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565268736 :
    ThetaLowerSegment 565268736 565334272 (3532731535469 / 6250) (3533144415959 / 6250) := by
  exact
    packedTile32768 565268736 565334272 13 3278 23775 29 _ _ (25191 / 1250) (2015283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565334272 :
    ThetaLowerSegment 565334272 565399808 (3533144415959 / 6250) (28268373747399 / 50000) := by
  exact
    packedTile32768 565334272 565399808 13 3194 23776 29 _ _ (2015291 / 100000) (1007647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565399808 :
    ThetaLowerSegment 565399808 565465344 (28268373747399 / 50000) (56543299244851 / 100000) := by
  exact
    packedTile32768 565399808 565465344 13 3251 23778 29 _ _ (2015303 / 100000) (1007653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565465344 :
    ThetaLowerSegment 565465344 565530880 (56543299244851 / 100000) (56549842969409 / 100000) := by
  exact
    packedTile32768 565465344 565530880 13 3247 23779 29 _ _ (1007657 / 50000) (2015317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565530880 :
    ThetaLowerSegment 565530880 565596416 (56549842969409 / 100000) (56556328288477 / 100000) := by
  exact
    packedTile32768 565530880 565596416 13 3218 23780 29 _ _ (1007663 / 50000) (2015329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565596416 :
    ThetaLowerSegment 565596416 565661952 (56556328288477 / 100000) (56562908367047 / 100000) := by
  exact
    packedTile32768 565596416 565661952 13 3265 23782 29 _ _ (1007669 / 50000) (2015341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565661952 :
    ThetaLowerSegment 565661952 565727488 (56562908367047 / 100000) (14142343905497 / 25000) := by
  exact
    packedTile32768 565661952 565727488 13 3209 23783 29 _ _ (2015349 / 100000) (251919 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565727488 :
    ThetaLowerSegment 565727488 565793024 (14142343905497 / 25000) (11315200022719 / 20000) := by
  exact
    packedTile32768 565727488 565793024 13 3287 23785 29 _ _ (2015361 / 100000) (503841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565793024 :
    ThetaLowerSegment 565793024 565858560 (11315200022719 / 20000) (56582642779707 / 100000) := by
  exact
    packedTile32768 565793024 565858560 13 3296 23786 29 _ _ (503843 / 25000) (16123 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565858560 :
    ThetaLowerSegment 565858560 565924096 (56582642779707 / 100000) (56589124254651 / 100000) := by
  exact
    packedTile32768 565858560 565924096 13 3216 23787 29 _ _ (251923 / 12500) (2015387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565924096 :
    ThetaLowerSegment 565924096 565989632 (56589124254651 / 100000) (56595688399423 / 100000) := by
  exact
    packedTile32768 565924096 565989632 13 3257 23789 29 _ _ (503849 / 25000) (2015399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell565989632 :
    ThetaLowerSegment 565989632 566055168 (56595688399423 / 100000) (1415057019893 / 2500) := by
  exact
    packedTile32768 565989632 566055168 13 3271 23790 29 _ _ (2015407 / 100000) (201541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566055168 :
    ThetaLowerSegment 566055168 566120704 (1415057019893 / 2500) (14152196642063 / 25000) := by
  exact
    packedTile32768 566055168 566120704 13 3228 23791 29 _ _ (2015419 / 100000) (1007711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566120704 :
    ThetaLowerSegment 566120704 566186240 (14152196642063 / 25000) (28307641149571 / 50000) := by
  exact
    packedTile32768 566120704 566186240 13 3223 23793 29 _ _ (201543 / 10000) (2015433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566186240 :
    ThetaLowerSegment 566186240 566251776 (28307641149571 / 50000) (7077734855101 / 12500) := by
  exact
    packedTile32768 566186240 566251776 13 3273 23794 29 _ _ (1007721 / 50000) (403089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566251776 :
    ThetaLowerSegment 566251776 566317312 (7077734855101 / 12500) (56628439140323 / 100000) := by
  exact
    packedTile32768 566251776 566317312 13 3255 23796 29 _ _ (2015453 / 100000) (62983 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566317312 :
    ThetaLowerSegment 566317312 566382848 (56628439140323 / 100000) (56634993432503 / 100000) := by
  exact
    packedTile32768 566317312 566382848 13 3252 23797 29 _ _ (403093 / 20000) (503867 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566382848 :
    ThetaLowerSegment 566382848 566448384 (56634993432503 / 100000) (28320776905069 / 50000) := by
  exact
    packedTile32768 566382848 566448384 13 3255 23798 29 _ _ (2015477 / 100000) (50387 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566448384 :
    ThetaLowerSegment 566448384 566513920 (28320776905069 / 50000) (28324006724589 / 50000) := by
  exact
    packedTile32768 566448384 566513920 13 3205 23800 29 _ _ (62984 / 3125) (2015491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566513920 :
    ThetaLowerSegment 566513920 566579456 (28324006724589 / 50000) (28327332299589 / 50000) := by
  exact
    packedTile32768 566513920 566579456 13 3300 23801 29 _ _ (4031 / 200) (2015503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566579456 :
    ThetaLowerSegment 566579456 566644992 (28327332299589 / 50000) (56661273459747 / 100000) := by
  exact
    packedTile32768 566579456 566644992 13 3279 23802 29 _ _ (2015511 / 100000) (1007757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566644992 :
    ThetaLowerSegment 566644992 566710528 (56661273459747 / 100000) (7083479248389 / 12500) := by
  exact
    packedTile32768 566644992 566710528 13 3255 23804 29 _ _ (2015523 / 100000) (1007763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566710528 :
    ThetaLowerSegment 566710528 566776064 (7083479248389 / 12500) (1771071617439 / 3125) := by
  exact
    packedTile32768 566710528 566776064 13 3204 23805 29 _ _ (1007767 / 50000) (2015537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566776064 :
    ThetaLowerSegment 566776064 566841600 (1771071617439 / 3125) (7085079587107 / 12500) := by
  exact
    packedTile32768 566776064 566841600 13 3148 23807 29 _ _ (1007773 / 50000) (2015549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566841600 :
    ThetaLowerSegment 566841600 566907136 (7085079587107 / 12500) (1133745478587 / 2000) := by
  exact
    packedTile32768 566841600 566907136 13 3293 23808 29 _ _ (1007779 / 50000) (2015561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566907136 :
    ThetaLowerSegment 566907136 566972672 (1133745478587 / 2000) (28346954591249 / 50000) := by
  exact
    packedTile32768 566907136 566972672 13 3292 23809 29 _ _ (2015569 / 100000) (503893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell566972672 :
    ThetaLowerSegment 566972672 567038208 (28346954591249 / 50000) (11340110910611 / 20000) := by
  exact
    packedTile32768 566972672 567038208 13 3297 23811 29 _ _ (2015581 / 100000) (62987 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567038208 :
    ThetaLowerSegment 567038208 567103744 (11340110910611 / 20000) (2268287030911 / 4000) := by
  exact
    packedTile32768 567038208 567103744 13 3285 23812 29 _ _ (251949 / 12500) (403119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567103744 :
    ThetaLowerSegment 567103744 567169280 (2268287030911 / 4000) (56713688189299 / 100000) := by
  exact
    packedTile32768 567103744 567169280 13 3231 23813 29 _ _ (503901 / 25000) (2015607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567169280 :
    ThetaLowerSegment 567169280 567234816 (56713688189299 / 100000) (28360066055227 / 50000) := by
  exact
    packedTile32768 567169280 567234816 13 3197 23815 29 _ _ (403123 / 20000) (1007809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567234816 :
    ThetaLowerSegment 567234816 567300352 (28360066055227 / 50000) (28363327339713 / 50000) := by
  exact
    packedTile32768 567234816 567300352 13 3236 23816 29 _ _ (2015627 / 100000) (201563 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567300352 :
    ThetaLowerSegment 567300352 567365888 (28363327339713 / 50000) (28366562438703 / 50000) := by
  exact
    packedTile32768 567300352 567365888 13 3210 23818 29 _ _ (1007819 / 50000) (2015641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567365888 :
    ThetaLowerSegment 567365888 567431424 (28366562438703 / 50000) (14184935564089 / 25000) := by
  exact
    packedTile32768 567365888 567431424 13 3283 23819 29 _ _ (40313 / 2000) (2015653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567431424 :
    ThetaLowerSegment 567431424 567496960 (14184935564089 / 25000) (28373177821689 / 50000) := by
  exact
    packedTile32768 567431424 567496960 13 3281 23820 29 _ _ (1007831 / 50000) (403133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567496960 :
    ThetaLowerSegment 567496960 567562496 (28373177821689 / 50000) (5675285417313 / 10000) := by
  exact
    packedTile32768 567496960 567562496 13 3224 23822 29 _ _ (2015673 / 100000) (503919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567562496 :
    ThetaLowerSegment 567562496 567628032 (5675285417313 / 10000) (1418986136577 / 2500) := by
  exact
    packedTile32768 567562496 567628032 13 3270 23823 29 _ _ (403137 / 20000) (251961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567628032 :
    ThetaLowerSegment 567628032 567693568 (1418986136577 / 2500) (7095742252487 / 12500) := by
  exact
    packedTile32768 567628032 567693568 13 3221 23824 29 _ _ (125981 / 6250) (2015699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567693568 :
    ThetaLowerSegment 567693568 567759104 (7095742252487 / 12500) (7096578771307 / 12500) := by
  exact
    packedTile32768 567693568 567759104 13 3320 23826 29 _ _ (503927 / 25000) (2015711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567759104 :
    ThetaLowerSegment 567759104 567824640 (7096578771307 / 12500) (56779146989983 / 100000) := by
  exact
    packedTile32768 567759104 567824640 13 3233 23827 29 _ _ (2015719 / 100000) (1007861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567824640 :
    ThetaLowerSegment 567824640 567890176 (56779146989983 / 100000) (56785637643803 / 100000) := by
  exact
    packedTile32768 567824640 567890176 13 3220 23829 29 _ _ (2015731 / 100000) (1007867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567890176 :
    ThetaLowerSegment 567890176 567955712 (56785637643803 / 100000) (56792156553431 / 100000) := by
  exact
    packedTile32768 567890176 567955712 13 3234 23830 29 _ _ (1007871 / 50000) (403149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell567955712 :
    ThetaLowerSegment 567955712 568021248 (56792156553431 / 100000) (56798786368337 / 100000) := by
  exact
    packedTile32768 567955712 568021248 13 3289 23831 29 _ _ (1007877 / 50000) (2015757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568021248 :
    ThetaLowerSegment 568021248 568086784 (56798786368337 / 100000) (3550335742037 / 6250) := by
  exact
    packedTile32768 568021248 568086784 13 3267 23833 29 _ _ (403153 / 20000) (251971 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568086784 :
    ThetaLowerSegment 568086784 568152320 (3550335742037 / 6250) (56811985636929 / 100000) := by
  exact
    packedTile32768 568086784 568152320 13 3281 23834 29 _ _ (2015777 / 100000) (100789 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568152320 :
    ThetaLowerSegment 568152320 568217856 (56811985636929 / 100000) (14204636757531 / 25000) := by
  exact
    packedTile32768 568152320 568217856 13 3255 23835 29 _ _ (2015789 / 100000) (125987 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568217856 :
    ThetaLowerSegment 568217856 568283392 (14204636757531 / 25000) (14206273587131 / 25000) := by
  exact
    packedTile32768 568217856 568283392 13 3248 23837 29 _ _ (10079 / 500) (2015803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568283392 :
    ThetaLowerSegment 568283392 568348928 (14206273587131 / 25000) (7103961008697 / 12500) := by
  exact
    packedTile32768 568283392 568348928 13 3271 23838 29 _ _ (503953 / 25000) (403163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568348928 :
    ThetaLowerSegment 568348928 568414464 (7103961008697 / 12500) (56838152813937 / 100000) := by
  exact
    packedTile32768 568348928 568414464 13 3207 23840 29 _ _ (2015823 / 100000) (1007913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568414464 :
    ThetaLowerSegment 568414464 568480000 (56838152813937 / 100000) (28422381368451 / 50000) := by
  exact
    packedTile32768 568414464 568480000 13 3279 23841 29 _ _ (403167 / 20000) (1007919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568480000 :
    ThetaLowerSegment 568480000 568545536 (28422381368451 / 50000) (3553205753881 / 6250) := by
  exact
    packedTile32768 568480000 568545536 13 3239 23842 29 _ _ (1007923 / 50000) (2015849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568545536 :
    ThetaLowerSegment 568545536 568611072 (3553205753881 / 6250) (14214483074587 / 25000) := by
  exact
    packedTile32768 568545536 568611072 13 3294 23844 29 _ _ (1007929 / 50000) (2015861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568611072 :
    ThetaLowerSegment 568611072 568676608 (14214483074587 / 25000) (56864433475873 / 100000) := by
  exact
    packedTile32768 568611072 568676608 13 3225 23845 29 _ _ (2015869 / 100000) (62996 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568676608 :
    ThetaLowerSegment 568676608 568742144 (56864433475873 / 100000) (56870977025599 / 100000) := by
  exact
    packedTile32768 568676608 568742144 13 3246 23846 29 _ _ (2015881 / 100000) (503971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568742144 :
    ThetaLowerSegment 568742144 568807680 (56870977025599 / 100000) (56877415784647 / 100000) := by
  exact
    packedTile32768 568742144 568807680 13 3194 23848 29 _ _ (503973 / 25000) (403179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568807680 :
    ThetaLowerSegment 568807680 568873216 (56877415784647 / 100000) (56884054156519 / 100000) := by
  exact
    packedTile32768 568807680 568873216 13 3293 23849 29 _ _ (62997 / 3125) (2015907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568873216 :
    ThetaLowerSegment 568873216 568938752 (56884054156519 / 100000) (14222645926301 / 25000) := by
  exact
    packedTile32768 568873216 568938752 13 3239 23851 29 _ _ (403183 / 20000) (1007959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell568938752 :
    ThetaLowerSegment 568938752 569004288 (14222645926301 / 25000) (56897286662479 / 100000) := by
  exact
    packedTile32768 568938752 569004288 13 3325 23852 29 _ _ (2015927 / 100000) (201593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569004288 :
    ThetaLowerSegment 569004288 569069824 (56897286662479 / 100000) (56903828381289 / 100000) := by
  exact
    packedTile32768 569004288 569069824 13 3245 23853 29 _ _ (1007969 / 50000) (2015941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569069824 :
    ThetaLowerSegment 569069824 569135360 (56903828381289 / 100000) (56910388282589 / 100000) := by
  exact
    packedTile32768 569069824 569135360 13 3254 23855 29 _ _ (40319 / 2000) (2015953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569135360 :
    ThetaLowerSegment 569135360 569200896 (56910388282589 / 100000) (3557307877757 / 6250) := by
  exact
    packedTile32768 569135360 569200896 13 3243 23856 29 _ _ (2015961 / 100000) (503991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569200896 :
    ThetaLowerSegment 569200896 569266432 (3557307877757 / 6250) (455387517223 / 800) := by
  exact
    packedTile32768 569200896 569266432 13 3231 23857 29 _ _ (2015973 / 100000) (251997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569266432 :
    ThetaLowerSegment 569266432 569331968 (455387517223 / 800) (56929945233243 / 100000) := by
  exact
    packedTile32768 569266432 569331968 13 3227 23859 29 _ _ (125999 / 6250) (2015987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569331968 :
    ThetaLowerSegment 569331968 569397504 (56929945233243 / 100000) (56936513348211 / 100000) := by
  exact
    packedTile32768 569331968 569397504 13 3258 23860 29 _ _ (503999 / 25000) (2015999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569397504 :
    ThetaLowerSegment 569397504 569463040 (56936513348211 / 100000) (56943057306933 / 100000) := by
  exact
    packedTile32768 569397504 569463040 13 3246 23862 29 _ _ (2016007 / 100000) (201601 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569463040 :
    ThetaLowerSegment 569463040 569528576 (56943057306933 / 100000) (3559351467551 / 6250) := by
  exact
    packedTile32768 569463040 569528576 13 3257 23863 29 _ _ (2016019 / 100000) (1008011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569528576 :
    ThetaLowerSegment 569528576 569594112 (3559351467551 / 6250) (1779881872843 / 3125) := by
  exact
    packedTile32768 569528576 569594112 13 3272 23864 29 _ _ (201603 / 10000) (2016033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569594112 :
    ThetaLowerSegment 569594112 569659648 (1779881872843 / 3125) (14240695032911 / 25000) := by
  exact
    packedTile32768 569594112 569659648 13 3254 23866 29 _ _ (1008021 / 50000) (403209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569659648 :
    ThetaLowerSegment 569659648 569725184 (14240695032911 / 25000) (56969318191523 / 100000) := by
  exact
    packedTile32768 569659648 569725184 13 3243 23867 29 _ _ (2016053 / 100000) (252007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569725184 :
    ThetaLowerSegment 569725184 569790720 (56969318191523 / 100000) (56975668796273 / 100000) := by
  exact
    packedTile32768 569725184 569790720 13 3150 23868 29 _ _ (403213 / 20000) (504017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569790720 :
    ThetaLowerSegment 569790720 569856256 (56975668796273 / 100000) (56982287573781 / 100000) := by
  exact
    packedTile32768 569790720 569856256 13 3283 23870 29 _ _ (504019 / 25000) (2016079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569856256 :
    ThetaLowerSegment 569856256 569921792 (56982287573781 / 100000) (56988696717533 / 100000) := by
  exact
    packedTile32768 569856256 569921792 13 3179 23871 29 _ _ (252011 / 12500) (2016091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569921792 :
    ThetaLowerSegment 569921792 569987328 (56988696717533 / 100000) (14248809739697 / 25000) := by
  exact
    packedTile32768 569921792 569987328 13 3245 23873 29 _ _ (2016099 / 100000) (1008051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell569987328 :
    ThetaLowerSegment 569987328 570052864 (14248809739697 / 25000) (1781309128909 / 3125) := by
  exact
    packedTile32768 569987328 570052864 13 3300 23874 29 _ _ (2016111 / 100000) (1008057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570052864 :
    ThetaLowerSegment 570052864 570118400 (1781309128909 / 3125) (1781514773353 / 3125) := by
  exact
    packedTile32768 570052864 570118400 13 3264 23875 29 _ _ (1008061 / 50000) (16129 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570118400 :
    ThetaLowerSegment 570118400 570183936 (1781514773353 / 3125) (28507527712403 / 50000) := by
  exact
    packedTile32768 570118400 570183936 13 3265 23877 29 _ _ (1008067 / 50000) (2016137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570183936 :
    ThetaLowerSegment 570183936 570249472 (28507527712403 / 50000) (14255395925579 / 25000) := by
  exact
    packedTile32768 570183936 570249472 13 3238 23878 29 _ _ (403229 / 20000) (504037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570249472 :
    ThetaLowerSegment 570249472 570315008 (14255395925579 / 25000) (11405617968191 / 20000) := by
  exact
    packedTile32768 570249472 570315008 13 3227 23879 29 _ _ (2016157 / 100000) (12601 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570315008 :
    ThetaLowerSegment 570315008 570380544 (11405617968191 / 20000) (57034640370787 / 100000) := by
  exact
    packedTile32768 570315008 570380544 13 3249 23881 29 _ _ (252021 / 12500) (2016171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570380544 :
    ThetaLowerSegment 570380544 570446080 (57034640370787 / 100000) (57041126421847 / 100000) := by
  exact
    packedTile32768 570380544 570446080 13 3217 23882 29 _ _ (100809 / 5000) (2016183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570446080 :
    ThetaLowerSegment 570446080 570511616 (57041126421847 / 100000) (11409530969661 / 20000) := by
  exact
    packedTile32768 570446080 570511616 13 3238 23884 29 _ _ (2016191 / 100000) (1008097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570511616 :
    ThetaLowerSegment 570511616 570577152 (11409530969661 / 20000) (7131780726989 / 12500) := by
  exact
    packedTile32768 570511616 570577152 13 3269 23885 29 _ _ (2016203 / 100000) (1008103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570577152 :
    ThetaLowerSegment 570577152 570642688 (7131780726989 / 12500) (5706085294919 / 10000) := by
  exact
    packedTile32768 570577152 570642688 13 3277 23886 29 _ _ (1008107 / 50000) (2016217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570642688 :
    ThetaLowerSegment 570642688 570708224 (5706085294919 / 10000) (356671222516 / 625) := by
  exact
    packedTile32768 570642688 570708224 13 3245 23888 29 _ _ (1008113 / 50000) (2016229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570708224 :
    ThetaLowerSegment 570708224 570773760 (356671222516 / 625) (57073914096781 / 100000) := by
  exact
    packedTile32768 570708224 570773760 13 3233 23889 29 _ _ (2016237 / 100000) (25203 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570773760 :
    ThetaLowerSegment 570773760 570839296 (57073914096781 / 100000) (5708040843481 / 10000) := by
  exact
    packedTile32768 570773760 570839296 13 3221 23890 29 _ _ (2016249 / 100000) (504063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570839296 :
    ThetaLowerSegment 570839296 570904832 (5708040843481 / 10000) (5708700362127 / 10000) := by
  exact
    packedTile32768 570839296 570904832 13 3271 23892 29 _ _ (100813 / 5000) (2016263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570904832 :
    ThetaLowerSegment 570904832 570970368 (5708700362127 / 10000) (28546772203819 / 50000) := by
  exact
    packedTile32768 570904832 570970368 13 3244 23893 29 _ _ (126017 / 6250) (80651 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell570970368 :
    ThetaLowerSegment 570970368 571035904 (28546772203819 / 50000) (57100111441369 / 100000) := by
  exact
    packedTile32768 570970368 571035904 13 3257 23894 29 _ _ (2016283 / 100000) (1008143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571035904 :
    ThetaLowerSegment 571035904 571101440 (57100111441369 / 100000) (57106656334939 / 100000) := by
  exact
    packedTile32768 571035904 571101440 13 3246 23896 29 _ _ (403259 / 20000) (1008149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571101440 :
    ThetaLowerSegment 571101440 571166976 (57106656334939 / 100000) (57113195215297 / 100000) := by
  exact
    packedTile32768 571101440 571166976 13 3243 23897 29 _ _ (1008153 / 50000) (2016309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571166976 :
    ThetaLowerSegment 571166976 571232512 (57113195215297 / 100000) (11423952069341 / 20000) := by
  exact
    packedTile32768 571166976 571232512 13 3256 23899 29 _ _ (1008159 / 50000) (2016321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571232512 :
    ThetaLowerSegment 571232512 571298048 (11423952069341 / 20000) (57126196468873 / 100000) := by
  exact
    packedTile32768 571232512 571298048 13 3192 23900 29 _ _ (2016329 / 100000) (504083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571298048 :
    ThetaLowerSegment 571298048 571363584 (57126196468873 / 100000) (14283214110799 / 25000) := by
  exact
    packedTile32768 571298048 571363584 13 3303 23901 29 _ _ (2016341 / 100000) (252043 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571363584 :
    ThetaLowerSegment 571363584 571429120 (14283214110799 / 25000) (14284845339567 / 25000) := by
  exact
    packedTile32768 571363584 571429120 13 3236 23903 29 _ _ (63011 / 3125) (403271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571429120 :
    ThetaLowerSegment 571429120 571494656 (14284845339567 / 25000) (14286479602589 / 25000) := by
  exact
    packedTile32768 571429120 571494656 13 3242 23904 29 _ _ (504091 / 25000) (2016367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571494656 :
    ThetaLowerSegment 571494656 571560192 (14286479602589 / 25000) (14288104800839 / 25000) := by
  exact
    packedTile32768 571494656 571560192 13 3224 23905 29 _ _ (16131 / 800) (1008189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571560192 :
    ThetaLowerSegment 571560192 571625728 (14288104800839 / 25000) (57159034969103 / 100000) := by
  exact
    packedTile32768 571560192 571625728 13 3281 23907 29 _ _ (2016387 / 100000) (201639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571625728 :
    ThetaLowerSegment 571625728 571691264 (57159034969103 / 100000) (11433129347629 / 20000) := by
  exact
    packedTile32768 571625728 571691264 13 3279 23908 29 _ _ (1008199 / 50000) (2016401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571691264 :
    ThetaLowerSegment 571691264 571756800 (11433129347629 / 20000) (11434444046297 / 20000) := by
  exact
    packedTile32768 571691264 571756800 13 3260 23910 29 _ _ (2016409 / 100000) (504103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571756800 :
    ThetaLowerSegment 571756800 571822336 (11434444046297 / 20000) (2858933134829 / 5000) := by
  exact
    packedTile32768 571756800 571822336 13 3195 23911 29 _ _ (2016421 / 100000) (252053 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571822336 :
    ThetaLowerSegment 571822336 571887872 (2858933134829 / 5000) (14296303521037 / 25000) := by
  exact
    packedTile32768 571822336 571887872 13 3249 23912 29 _ _ (126027 / 6250) (403287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571887872 :
    ThetaLowerSegment 571887872 571953408 (14296303521037 / 25000) (14297939865343 / 25000) := by
  exact
    packedTile32768 571887872 571953408 13 3246 23914 29 _ _ (504111 / 25000) (2016447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell571953408 :
    ThetaLowerSegment 571953408 572018944 (14297939865343 / 25000) (14299577226803 / 25000) := by
  exact
    packedTile32768 571953408 572018944 13 3248 23915 29 _ _ (403291 / 20000) (1008229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572018944 :
    ThetaLowerSegment 572018944 572084480 (14299577226803 / 25000) (57204844276759 / 100000) := by
  exact
    packedTile32768 572018944 572084480 13 3241 23916 29 _ _ (2016467 / 100000) (201647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572084480 :
    ThetaLowerSegment 572084480 572150016 (57204844276759 / 100000) (57211426060951 / 100000) := by
  exact
    packedTile32768 572084480 572150016 13 3264 23918 29 _ _ (1008239 / 50000) (2016481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572150016 :
    ThetaLowerSegment 572150016 572215552 (57211426060951 / 100000) (57218001834841 / 100000) := by
  exact
    packedTile32768 572150016 572215552 13 3261 23919 29 _ _ (201649 / 10000) (2016493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572215552 :
    ThetaLowerSegment 572215552 572281088 (57218001834841 / 100000) (14306109122383 / 25000) := by
  exact
    packedTile32768 572215552 572281088 13 3191 23921 29 _ _ (2016501 / 100000) (252063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572281088 :
    ThetaLowerSegment 572281088 572346624 (14306109122383 / 25000) (28615543474703 / 50000) := by
  exact
    packedTile32768 572281088 572346624 13 3298 23922 29 _ _ (2016513 / 100000) (504129 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572346624 :
    ThetaLowerSegment 572346624 572412160 (28615543474703 / 50000) (28618961482883 / 50000) := by
  exact
    packedTile32768 572346624 572412160 13 3390 23923 29 _ _ (504131 / 25000) (2016527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572412160 :
    ThetaLowerSegment 572412160 572477696 (28618961482883 / 50000) (57244422258071 / 100000) := by
  exact
    packedTile32768 572412160 572477696 13 3223 23925 29 _ _ (403307 / 20000) (1008269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572477696 :
    ThetaLowerSegment 572477696 572543232 (57244422258071 / 100000) (57250967969633 / 100000) := by
  exact
    packedTile32768 572477696 572543232 13 3246 23926 29 _ _ (2016547 / 100000) (40331 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572543232 :
    ThetaLowerSegment 572543232 572608768 (57250967969633 / 100000) (57257592362663 / 100000) := by
  exact
    packedTile32768 572543232 572608768 13 3285 23927 29 _ _ (1008279 / 50000) (2016561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572608768 :
    ThetaLowerSegment 572608768 572674304 (57257592362663 / 100000) (57264029254103 / 100000) := by
  exact
    packedTile32768 572608768 572674304 13 3192 23929 29 _ _ (201657 / 10000) (2016573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572674304 :
    ThetaLowerSegment 572674304 572739840 (57264029254103 / 100000) (57270514578599 / 100000) := by
  exact
    packedTile32768 572674304 572739840 13 3216 23930 29 _ _ (2016581 / 100000) (252073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572739840 :
    ThetaLowerSegment 572739840 572805376 (57270514578599 / 100000) (11455422574179 / 20000) := by
  exact
    packedTile32768 572739840 572805376 13 3272 23931 29 _ _ (2016593 / 100000) (504149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572805376 :
    ThetaLowerSegment 572805376 572870912 (11455422574179 / 20000) (57283769680699 / 100000) := by
  exact
    packedTile32768 572805376 572870912 13 3301 23933 29 _ _ (504151 / 25000) (2016607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572870912 :
    ThetaLowerSegment 572870912 572936448 (57283769680699 / 100000) (57290263184219 / 100000) := by
  exact
    packedTile32768 572870912 572936448 13 3220 23934 29 _ _ (252077 / 12500) (2016619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell572936448 :
    ThetaLowerSegment 572936448 573001984 (57290263184219 / 100000) (57296736556889 / 100000) := by
  exact
    packedTile32768 572936448 573001984 13 3210 23936 29 _ _ (2016627 / 100000) (201663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573001984 :
    ThetaLowerSegment 573001984 573067520 (57296736556889 / 100000) (57303401545479 / 100000) := by
  exact
    packedTile32768 573001984 573067520 13 3305 23937 29 _ _ (1008319 / 50000) (2016641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573067520 :
    ThetaLowerSegment 573067520 573133056 (57303401545479 / 100000) (57309949608029 / 100000) := by
  exact
    packedTile32768 573067520 573133056 13 3247 23938 29 _ _ (40333 / 2000) (2016653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573133056 :
    ThetaLowerSegment 573133056 573198592 (57309949608029 / 100000) (7164562213287 / 12500) := by
  exact
    packedTile32768 573133056 573198592 13 3247 23940 29 _ _ (2016661 / 100000) (252083 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573198592 :
    ThetaLowerSegment 573198592 573264128 (7164562213287 / 12500) (1791346758136 / 3125) := by
  exact
    packedTile32768 573198592 573264128 13 3272 23941 29 _ _ (2016673 / 100000) (504169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573264128 :
    ThetaLowerSegment 573264128 573329664 (1791346758136 / 3125) (3583102398953 / 6250) := by
  exact
    packedTile32768 573264128 573329664 13 3244 23942 29 _ _ (504171 / 25000) (2016687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573329664 :
    ThetaLowerSegment 573329664 573395200 (3583102398953 / 6250) (1791755011816 / 3125) := by
  exact
    packedTile32768 573329664 573395200 13 3234 23944 29 _ _ (252087 / 12500) (2016699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573395200 :
    ThetaLowerSegment 573395200 573460736 (1791755011816 / 3125) (28671397672071 / 50000) := by
  exact
    packedTile32768 573395200 573460736 13 3290 23945 29 _ _ (2016707 / 100000) (201671 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573460736 :
    ThetaLowerSegment 573460736 573526272 (28671397672071 / 50000) (5734939404871 / 10000) := by
  exact
    packedTile32768 573460736 573526272 13 3272 23947 29 _ _ (2016719 / 100000) (1008361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573526272 :
    ThetaLowerSegment 573526272 573591808 (5734939404871 / 10000) (5735595648813 / 10000) := by
  exact
    packedTile32768 573526272 573591808 13 3254 23948 29 _ _ (201673 / 10000) (2016733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573591808 :
    ThetaLowerSegment 573591808 573657344 (5735595648813 / 10000) (57362504846157 / 100000) := by
  exact
    packedTile32768 573591808 573657344 13 3247 23949 29 _ _ (2016741 / 100000) (252093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573657344 :
    ThetaLowerSegment 573657344 573722880 (57362504846157 / 100000) (14342251210269 / 25000) := by
  exact
    packedTile32768 573657344 573722880 13 3223 23951 29 _ _ (2016753 / 100000) (504189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573722880 :
    ThetaLowerSegment 573722880 573788416 (14342251210269 / 25000) (717195273047 / 1250) := by
  exact
    packedTile32768 573722880 573788416 13 3281 23952 29 _ _ (504191 / 25000) (2016767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573788416 :
    ThetaLowerSegment 573788416 573853952 (717195273047 / 1250) (358638602286 / 625) := by
  exact
    packedTile32768 573788416 573853952 13 3250 23953 29 _ _ (252097 / 12500) (2016779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573853952 :
    ThetaLowerSegment 573853952 573919488 (358638602286 / 625) (57388732940297 / 100000) := by
  exact
    packedTile32768 573853952 573919488 13 3251 23955 29 _ _ (2016787 / 100000) (201679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573919488 :
    ThetaLowerSegment 573919488 573985024 (57388732940297 / 100000) (57395212912271 / 100000) := by
  exact
    packedTile32768 573919488 573985024 13 3213 23956 29 _ _ (1008399 / 50000) (2016801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell573985024 :
    ThetaLowerSegment 573985024 574050560 (57395212912271 / 100000) (57401753427101 / 100000) := by
  exact
    packedTile32768 573985024 574050560 13 3243 23957 29 _ _ (201681 / 10000) (2016813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574050560 :
    ThetaLowerSegment 574050560 574116096 (57401753427101 / 100000) (57408287927141 / 100000) := by
  exact
    packedTile32768 574050560 574116096 13 3240 23959 29 _ _ (2016821 / 100000) (252103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574116096 :
    ThetaLowerSegment 574116096 574181632 (57408287927141 / 100000) (57414887004717 / 100000) := by
  exact
    packedTile32768 574116096 574181632 13 3272 23960 29 _ _ (2016833 / 100000) (504209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574181632 :
    ThetaLowerSegment 574181632 574247168 (57414887004717 / 100000) (57421340905517 / 100000) := by
  exact
    packedTile32768 574181632 574247168 13 3200 23962 29 _ _ (504211 / 25000) (2016847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574247168 :
    ThetaLowerSegment 574247168 574312704 (57421340905517 / 100000) (11485578330761 / 20000) := by
  exact
    packedTile32768 574247168 574312704 13 3248 23963 29 _ _ (252107 / 12500) (2016859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574312704 :
    ThetaLowerSegment 574312704 574378240 (11485578330761 / 20000) (1435859901247 / 2500) := by
  exact
    packedTile32768 574312704 574378240 13 3225 23964 29 _ _ (2016867 / 100000) (201687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574378240 :
    ThetaLowerSegment 574378240 574443776 (1435859901247 / 2500) (7180114324947 / 12500) := by
  exact
    packedTile32768 574378240 574443776 13 3232 23966 29 _ _ (1008439 / 50000) (2016881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574443776 :
    ThetaLowerSegment 574443776 574509312 (7180114324947 / 12500) (28723745838933 / 50000) := by
  exact
    packedTile32768 574443776 574509312 13 3261 23967 29 _ _ (201689 / 10000) (2016893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574509312 :
    ThetaLowerSegment 574509312 574574848 (28723745838933 / 50000) (7181744732809 / 12500) := by
  exact
    packedTile32768 574509312 574574848 13 3206 23968 29 _ _ (2016901 / 100000) (252113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574574848 :
    ThetaLowerSegment 574574848 574640384 (7181744732809 / 12500) (57460462406897 / 100000) := by
  exact
    packedTile32768 574574848 574640384 13 3225 23970 29 _ _ (2016913 / 100000) (504229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574640384 :
    ThetaLowerSegment 574640384 574705920 (57460462406897 / 100000) (11493400254901 / 20000) := by
  exact
    packedTile32768 574640384 574705920 13 3242 23971 29 _ _ (504231 / 25000) (2016927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574705920 :
    ThetaLowerSegment 574705920 574771456 (11493400254901 / 20000) (11494729818453 / 20000) := by
  exact
    packedTile32768 574705920 574771456 13 3296 23973 29 _ _ (403387 / 20000) (1008469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574771456 :
    ThetaLowerSegment 574771456 574836992 (11494729818453 / 20000) (57480292915683 / 100000) := by
  exact
    packedTile32768 574771456 574836992 13 3294 23974 29 _ _ (2016947 / 100000) (40339 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574836992 :
    ThetaLowerSegment 574836992 574902528 (57480292915683 / 100000) (57486924673587 / 100000) := by
  exact
    packedTile32768 574836992 574902528 13 3288 23975 29 _ _ (1008479 / 50000) (2016961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574902528 :
    ThetaLowerSegment 574902528 574968064 (57486924673587 / 100000) (57493485876997 / 100000) := by
  exact
    packedTile32768 574902528 574968064 13 3253 23977 29 _ _ (201697 / 10000) (2016973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell574968064 :
    ThetaLowerSegment 574968064 575033600 (57493485876997 / 100000) (57500081404867 / 100000) := by
  exact
    packedTile32768 574968064 575033600 13 3270 23978 29 _ _ (2016981 / 100000) (252123 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575033600 :
    ThetaLowerSegment 575033600 575099136 (57500081404867 / 100000) (57506539813251 / 100000) := by
  exact
    packedTile32768 575033600 575099136 13 3202 23979 29 _ _ (63031 / 3125) (403399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575099136 :
    ThetaLowerSegment 575099136 575164672 (57506539813251 / 100000) (57513052719167 / 100000) := by
  exact
    packedTile32768 575099136 575164672 13 3229 23981 29 _ _ (504251 / 25000) (2017007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575164672 :
    ThetaLowerSegment 575164672 575230208 (57513052719167 / 100000) (57519684664487 / 100000) := by
  exact
    packedTile32768 575164672 575230208 13 3288 23982 29 _ _ (403403 / 20000) (1008509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575230208 :
    ThetaLowerSegment 575230208 575295744 (57519684664487 / 100000) (14381542351573 / 25000) := by
  exact
    packedTile32768 575230208 575295744 13 3215 23983 29 _ _ (2017027 / 100000) (201703 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575295744 :
    ThetaLowerSegment 575295744 575361280 (14381542351573 / 25000) (14383170101239 / 25000) := by
  exact
    packedTile32768 575295744 575361280 13 3228 23985 29 _ _ (1008519 / 50000) (2017041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575361280 :
    ThetaLowerSegment 575361280 575426816 (14383170101239 / 25000) (7192415066283 / 12500) := by
  exact
    packedTile32768 575361280 575426816 13 3292 23986 29 _ _ (2017049 / 100000) (504263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575426816 :
    ThetaLowerSegment 575426816 575492352 (7192415066283 / 12500) (57545849756721 / 100000) := by
  exact
    packedTile32768 575426816 575492352 13 3237 23988 29 _ _ (2017061 / 100000) (252133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575492352 :
    ThetaLowerSegment 575492352 575557888 (57545849756721 / 100000) (11510489923261 / 20000) := by
  exact
    packedTile32768 575492352 575557888 13 3272 23989 29 _ _ (126067 / 6250) (80683 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575557888 :
    ThetaLowerSegment 575557888 575623424 (11510489923261 / 20000) (57558989002633 / 100000) := by
  exact
    packedTile32768 575557888 575623424 13 3242 23990 29 _ _ (504271 / 25000) (2017087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575623424 :
    ThetaLowerSegment 575623424 575688960 (57558989002633 / 100000) (28782732947339 / 50000) := by
  exact
    packedTile32768 575623424 575688960 13 3211 23992 29 _ _ (403419 / 20000) (1008549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575688960 :
    ThetaLowerSegment 575688960 575754496 (28782732947339 / 50000) (143929988167 / 250) := by
  exact
    packedTile32768 575688960 575754496 13 3237 23993 29 _ _ (1008553 / 50000) (2017109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575754496 :
    ThetaLowerSegment 575754496 575820032 (143929988167 / 250) (28789306715479 / 50000) := by
  exact
    packedTile32768 575754496 575820032 13 3281 23994 29 _ _ (1008559 / 50000) (2017121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575820032 :
    ThetaLowerSegment 575820032 575885568 (28789306715479 / 50000) (57585130774757 / 100000) := by
  exact
    packedTile32768 575820032 575885568 13 3231 23996 29 _ _ (2017129 / 100000) (504283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575885568 :
    ThetaLowerSegment 575885568 575951104 (57585130774757 / 100000) (57591660256937 / 100000) := by
  exact
    packedTile32768 575885568 575951104 13 3237 23997 29 _ _ (100857 / 5000) (2017143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell575951104 :
    ThetaLowerSegment 575951104 576016640 (57591660256937 / 100000) (57598201880873 / 100000) := by
  exact
    packedTile32768 575951104 576016640 13 3243 23998 29 _ _ (63036 / 3125) (403431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576016640 :
    ThetaLowerSegment 576016640 576082176 (57598201880873 / 100000) (2880233747847 / 5000) := by
  exact
    packedTile32768 576016640 576082176 13 3209 24000 29 _ _ (2017163 / 100000) (1008583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576082176 :
    ThetaLowerSegment 576082176 576147712 (2880233747847 / 5000) (5761119043219 / 10000) := by
  exact
    packedTile32768 576082176 576147712 13 3230 24001 29 _ _ (80687 / 4000) (1008589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576147712 :
    ThetaLowerSegment 576147712 576213248 (5761119043219 / 10000) (28808897349577 / 50000) := by
  exact
    packedTile32768 576147712 576213248 13 3274 24003 29 _ _ (1008593 / 50000) (2017189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576213248 :
    ThetaLowerSegment 576213248 576278784 (28808897349577 / 50000) (57624348572207 / 100000) := by
  exact
    packedTile32768 576213248 576278784 13 3249 24004 29 _ _ (2017197 / 100000) (5043 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576278784 :
    ThetaLowerSegment 576278784 576344320 (57624348572207 / 100000) (1152617162113 / 2000) := by
  exact
    packedTile32768 576278784 576344320 13 3227 24005 29 _ _ (2017209 / 100000) (504303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576344320 :
    ThetaLowerSegment 576344320 576409856 (1152617162113 / 2000) (5763742819119 / 10000) := by
  exact
    packedTile32768 576344320 576409856 13 3257 24007 29 _ _ (100861 / 5000) (2017223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576409856 :
    ThetaLowerSegment 576409856 576475392 (5763742819119 / 10000) (14411012185833 / 25000) := by
  exact
    packedTile32768 576409856 576475392 13 3282 24008 29 _ _ (2017231 / 100000) (1008617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576475392 :
    ThetaLowerSegment 576475392 576540928 (14411012185833 / 25000) (288253286157 / 500) := by
  exact
    packedTile32768 576475392 576540928 13 3276 24009 29 _ _ (2017243 / 100000) (1008623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576540928 :
    ThetaLowerSegment 576540928 576606464 (288253286157 / 500) (28828654058919 / 50000) := by
  exact
    packedTile32768 576540928 576606464 13 3297 24011 29 _ _ (1008627 / 50000) (2017257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576606464 :
    ThetaLowerSegment 576606464 576672000 (28828654058919 / 50000) (14415968579667 / 25000) := by
  exact
    packedTile32768 576606464 576672000 13 3255 24012 29 _ _ (1008633 / 50000) (2017269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576672000 :
    ThetaLowerSegment 576672000 576737536 (14415968579667 / 25000) (57670501073613 / 100000) := by
  exact
    packedTile32768 576672000 576737536 13 3285 24013 29 _ _ (2017277 / 100000) (12608 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576737536 :
    ThetaLowerSegment 576737536 576803072 (57670501073613 / 100000) (11535427186769 / 20000) := by
  exact
    packedTile32768 576737536 576803072 13 3289 24015 29 _ _ (252161 / 12500) (2017291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576803072 :
    ThetaLowerSegment 576803072 576868608 (11535427186769 / 20000) (11536731976409 / 20000) := by
  exact
    packedTile32768 576803072 576868608 13 3234 24016 29 _ _ (20173 / 1000) (2017303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576868608 :
    ThetaLowerSegment 576868608 576934144 (11536731976409 / 20000) (14422529323639 / 25000) := by
  exact
    packedTile32768 576868608 576934144 13 3201 24018 29 _ _ (2017311 / 100000) (1008657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576934144 :
    ThetaLowerSegment 576934144 576999680 (14422529323639 / 25000) (28848337804189 / 50000) := by
  exact
    packedTile32768 576934144 576999680 13 3251 24019 29 _ _ (1008661 / 50000) (80693 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell576999680 :
    ThetaLowerSegment 576999680 577065216 (28848337804189 / 50000) (1154062944317 / 2000) := by
  exact
    packedTile32768 576999680 577065216 13 3208 24020 29 _ _ (1008667 / 50000) (2017337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577065216 :
    ThetaLowerSegment 577065216 577130752 (1154062944317 / 2000) (1442744001819 / 2500) := by
  exact
    packedTile32768 577065216 577130752 13 3278 24022 29 _ _ (403469 / 20000) (504337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577130752 :
    ThetaLowerSegment 577130752 577196288 (1442744001819 / 2500) (2885813302293 / 5000) := by
  exact
    packedTile32768 577130752 577196288 13 3225 24023 29 _ _ (504339 / 25000) (2017359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577196288 :
    ThetaLowerSegment 577196288 577261824 (2885813302293 / 5000) (2886147681039 / 5000) := by
  exact
    packedTile32768 577196288 577261824 13 3315 24024 29 _ _ (252171 / 12500) (2017371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577261824 :
    ThetaLowerSegment 577261824 577327360 (2886147681039 / 5000) (1804045803756 / 3125) := by
  exact
    packedTile32768 577261824 577327360 13 3228 24026 29 _ _ (2017379 / 100000) (1008691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577327360 :
    ThetaLowerSegment 577327360 577392896 (1804045803756 / 3125) (2309441938681 / 4000) := by
  exact
    packedTile32768 577327360 577392896 13 3263 24027 29 _ _ (2017391 / 100000) (1008697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577392896 :
    ThetaLowerSegment 577392896 577458432 (2309441938681 / 4000) (57742580814701 / 100000) := by
  exact
    packedTile32768 577392896 577458432 13 3238 24029 29 _ _ (1008701 / 50000) (403481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577458432 :
    ThetaLowerSegment 577458432 577523968 (57742580814701 / 100000) (3609319700963 / 6250) := by
  exact
    packedTile32768 577458432 577523968 13 3239 24030 29 _ _ (2017413 / 100000) (252177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577523968 :
    ThetaLowerSegment 577523968 577589504 (3609319700963 / 6250) (57755572992833 / 100000) := by
  exact
    packedTile32768 577523968 577589504 13 3201 24031 29 _ _ (80697 / 4000) (504357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577589504 :
    ThetaLowerSegment 577589504 577655040 (57755572992833 / 100000) (2310488979173 / 4000) := by
  exact
    packedTile32768 577589504 577655040 13 3297 24033 29 _ _ (504359 / 25000) (2017439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577655040 :
    ThetaLowerSegment 577655040 577720576 (2310488979173 / 4000) (28884323006563 / 50000) := by
  exact
    packedTile32768 577655040 577720576 13 3183 24034 29 _ _ (2017447 / 100000) (40349 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577720576 :
    ThetaLowerSegment 577720576 577786112 (28884323006563 / 50000) (57775317750039 / 100000) := by
  exact
    packedTile32768 577720576 577786112 13 3307 24035 29 _ _ (2017459 / 100000) (1008731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577786112 :
    ThetaLowerSegment 577786112 577851648 (57775317750039 / 100000) (57781725234759 / 100000) := by
  exact
    packedTile32768 577786112 577851648 13 3176 24037 29 _ _ (201747 / 10000) (2017473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577851648 :
    ThetaLowerSegment 577851648 577917184 (57781725234759 / 100000) (57788431341603 / 100000) := by
  exact
    packedTile32768 577851648 577917184 13 3324 24038 29 _ _ (2017481 / 100000) (504371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577917184 :
    ThetaLowerSegment 577917184 577982720 (57788431341603 / 100000) (5779492565157 / 10000) := by
  exact
    packedTile32768 577917184 577982720 13 3219 24039 29 _ _ (2017493 / 100000) (252187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell577982720 :
    ThetaLowerSegment 577982720 578048256 (5779492565157 / 10000) (28900641403337 / 50000) := by
  exact
    packedTile32768 577982720 578048256 13 3151 24041 29 _ _ (63047 / 3125) (2017507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578048256 :
    ThetaLowerSegment 578048256 578113792 (28900641403337 / 50000) (57807890168299 / 100000) := by
  exact
    packedTile32768 578048256 578113792 13 3275 24042 29 _ _ (403503 / 20000) (1008759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578113792 :
    ThetaLowerSegment 578113792 578179328 (57807890168299 / 100000) (57814471341373 / 100000) := by
  exact
    packedTile32768 578113792 578179328 13 3262 24043 29 _ _ (2017527 / 100000) (201753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578179328 :
    ThetaLowerSegment 578179328 578244864 (57814471341373 / 100000) (57821004129417 / 100000) := by
  exact
    packedTile32768 578179328 578244864 13 3238 24045 29 _ _ (1008769 / 50000) (2017541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578244864 :
    ThetaLowerSegment 578244864 578310400 (57821004129417 / 100000) (7228455485397 / 12500) := by
  exact
    packedTile32768 578244864 578310400 13 3291 24046 29 _ _ (2017549 / 100000) (126097 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578310400 :
    ThetaLowerSegment 578310400 578375936 (7228455485397 / 12500) (57834202973987 / 100000) := by
  exact
    packedTile32768 578310400 578375936 13 3251 24048 29 _ _ (2017561 / 100000) (504391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578375936 :
    ThetaLowerSegment 578375936 578441472 (57834202973987 / 100000) (57840864996731 / 100000) := by
  exact
    packedTile32768 578375936 578441472 13 3302 24049 29 _ _ (504393 / 25000) (80703 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578441472 :
    ThetaLowerSegment 578441472 578507008 (57840864996731 / 100000) (11569475550931 / 20000) := by
  exact
    packedTile32768 578441472 578507008 13 3228 24050 29 _ _ (2017583 / 100000) (1008793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578507008 :
    ThetaLowerSegment 578507008 578572544 (11569475550931 / 20000) (5785394906157 / 10000) := by
  exact
    packedTile32768 578507008 578572544 13 3257 24052 29 _ _ (403519 / 20000) (1008799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578572544 :
    ThetaLowerSegment 578572544 578638080 (5785394906157 / 10000) (28930198665173 / 50000) := by
  exact
    packedTile32768 578572544 578638080 13 3196 24053 29 _ _ (1008803 / 50000) (2017609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578638080 :
    ThetaLowerSegment 578638080 578703616 (28930198665173 / 50000) (11573377600847 / 20000) := by
  exact
    packedTile32768 578638080 578703616 13 3217 24054 29 _ _ (2017617 / 100000) (100881 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578703616 :
    ThetaLowerSegment 578703616 578769152 (11573377600847 / 20000) (57873481615807 / 100000) := by
  exact
    packedTile32768 578703616 578769152 13 3268 24056 29 _ _ (2017629 / 100000) (63051 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578769152 :
    ThetaLowerSegment 578769152 578834688 (57873481615807 / 100000) (57879927975607 / 100000) := by
  exact
    packedTile32768 578769152 578834688 13 3195 24057 29 _ _ (50441 / 2500) (2017643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578834688 :
    ThetaLowerSegment 578834688 578900224 (57879927975607 / 100000) (57886489376659 / 100000) := by
  exact
    packedTile32768 578834688 578900224 13 3252 24058 29 _ _ (2017651 / 100000) (1008827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578900224 :
    ThetaLowerSegment 578900224 578965760 (57886489376659 / 100000) (11578606128021 / 20000) := by
  exact
    packedTile32768 578900224 578965760 13 3242 24060 29 _ _ (2017663 / 100000) (1008833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell578965760 :
    ThetaLowerSegment 578965760 579031296 (11578606128021 / 20000) (11579917616121 / 20000) := by
  exact
    packedTile32768 578965760 579031296 13 3250 24061 29 _ _ (1008837 / 50000) (2017677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579031296 :
    ThetaLowerSegment 579031296 579096832 (11579917616121 / 20000) (11581240410407 / 20000) := by
  exact
    packedTile32768 579031296 579096832 13 3278 24063 29 _ _ (403537 / 20000) (252211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579096832 :
    ThetaLowerSegment 579096832 579162368 (11581240410407 / 20000) (57912686930193 / 100000) := by
  exact
    packedTile32768 579096832 579162368 13 3214 24064 29 _ _ (2017697 / 100000) (20177 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579162368 :
    ThetaLowerSegment 579162368 579227904 (57912686930193 / 100000) (2316772119789 / 4000) := by
  exact
    packedTile32768 579162368 579227904 13 3279 24065 29 _ _ (504427 / 25000) (2017711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579227904 :
    ThetaLowerSegment 579227904 579293440 (2316772119789 / 4000) (2896298577801 / 5000) := by
  exact
    packedTile32768 579227904 579293440 13 3305 24067 29 _ _ (2017719 / 100000) (1008861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579293440 :
    ThetaLowerSegment 579293440 579358976 (2896298577801 / 5000) (28966341263 / 50) := by
  exact
    packedTile32768 579293440 579358976 13 3326 24068 29 _ _ (201773 / 10000) (2017733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579358976 :
    ThetaLowerSegment 579358976 579424512 (28966341263 / 50) (2896964027117 / 5000) := by
  exact
    packedTile32768 579358976 579424512 13 3270 24069 29 _ _ (1008871 / 50000) (403549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579424512 :
    ThetaLowerSegment 579424512 579490048 (2896964027117 / 5000) (57945900789933 / 100000) := by
  exact
    packedTile32768 579424512 579490048 13 3281 24071 29 _ _ (2017753 / 100000) (504439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579490048 :
    ThetaLowerSegment 579490048 579555584 (57945900789933 / 100000) (57952422203181 / 100000) := by
  exact
    packedTile32768 579490048 579555584 13 3232 24072 29 _ _ (504441 / 25000) (2017767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579555584 :
    ThetaLowerSegment 579555584 579621120 (57952422203181 / 100000) (57958873033053 / 100000) := by
  exact
    packedTile32768 579555584 579621120 13 3197 24073 29 _ _ (126111 / 6250) (2017779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579621120 :
    ThetaLowerSegment 579621120 579686656 (57958873033053 / 100000) (14491339045671 / 25000) := by
  exact
    packedTile32768 579621120 579686656 13 3213 24075 29 _ _ (2017787 / 100000) (201779 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579686656 :
    ThetaLowerSegment 579686656 579752192 (14491339045671 / 25000) (28985931790617 / 50000) := by
  exact
    packedTile32768 579686656 579752192 13 3225 24076 29 _ _ (1008899 / 50000) (2017801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579752192 :
    ThetaLowerSegment 579752192 579817728 (28985931790617 / 50000) (14494618986151 / 25000) := by
  exact
    packedTile32768 579752192 579817728 13 3277 24078 29 _ _ (201781 / 10000) (2017813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579817728 :
    ThetaLowerSegment 579817728 579883264 (14494618986151 / 25000) (57985003595539 / 100000) := by
  exact
    packedTile32768 579817728 579883264 13 3235 24079 29 _ _ (2017821 / 100000) (63057 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579883264 :
    ThetaLowerSegment 579883264 579948800 (57985003595539 / 100000) (57991622084499 / 100000) := by
  exact
    packedTile32768 579883264 579948800 13 3280 24080 29 _ _ (252229 / 12500) (403567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell579948800 :
    ThetaLowerSegment 579948800 580014336 (57991622084499 / 100000) (463985505191 / 800) := by
  exact
    packedTile32768 579948800 580014336 13 3254 24082 29 _ _ (504461 / 25000) (2017847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580014336 :
    ThetaLowerSegment 580014336 580079872 (463985505191 / 800) (11600926635549 / 20000) := by
  exact
    packedTile32768 580014336 580079872 13 3194 24083 29 _ _ (403571 / 20000) (1008929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580079872 :
    ThetaLowerSegment 580079872 580145408 (11600926635549 / 20000) (58011084295347 / 100000) := by
  exact
    packedTile32768 580079872 580145408 13 3197 24084 29 _ _ (1008933 / 50000) (2017869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580145408 :
    ThetaLowerSegment 580145408 580210944 (58011084295347 / 100000) (29008854492769 / 50000) := by
  exact
    packedTile32768 580145408 580210944 13 3283 24086 29 _ _ (2017877 / 100000) (50447 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580210944 :
    ThetaLowerSegment 580210944 580276480 (29008854492769 / 50000) (29012163830729 / 50000) := by
  exact
    packedTile32768 580210944 580276480 13 3280 24087 29 _ _ (2017889 / 100000) (504473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580276480 :
    ThetaLowerSegment 580276480 580342016 (29012163830729 / 50000) (29015493365729 / 50000) := by
  exact
    packedTile32768 580276480 580342016 13 3300 24088 29 _ _ (20179 / 1000) (2017903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580342016 :
    ThetaLowerSegment 580342016 580407552 (29015493365729 / 50000) (5803742790337 / 10000) := by
  exact
    packedTile32768 580342016 580407552 13 3192 24090 29 _ _ (2017911 / 100000) (1008957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580407552 :
    ThetaLowerSegment 580407552 580473088 (5803742790337 / 10000) (7255496251217 / 12500) := by
  exact
    packedTile32768 580407552 580473088 13 3242 24091 29 _ _ (2017923 / 100000) (1008963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580473088 :
    ThetaLowerSegment 580473088 580538624 (7255496251217 / 12500) (29025317622869 / 50000) := by
  exact
    packedTile32768 580473088 580538624 13 3303 24093 29 _ _ (1008967 / 50000) (2017937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580538624 :
    ThetaLowerSegment 580538624 580604160 (29025317622869 / 50000) (58057102759463 / 100000) := by
  exact
    packedTile32768 580538624 580604160 13 3205 24094 29 _ _ (403589 / 20000) (504487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580604160 :
    ThetaLowerSegment 580604160 580669696 (58057102759463 / 100000) (58063677260111 / 100000) := by
  exact
    packedTile32768 580604160 580669696 13 3258 24095 29 _ _ (504489 / 25000) (2017959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580669696 :
    ThetaLowerSegment 580669696 580735232 (58063677260111 / 100000) (58070267943599 / 100000) := by
  exact
    packedTile32768 580669696 580735232 13 3266 24097 29 _ _ (126123 / 6250) (2017971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580735232 :
    ThetaLowerSegment 580735232 580800768 (58070267943599 / 100000) (1814899878302 / 3125) := by
  exact
    packedTile32768 580735232 580800768 13 3235 24098 29 _ _ (2017979 / 100000) (1008991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580800768 :
    ThetaLowerSegment 580800768 580866304 (1814899878302 / 3125) (3630216471539 / 6250) := by
  exact
    packedTile32768 580800768 580866304 13 3304 24099 29 _ _ (201799 / 10000) (2017993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580866304 :
    ThetaLowerSegment 580866304 580931840 (3630216471539 / 6250) (14522473224749 / 25000) := by
  exact
    packedTile32768 580866304 580931840 13 3186 24101 29 _ _ (1009001 / 50000) (403601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580931840 :
    ThetaLowerSegment 580931840 580997376 (14522473224749 / 25000) (58096485747467 / 100000) := by
  exact
    packedTile32768 580931840 580997376 13 3267 24102 29 _ _ (2018013 / 100000) (63063 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell580997376 :
    ThetaLowerSegment 580997376 581062912 (58096485747467 / 100000) (58102812252707 / 100000) := by
  exact
    packedTile32768 580997376 581062912 13 3135 24103 29 _ _ (252253 / 12500) (2018027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581062912 :
    ThetaLowerSegment 581062912 581128448 (58102812252707 / 100000) (29054684424211 / 50000) := by
  exact
    packedTile32768 581062912 581128448 13 3249 24105 29 _ _ (403607 / 20000) (1009019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581128448 :
    ThetaLowerSegment 581128448 581193984 (29054684424211 / 50000) (29058010165667 / 50000) := by
  exact
    packedTile32768 581128448 581193984 13 3296 24106 29 _ _ (2018047 / 100000) (40361 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581193984 :
    ThetaLowerSegment 581193984 581259520 (29058010165667 / 50000) (14530631133067 / 25000) := by
  exact
    packedTile32768 581193984 581259520 13 3223 24107 29 _ _ (1009029 / 50000) (2018061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581259520 :
    ThetaLowerSegment 581259520 581325056 (14530631133067 / 25000) (58129020696379 / 100000) := by
  exact
    packedTile32768 581259520 581325056 13 3219 24109 29 _ _ (2018069 / 100000) (252259 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581325056 :
    ThetaLowerSegment 581325056 581390592 (58129020696379 / 100000) (14533878215739 / 25000) := by
  exact
    packedTile32768 581325056 581390592 13 3217 24110 29 _ _ (2018081 / 100000) (504521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581390592 :
    ThetaLowerSegment 581390592 581456128 (14533878215739 / 25000) (14535547177823 / 25000) := by
  exact
    packedTile32768 581390592 581456128 13 3308 24112 29 _ _ (504523 / 25000) (403619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581456128 :
    ThetaLowerSegment 581456128 581521664 (14535547177823 / 25000) (58148793962411 / 100000) := by
  exact
    packedTile32768 581456128 581521664 13 3273 24113 29 _ _ (2018103 / 100000) (1009053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581521664 :
    ThetaLowerSegment 581521664 581587200 (58148793962411 / 100000) (11631075006433 / 20000) := by
  exact
    packedTile32768 581521664 581587200 13 3261 24114 29 _ _ (1009057 / 50000) (2018117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581587200 :
    ThetaLowerSegment 581587200 581652736 (11631075006433 / 20000) (11632408987719 / 20000) := by
  exact
    packedTile32768 581587200 581652736 13 3305 24116 29 _ _ (1009063 / 50000) (2018129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581652736 :
    ThetaLowerSegment 581652736 581718272 (11632408987719 / 20000) (29084315059813 / 50000) := by
  exact
    packedTile32768 581652736 581718272 13 3263 24117 29 _ _ (2018137 / 100000) (100907 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581718272 :
    ThetaLowerSegment 581718272 581783808 (29084315059813 / 50000) (29087603631979 / 50000) := by
  exact
    packedTile32768 581718272 581783808 13 3259 24118 29 _ _ (504537 / 25000) (2018151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581783808 :
    ThetaLowerSegment 581783808 581849344 (29087603631979 / 50000) (29090848831651 / 50000) := by
  exact
    packedTile32768 581783808 581849344 13 3216 24120 29 _ _ (2018159 / 100000) (1009081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581849344 :
    ThetaLowerSegment 581849344 581914880 (29090848831651 / 50000) (58188165901357 / 100000) := by
  exact
    packedTile32768 581849344 581914880 13 3205 24121 29 _ _ (2018171 / 100000) (1009087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581914880 :
    ThetaLowerSegment 581914880 581980416 (58188165901357 / 100000) (11638918358569 / 20000) := by
  exact
    packedTile32768 581914880 581980416 13 3184 24122 29 _ _ (1009091 / 50000) (403637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell581980416 :
    ThetaLowerSegment 581980416 582045952 (11638918358569 / 20000) (29100578487337 / 50000) := by
  exact
    packedTile32768 581980416 582045952 13 3253 24124 29 _ _ (2018193 / 100000) (504549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582045952 :
    ThetaLowerSegment 582045952 582111488 (29100578487337 / 50000) (5820768384641 / 10000) := by
  exact
    packedTile32768 582045952 582111488 13 3234 24125 29 _ _ (504551 / 25000) (2018207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582111488 :
    ThetaLowerSegment 582111488 582177024 (5820768384641 / 10000) (29107100332937 / 50000) := by
  exact
    packedTile32768 582111488 582177024 13 3229 24126 29 _ _ (252277 / 12500) (2018219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582177024 :
    ThetaLowerSegment 582177024 582242560 (29107100332937 / 50000) (29110410225217 / 50000) := by
  exact
    packedTile32768 582177024 582242560 13 3280 24128 29 _ _ (2018227 / 100000) (201823 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582242560 :
    ThetaLowerSegment 582242560 582308096 (29110410225217 / 50000) (3639218170439 / 6250) := by
  exact
    packedTile32768 582242560 582308096 13 3305 24129 29 _ _ (1009119 / 50000) (2018241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582308096 :
    ThetaLowerSegment 582308096 582373632 (3639218170439 / 6250) (3639627875189 / 6250) := by
  exact
    packedTile32768 582308096 582373632 13 3248 24131 29 _ _ (8073 / 400) (2018253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582373632 :
    ThetaLowerSegment 582373632 582439168 (3639627875189 / 6250) (58240595259969 / 100000) := by
  exact
    packedTile32768 582373632 582439168 13 3245 24132 29 _ _ (2018261 / 100000) (252283 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582439168 :
    ThetaLowerSegment 582439168 582504704 (58240595259969 / 100000) (58247164735329 / 100000) := by
  exact
    packedTile32768 582439168 582504704 13 3255 24133 29 _ _ (63071 / 3125) (80731 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582504704 :
    ThetaLowerSegment 582504704 582570240 (58247164735329 / 100000) (58253772593871 / 100000) := by
  exact
    packedTile32768 582504704 582570240 13 3274 24135 29 _ _ (2018283 / 100000) (1009143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582570240 :
    ThetaLowerSegment 582570240 582635776 (58253772593871 / 100000) (58260445077141 / 100000) := by
  exact
    packedTile32768 582570240 582635776 13 3306 24136 29 _ _ (403659 / 20000) (1009149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582635776 :
    ThetaLowerSegment 582635776 582701312 (58260445077141 / 100000) (58266845125467 / 100000) := by
  exact
    packedTile32768 582635776 582701312 13 3171 24137 29 _ _ (1009153 / 50000) (2018309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582701312 :
    ThetaLowerSegment 582701312 582766848 (58266845125467 / 100000) (2913672150187 / 5000) := by
  exact
    packedTile32768 582701312 582766848 13 3269 24139 29 _ _ (2018317 / 100000) (25229 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582766848 :
    ThetaLowerSegment 582766848 582832384 (2913672150187 / 5000) (14570012247821 / 25000) := by
  exact
    packedTile32768 582766848 582832384 13 3273 24140 29 _ _ (252291 / 12500) (2018331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582832384 :
    ThetaLowerSegment 582832384 582897920 (14570012247821 / 25000) (1821458095462 / 3125) := by
  exact
    packedTile32768 582832384 582897920 13 3275 24141 29 _ _ (100917 / 5000) (2018343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582897920 :
    ThetaLowerSegment 582897920 582963456 (1821458095462 / 3125) (29146617421171 / 50000) := by
  exact
    packedTile32768 582897920 582963456 13 3258 24143 29 _ _ (2018351 / 100000) (1009177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell582963456 :
    ThetaLowerSegment 582963456 583028992 (29146617421171 / 50000) (29149919461403 / 50000) := by
  exact
    packedTile32768 582963456 583028992 13 3272 24144 29 _ _ (1009181 / 50000) (403673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583028992 :
    ThetaLowerSegment 583028992 583094528 (29149919461403 / 50000) (58306408726921 / 100000) := by
  exact
    packedTile32768 583028992 583094528 13 3255 24145 29 _ _ (2018373 / 100000) (252297 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583094528 :
    ThetaLowerSegment 583094528 583160064 (58306408726921 / 100000) (11662579969973 / 20000) := by
  exact
    packedTile32768 583094528 583160064 13 3216 24147 29 _ _ (126149 / 6250) (2018387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583160064 :
    ThetaLowerSegment 583160064 583225600 (11662579969973 / 20000) (58319380919421 / 100000) := by
  exact
    packedTile32768 583160064 583225600 13 3211 24148 29 _ _ (504599 / 25000) (2018399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583225600 :
    ThetaLowerSegment 583225600 583291136 (58319380919421 / 100000) (466607881177 / 800) := by
  exact
    packedTile32768 583225600 583291136 13 3272 24150 29 _ _ (2018407 / 100000) (201841 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583291136 :
    ThetaLowerSegment 583291136 583356672 (466607881177 / 800) (11666511019543 / 20000) := by
  exact
    packedTile32768 583291136 583356672 13 3255 24151 29 _ _ (1009209 / 50000) (2018421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583356672 :
    ThetaLowerSegment 583356672 583422208 (11666511019543 / 20000) (29169606947493 / 50000) := by
  exact
    packedTile32768 583356672 583422208 13 3299 24152 29 _ _ (2018429 / 100000) (63076 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583422208 :
    ThetaLowerSegment 583422208 583487744 (29169606947493 / 50000) (58345836399907 / 100000) := by
  exact
    packedTile32768 583422208 583487744 13 3281 24154 29 _ _ (2018441 / 100000) (504611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583487744 :
    ThetaLowerSegment 583487744 583553280 (58345836399907 / 100000) (58352507383767 / 100000) := by
  exact
    packedTile32768 583487744 583553280 13 3305 24155 29 _ _ (504613 / 25000) (403691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583553280 :
    ThetaLowerSegment 583553280 583618816 (58352507383767 / 100000) (29179512500397 / 50000) := by
  exact
    packedTile32768 583553280 583618816 13 3229 24156 29 _ _ (2018463 / 100000) (1009233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583618816 :
    ThetaLowerSegment 583618816 583684352 (29179512500397 / 50000) (29182780409803 / 50000) := by
  exact
    packedTile32768 583618816 583684352 13 3238 24158 29 _ _ (1009237 / 50000) (2018477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583684352 :
    ThetaLowerSegment 583684352 583749888 (29182780409803 / 50000) (29186066505011 / 50000) := by
  exact
    packedTile32768 583684352 583749888 13 3256 24159 29 _ _ (1009243 / 50000) (2018489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583749888 :
    ThetaLowerSegment 583749888 583815424 (29186066505011 / 50000) (29189288026223 / 50000) := by
  exact
    packedTile32768 583749888 583815424 13 3192 24160 29 _ _ (2018497 / 100000) (4037 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583815424 :
    ThetaLowerSegment 583815424 583880960 (29189288026223 / 50000) (29192592323819 / 50000) := by
  exact
    packedTile32768 583815424 583880960 13 3274 24162 29 _ _ (504627 / 25000) (2018511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583880960 :
    ThetaLowerSegment 583880960 583946496 (29192592323819 / 50000) (14597911986369 / 25000) := by
  exact
    packedTile32768 583880960 583946496 13 3202 24163 29 _ _ (2018519 / 100000) (1009261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell583946496 :
    ThetaLowerSegment 583946496 584012032 (14597911986369 / 25000) (29199131334143 / 50000) := by
  exact
    packedTile32768 583946496 584012032 13 3277 24164 29 _ _ (201853 / 10000) (2018533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584012032 :
    ThetaLowerSegment 584012032 584077568 (29199131334143 / 50000) (14601174949681 / 25000) := by
  exact
    packedTile32768 584012032 584077568 13 3189 24166 29 _ _ (1009271 / 50000) (403709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584077568 :
    ThetaLowerSegment 584077568 584143104 (14601174949681 / 25000) (58411197520831 / 100000) := by
  exact
    packedTile32768 584077568 584143104 13 3219 24167 29 _ _ (2018553 / 100000) (504639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584143104 :
    ThetaLowerSegment 584143104 584208640 (58411197520831 / 100000) (58417786113727 / 100000) := by
  exact
    packedTile32768 584143104 584208640 13 3264 24169 29 _ _ (504641 / 25000) (2018567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584208640 :
    ThetaLowerSegment 584208640 584274176 (58417786113727 / 100000) (58424245553727 / 100000) := by
  exact
    packedTile32768 584208640 584274176 13 3200 24170 29 _ _ (80743 / 4000) (1009289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584274176 :
    ThetaLowerSegment 584274176 584339712 (58424245553727 / 100000) (29215373711227 / 50000) := by
  exact
    packedTile32768 584274176 584339712 13 3221 24171 29 _ _ (2018587 / 100000) (201859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584339712 :
    ThetaLowerSegment 584339712 584405248 (29215373711227 / 50000) (29218639802791 / 50000) := by
  exact
    packedTile32768 584339712 584405248 13 3236 24173 29 _ _ (1009299 / 50000) (2018601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584405248 :
    ThetaLowerSegment 584405248 584470784 (29218639802791 / 50000) (2337751746273 / 4000) := by
  exact
    packedTile32768 584405248 584470784 13 3227 24174 29 _ _ (2018609 / 100000) (504653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584470784 :
    ThetaLowerSegment 584470784 584536320 (2337751746273 / 4000) (11690081331189 / 20000) := by
  exact
    packedTile32768 584470784 584536320 13 3276 24175 29 _ _ (100931 / 5000) (2018623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584536320 :
    ThetaLowerSegment 584536320 584601856 (11690081331189 / 20000) (29228480575401 / 50000) := by
  exact
    packedTile32768 584536320 584601856 13 3247 24177 29 _ _ (2018631 / 100000) (1009317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584601856 :
    ThetaLowerSegment 584601856 584667392 (29228480575401 / 50000) (29231791149921 / 50000) := by
  exact
    packedTile32768 584601856 584667392 13 3280 24178 29 _ _ (2018643 / 100000) (1009323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584667392 :
    ThetaLowerSegment 584667392 584732928 (29231791149921 / 50000) (7308756510739 / 12500) := by
  exact
    packedTile32768 584667392 584732928 13 3205 24179 29 _ _ (1009327 / 50000) (2018657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584732928 :
    ThetaLowerSegment 584732928 584798464 (7308756510739 / 12500) (29238383082851 / 50000) := by
  exact
    packedTile32768 584732928 584798464 13 3326 24181 29 _ _ (403733 / 20000) (504667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584798464 :
    ThetaLowerSegment 584798464 584864000 (29238383082851 / 50000) (29241576628283 / 50000) := by
  exact
    packedTile32768 584798464 584864000 13 3164 24182 29 _ _ (504669 / 25000) (2018679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584864000 :
    ThetaLowerSegment 584864000 584929536 (29241576628283 / 50000) (11697929474529 / 20000) := by
  exact
    packedTile32768 584864000 584929536 13 3217 24183 29 _ _ (2018687 / 100000) (201869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584929536 :
    ThetaLowerSegment 584929536 584995072 (11697929474529 / 20000) (58496171807813 / 100000) := by
  exact
    packedTile32768 584929536 584995072 13 3232 24185 29 _ _ (2018699 / 100000) (1009351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell584995072 :
    ThetaLowerSegment 584995072 585060608 (58496171807813 / 100000) (58502748764993 / 100000) := by
  exact
    packedTile32768 584995072 585060608 13 3258 24186 29 _ _ (201871 / 10000) (2018713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585060608 :
    ThetaLowerSegment 585060608 585126144 (58502748764993 / 100000) (14627319831857 / 25000) := by
  exact
    packedTile32768 585060608 585126144 13 3235 24188 29 _ _ (2018721 / 100000) (504681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585126144 :
    ThetaLowerSegment 585126144 585191680 (14627319831857 / 25000) (1828619691024 / 3125) := by
  exact
    packedTile32768 585126144 585191680 13 3245 24189 29 _ _ (504683 / 25000) (403747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585191680 :
    ThetaLowerSegment 585191680 585257216 (1828619691024 / 3125) (7315303168677 / 12500) := by
  exact
    packedTile32768 585191680 585257216 13 3267 24190 29 _ _ (252343 / 12500) (2018747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585257216 :
    ThetaLowerSegment 585257216 585322752 (7315303168677 / 12500) (58528956021841 / 100000) := by
  exact
    packedTile32768 585257216 585322752 13 3235 24192 29 _ _ (403751 / 20000) (1009379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585322752 :
    ThetaLowerSegment 585322752 585339136 (58528956021841 / 100000) (58530542771917 / 100000) := by
  exact
    packedTile32768 585322752 585339136 11 786 24193 29 _ _ (1009383 / 50000) (2018769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell585339136 :
    ThetaLowerSegment 585339136 585341184 (58530542771917 / 100000) (5853077896789 / 10000) := by
  exact
    packedTile32768 585339136 585341184 8 117 24193 29 _ _ (2018769 / 100000) (504693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_553341184_585341184 :
    ThetaLowerSegment 553341184 585341184 (55331452530587 / 100000) (5853077896789 / 10000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell553341184 cell553406720)
                    (ThetaLowerSegment.join cell553472256 cell553537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell553603328 cell553668864)
                    (ThetaLowerSegment.join cell553734400 cell553799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell553865472 cell553931008)
                    (ThetaLowerSegment.join cell553996544 cell554062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell554127616 cell554193152)
                    (ThetaLowerSegment.join cell554258688 cell554324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell554389760 cell554455296)
                    (ThetaLowerSegment.join cell554520832 cell554586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell554651904 cell554717440)
                    (ThetaLowerSegment.join cell554782976 cell554848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell554914048 cell554979584)
                    (ThetaLowerSegment.join cell555045120 cell555110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell555176192 cell555241728)
                    (ThetaLowerSegment.join cell555307264 cell555372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell555438336 cell555503872)
                    (ThetaLowerSegment.join cell555569408 cell555634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell555700480 cell555766016)
                    (ThetaLowerSegment.join cell555831552 cell555897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell555962624 cell556028160)
                    (ThetaLowerSegment.join cell556093696 cell556159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell556224768 cell556290304)
                    (ThetaLowerSegment.join cell556355840 cell556421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell556486912 cell556552448)
                    (ThetaLowerSegment.join cell556617984 cell556683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell556749056 cell556814592)
                    (ThetaLowerSegment.join cell556880128 cell556945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell557011200 cell557076736)
                    (ThetaLowerSegment.join cell557142272 cell557207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell557273344 cell557338880)
                    (ThetaLowerSegment.join cell557404416 cell557469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell557535488 cell557601024)
                    (ThetaLowerSegment.join cell557666560 cell557732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell557797632 cell557863168)
                    (ThetaLowerSegment.join cell557928704 cell557994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell558059776 cell558125312)
                    (ThetaLowerSegment.join cell558190848 cell558256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell558321920 cell558387456)
                    (ThetaLowerSegment.join cell558452992 cell558518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell558584064 cell558649600)
                    (ThetaLowerSegment.join cell558715136 cell558780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell558846208 cell558911744)
                    (ThetaLowerSegment.join cell558977280 cell559042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell559108352 cell559173888)
                    (ThetaLowerSegment.join cell559239424 cell559304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell559370496 cell559436032)
                    (ThetaLowerSegment.join cell559501568 cell559567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell559632640 cell559698176)
                    (ThetaLowerSegment.join cell559763712 cell559829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell559894784 cell559960320)
                    (ThetaLowerSegment.join cell560025856 cell560091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell560156928 cell560222464)
                    (ThetaLowerSegment.join cell560288000 cell560353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell560419072 cell560484608)
                    (ThetaLowerSegment.join cell560550144 cell560615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell560681216 cell560746752)
                    (ThetaLowerSegment.join cell560812288 cell560877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell560943360 cell561008896)
                    (ThetaLowerSegment.join cell561074432 cell561139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell561205504 cell561271040)
                    (ThetaLowerSegment.join cell561336576 cell561402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell561467648 cell561533184)
                    (ThetaLowerSegment.join cell561598720 cell561664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell561729792 cell561795328)
                    (ThetaLowerSegment.join cell561860864 cell561926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell561991936 cell562057472)
                    (ThetaLowerSegment.join cell562123008 cell562188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell562254080 cell562319616)
                    (ThetaLowerSegment.join cell562385152 cell562450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell562516224 cell562581760)
                    (ThetaLowerSegment.join cell562647296 cell562712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell562778368 cell562843904)
                    (ThetaLowerSegment.join cell562909440 cell562974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell563040512 cell563106048)
                    (ThetaLowerSegment.join cell563171584 cell563237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell563302656 cell563368192)
                    (ThetaLowerSegment.join cell563433728 cell563499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell563564800 cell563630336)
                    (ThetaLowerSegment.join cell563695872 cell563761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell563826944 cell563892480)
                    (ThetaLowerSegment.join cell563958016 cell564023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell564089088 cell564154624)
                    (ThetaLowerSegment.join cell564220160 cell564285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell564351232 cell564416768)
                    (ThetaLowerSegment.join cell564482304 cell564547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell564613376 cell564678912)
                    (ThetaLowerSegment.join cell564744448 cell564809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell564875520 cell564941056)
                    (ThetaLowerSegment.join cell565006592 cell565072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell565137664 cell565203200)
                    (ThetaLowerSegment.join cell565268736 cell565334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell565399808 cell565465344)
                    (ThetaLowerSegment.join cell565530880 cell565596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell565661952 cell565727488)
                    (ThetaLowerSegment.join cell565793024 cell565858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell565924096 cell565989632)
                    (ThetaLowerSegment.join cell566055168 cell566120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell566186240 cell566251776)
                    (ThetaLowerSegment.join cell566317312 cell566382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell566448384 cell566513920)
                    (ThetaLowerSegment.join cell566579456 cell566644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell566710528 cell566776064)
                    (ThetaLowerSegment.join cell566841600 cell566907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell566972672 cell567038208)
                    (ThetaLowerSegment.join cell567103744 cell567169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell567234816 cell567300352)
                    (ThetaLowerSegment.join cell567365888 cell567431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell567496960 cell567562496)
                    (ThetaLowerSegment.join cell567628032 cell567693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell567759104 cell567824640)
                    (ThetaLowerSegment.join cell567890176 cell567955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell568021248 cell568086784)
                    (ThetaLowerSegment.join cell568152320 cell568217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell568283392 cell568348928)
                    (ThetaLowerSegment.join cell568414464 cell568480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell568545536 cell568611072)
                    (ThetaLowerSegment.join cell568676608 cell568742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell568807680 cell568873216)
                    (ThetaLowerSegment.join cell568938752 cell569004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell569069824 cell569135360)
                    (ThetaLowerSegment.join cell569200896 cell569266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell569331968 cell569397504)
                    (ThetaLowerSegment.join cell569463040 cell569528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell569594112 cell569659648)
                    (ThetaLowerSegment.join cell569725184 cell569790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell569856256 cell569921792)
                    (ThetaLowerSegment.join cell569987328 cell570052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell570118400 cell570183936)
                    (ThetaLowerSegment.join cell570249472 cell570315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell570380544 cell570446080)
                    (ThetaLowerSegment.join cell570511616 cell570577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell570642688 cell570708224)
                    (ThetaLowerSegment.join cell570773760 cell570839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell570904832 cell570970368)
                    (ThetaLowerSegment.join cell571035904 cell571101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell571166976 cell571232512)
                    (ThetaLowerSegment.join cell571298048 cell571363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell571429120 cell571494656)
                    (ThetaLowerSegment.join cell571560192 cell571625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell571691264 cell571756800)
                    (ThetaLowerSegment.join cell571822336 cell571887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell571953408 cell572018944)
                    (ThetaLowerSegment.join cell572084480 cell572150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell572215552 cell572281088)
                    (ThetaLowerSegment.join cell572346624 cell572412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell572477696 cell572543232)
                    (ThetaLowerSegment.join cell572608768 cell572674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell572739840 cell572805376)
                    (ThetaLowerSegment.join cell572870912 cell572936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell573001984 cell573067520)
                    (ThetaLowerSegment.join cell573133056 cell573198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell573264128 cell573329664)
                    (ThetaLowerSegment.join cell573395200 cell573460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell573526272 cell573591808)
                    (ThetaLowerSegment.join cell573657344 cell573722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell573788416 cell573853952)
                    (ThetaLowerSegment.join cell573919488 cell573985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell574050560 cell574116096)
                    (ThetaLowerSegment.join cell574181632 cell574247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell574312704 cell574378240)
                    (ThetaLowerSegment.join cell574443776 cell574509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell574574848 cell574640384)
                    (ThetaLowerSegment.join cell574705920 cell574771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell574836992 cell574902528)
                    (ThetaLowerSegment.join cell574968064 cell575033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell575099136 cell575164672)
                    (ThetaLowerSegment.join cell575230208 cell575295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell575361280 cell575426816)
                    (ThetaLowerSegment.join cell575492352 cell575557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell575623424 cell575688960)
                    (ThetaLowerSegment.join cell575754496 cell575820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell575885568 cell575951104)
                    (ThetaLowerSegment.join cell576016640 cell576082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell576147712 cell576213248)
                    (ThetaLowerSegment.join cell576278784 cell576344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell576409856 cell576475392)
                    (ThetaLowerSegment.join cell576540928 cell576606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell576672000 cell576737536)
                    (ThetaLowerSegment.join cell576803072 cell576868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell576934144 cell576999680)
                    (ThetaLowerSegment.join cell577065216 cell577130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell577196288 cell577261824)
                    (ThetaLowerSegment.join cell577327360 cell577392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell577458432 cell577523968)
                    (ThetaLowerSegment.join cell577589504 cell577655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell577720576 cell577786112)
                    (ThetaLowerSegment.join cell577851648 cell577917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell577982720 cell578048256)
                    (ThetaLowerSegment.join cell578113792 cell578179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell578244864 cell578310400)
                    (ThetaLowerSegment.join cell578375936 cell578441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell578507008 cell578572544)
                    (ThetaLowerSegment.join cell578638080 cell578703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell578769152 cell578834688)
                    (ThetaLowerSegment.join cell578900224 cell578965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell579031296 cell579096832)
                    (ThetaLowerSegment.join cell579162368 cell579227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell579293440 cell579358976)
                    (ThetaLowerSegment.join cell579424512 cell579490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell579555584 cell579621120)
                    (ThetaLowerSegment.join cell579686656 cell579752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell579817728 cell579883264)
                    (ThetaLowerSegment.join cell579948800 cell580014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell580079872 cell580145408)
                    (ThetaLowerSegment.join cell580210944 cell580276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell580342016 cell580407552)
                    (ThetaLowerSegment.join cell580473088 cell580538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell580604160 cell580669696)
                    (ThetaLowerSegment.join cell580735232 cell580800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell580866304 cell580931840)
                    (ThetaLowerSegment.join cell580997376 cell581062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell581128448 cell581193984)
                    (ThetaLowerSegment.join cell581259520 cell581325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell581390592 cell581456128)
                    (ThetaLowerSegment.join cell581521664 cell581587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell581652736 cell581718272)
                    (ThetaLowerSegment.join cell581783808 cell581849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell581914880 cell581980416)
                    (ThetaLowerSegment.join cell582045952 cell582111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell582177024 cell582242560)
                    (ThetaLowerSegment.join cell582308096 cell582373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell582439168 cell582504704)
                    (ThetaLowerSegment.join cell582570240 cell582635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell582701312 cell582766848)
                    (ThetaLowerSegment.join cell582832384 cell582897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell582963456 cell583028992)
                    (ThetaLowerSegment.join cell583094528 cell583160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell583225600 cell583291136)
                    (ThetaLowerSegment.join cell583356672 cell583422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell583487744 cell583553280)
                    (ThetaLowerSegment.join cell583618816 cell583684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell583749888 cell583815424)
                    (ThetaLowerSegment.join cell583880960 cell583946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell584012032 cell584077568)
                    (ThetaLowerSegment.join cell584143104 cell584208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell584274176 cell584339712)
                    (ThetaLowerSegment.join cell584405248 cell584470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell584536320 cell584601856)
                    (ThetaLowerSegment.join cell584667392 cell584732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell584798464 cell584864000)
                  (ThetaLowerSegment.join cell584929536 cell584995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell585060608 cell585126144)
                  (ThetaLowerSegment.join cell585191680 cell585257216)))
              (ThetaLowerSegment.join cell585322752 cell585339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
