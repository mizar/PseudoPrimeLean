/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2665341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2633341184 :
    ThetaLowerSegment 2633341184 2633472256 (65832433071487 / 25000) (8229469390589 / 3125) := by
  exact
    packedTile65536 2633341184 2633472256 14 6126 51316 31 _ _ (43383 / 2000) (2169153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633472256 :
    ThetaLowerSegment 2633472256 2633603328 (8229469390589 / 3125) (263356120025893 / 100000) := by
  exact
    packedTile65536 2633472256 2633603328 14 6039 51317 31 _ _ (433831 / 20000) (1084579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633603328 :
    ThetaLowerSegment 2633603328 2633734400 (263356120025893 / 100000)
      (263369260797173 / 100000) := by
  exact
    packedTile65536 2633603328 2633734400 14 6058 51318 31 _ _ (54229 / 2500) (2169163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633734400 :
    ThetaLowerSegment 2633734400 2633865472 (263369260797173 / 100000)
      (32922801555571 / 12500) := by
  exact
    packedTile65536 2633734400 2633865472 14 6063 51319 31 _ _ (433833 / 20000) (135573 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633865472 :
    ThetaLowerSegment 2633865472 2633996544 (32922801555571 / 12500) (8231110633169 / 3125) := by
  exact
    packedTile65536 2633865472 2633996544 14 6052 51321 31 _ _ (216917 / 10000) (2169173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2633996544 :
    ThetaLowerSegment 2633996544 2634127616 (8231110633169 / 3125) (263408652924283 / 100000) := by
  exact
    packedTile65536 2633996544 2634127616 14 6045 51322 31 _ _ (86767 / 4000) (1084589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634127616 :
    ThetaLowerSegment 2634127616 2634258688 (263408652924283 / 100000)
      (263421711387883 / 100000) := by
  exact
    packedTile65536 2634127616 2634258688 14 6020 51323 31 _ _ (108459 / 5000) (2169183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634258688 :
    ThetaLowerSegment 2634258688 2634389760 (263421711387883 / 100000) (16464673253173 / 6250) := by
  exact
    packedTile65536 2634258688 2634389760 14 6021 51325 31 _ _ (433837 / 20000) (542297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634389760 :
    ThetaLowerSegment 2634389760 2634520832 (16464673253173 / 6250) (16465488868613 / 6250) := by
  exact
    packedTile65536 2634389760 2634520832 14 6016 51326 31 _ _ (216919 / 10000) (2169193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634520832 :
    ThetaLowerSegment 2634520832 2634651904 (16465488868613 / 6250) (131730438056659 / 50000) := by
  exact
    packedTile65536 2634520832 2634651904 14 6018 51327 31 _ _ (433839 / 20000) (1084599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634651904 :
    ThetaLowerSegment 2634651904 2634782976 (131730438056659 / 50000)
      (131737049778259 / 50000) := by
  exact
    packedTile65536 2634651904 2634782976 14 6096 51328 31 _ _ (5423 / 250) (2169203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634782976 :
    ThetaLowerSegment 2634782976 2634914048 (131737049778259 / 50000) (32935879044591 / 12500) := by
  exact
    packedTile65536 2634782976 2634914048 14 5962 51330 31 _ _ (433841 / 20000) (271151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2634914048 :
    ThetaLowerSegment 2634914048 2635045120 (32935879044591 / 12500) (32937514628931 / 12500) := by
  exact
    packedTile65536 2634914048 2635045120 14 6032 51331 31 _ _ (216921 / 10000) (2169213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635045120 :
    ThetaLowerSegment 2635045120 2635176192 (32937514628931 / 12500) (32939145878611 / 12500) := by
  exact
    packedTile65536 2635045120 2635176192 14 6016 51332 31 _ _ (433843 / 20000) (1084609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635176192 :
    ThetaLowerSegment 2635176192 2635307264 (32939145878611 / 12500) (16470386125653 / 6250) := by
  exact
    packedTile65536 2635176192 2635307264 14 5998 51333 31 _ _ (108461 / 5000) (2169223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635307264 :
    ThetaLowerSegment 2635307264 2635438336 (16470386125653 / 6250) (131769542449599 / 50000) := by
  exact
    packedTile65536 2635307264 2635438336 14 5950 51335 31 _ _ (86769 / 4000) (542307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635438336 :
    ThetaLowerSegment 2635438336 2635569408 (131769542449599 / 50000)
      (131776060985749 / 50000) := by
  exact
    packedTile65536 2635438336 2635569408 14 6010 51336 31 _ _ (216923 / 10000) (2169233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635569408 :
    ThetaLowerSegment 2635569408 2635700480 (131776060985749 / 50000)
      (263565308751063 / 100000) := by
  exact
    packedTile65536 2635569408 2635700480 14 6079 51337 31 _ _ (433847 / 20000) (1084619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635700480 :
    ThetaLowerSegment 2635700480 2635831552 (263565308751063 / 100000)
      (263578376252823 / 100000) := by
  exact
    packedTile65536 2635700480 2635831552 14 6024 51339 31 _ _ (54231 / 2500) (2169243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635831552 :
    ThetaLowerSegment 2635831552 2635962624 (263578376252823 / 100000)
      (131795720807729 / 50000) := by
  exact
    packedTile65536 2635831552 2635962624 14 6023 51340 31 _ _ (433849 / 20000) (67789 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2635962624 :
    ThetaLowerSegment 2635962624 2636093696 (131795720807729 / 50000)
      (131802239403979 / 50000) := by
  exact
    packedTile65536 2635962624 2636093696 14 6010 51341 31 _ _ (8677 / 400) (2169253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636093696 :
    ThetaLowerSegment 2636093696 2636224768 (131802239403979 / 50000) (16476094209593 / 6250) := by
  exact
    packedTile65536 2636093696 2636224768 14 6006 51342 31 _ _ (433851 / 20000) (1084629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636224768 :
    ThetaLowerSegment 2636224768 2636355840 (16476094209593 / 6250) (8238451400629 / 3125) := by
  exact
    packedTile65536 2636224768 2636355840 14 5964 51344 31 _ _ (108463 / 5000) (2169263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636355840 :
    ThetaLowerSegment 2636355840 2636486912 (8238451400629 / 3125) (131821832160519 / 50000) := by
  exact
    packedTile65536 2636355840 2636486912 14 6094 51345 31 _ _ (433853 / 20000) (542317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636486912 :
    ThetaLowerSegment 2636486912 2636617984 (131821832160519 / 50000)
      (131828400710079 / 50000) := by
  exact
    packedTile65536 2636486912 2636617984 14 6056 51346 31 _ _ (216927 / 10000) (2169273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636617984 :
    ThetaLowerSegment 2636617984 2636749056 (131828400710079 / 50000)
      (131834895519429 / 50000) := by
  exact
    packedTile65536 2636617984 2636749056 14 5988 51348 31 _ _ (86771 / 4000) (1084639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636749056 :
    ThetaLowerSegment 2636749056 2636880128 (131834895519429 / 50000)
      (131841370820229 / 50000) := by
  exact
    packedTile65536 2636749056 2636880128 14 5970 51349 31 _ _ (13558 / 625) (2169283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2636880128 :
    ThetaLowerSegment 2636880128 2637011200 (131841370820229 / 50000)
      (263695885338273 / 100000) := by
  exact
    packedTile65536 2636880128 2637011200 14 6059 51350 31 _ _ (433857 / 20000) (271161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637011200 :
    ThetaLowerSegment 2637011200 2637142272 (263695885338273 / 100000)
      (263709104991533 / 100000) := by
  exact
    packedTile65536 2637011200 2637142272 14 6094 51351 31 _ _ (216929 / 10000) (2169293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637142272 :
    ThetaLowerSegment 2637142272 2637273344 (263709104991533 / 100000)
      (131861124374969 / 50000) := by
  exact
    packedTile65536 2637142272 2637273344 14 6059 51353 31 _ _ (433859 / 20000) (1084649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637273344 :
    ThetaLowerSegment 2637273344 2637404416 (131861124374969 / 50000)
      (131867690846069 / 50000) := by
  exact
    packedTile65536 2637273344 2637404416 14 6054 51354 31 _ _ (21693 / 1000) (2169303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637404416 :
    ThetaLowerSegment 2637404416 2637535488 (131867690846069 / 50000)
      (263748490802253 / 100000) := by
  exact
    packedTile65536 2637404416 2637535488 14 6043 51355 31 _ _ (433861 / 20000) (542327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637535488 :
    ThetaLowerSegment 2637535488 2637666560 (263748490802253 / 100000)
      (263761537032593 / 100000) := by
  exact
    packedTile65536 2637535488 2637666560 14 6014 51356 31 _ _ (216931 / 10000) (2169313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637666560 :
    ThetaLowerSegment 2637666560 2637797632 (263761537032593 / 100000)
      (263774644033823 / 100000) := by
  exact
    packedTile65536 2637666560 2637797632 14 6042 51358 31 _ _ (433863 / 20000) (1084659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637797632 :
    ThetaLowerSegment 2637797632 2637928704 (263774644033823 / 100000)
      (263787748895943 / 100000) := by
  exact
    packedTile65536 2637797632 2637928704 14 6041 51359 31 _ _ (54233 / 2500) (2169323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2637928704 :
    ThetaLowerSegment 2637928704 2638059776 (263787748895943 / 100000)
      (263800899338031 / 100000) := by
  exact
    packedTile65536 2637928704 2638059776 14 6062 51360 31 _ _ (542331 / 25000) (2169327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638059776 :
    ThetaLowerSegment 2638059776 2638190848 (263800899338031 / 100000)
      (263814206002117 / 100000) := by
  exact
    packedTile65536 2638059776 2638190848 14 6134 51362 31 _ _ (2169329 / 100000) (542333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638190848 :
    ThetaLowerSegment 2638190848 2638321920 (263814206002117 / 100000)
      (263827456294189 / 100000) := by
  exact
    packedTile65536 2638190848 2638321920 14 6108 51363 31 _ _ (1084667 / 50000) (2169337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638321920 :
    ThetaLowerSegment 2638321920 2638452992 (263827456294189 / 100000)
      (26384055693241 / 10000) := by
  exact
    packedTile65536 2638321920 2638452992 14 6039 51364 31 _ _ (2169339 / 100000) (1084671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638452992 :
    ThetaLowerSegment 2638452992 2638584064 (26384055693241 / 10000) (131926948114333 / 50000) := by
  exact
    packedTile65536 2638452992 2638584064 14 6149 51365 31 _ _ (67792 / 3125) (2169347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638584064 :
    ThetaLowerSegment 2638584064 2638715136 (131926948114333 / 50000)
      (263866793008471 / 100000) := by
  exact
    packedTile65536 2638584064 2638715136 14 5945 51367 31 _ _ (2169349 / 100000) (271169 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638715136 :
    ThetaLowerSegment 2638715136 2638846208 (263866793008471 / 100000)
      (263879733205081 / 100000) := by
  exact
    packedTile65536 2638715136 2638846208 14 5965 51368 31 _ _ (1084677 / 50000) (2169357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638846208 :
    ThetaLowerSegment 2638846208 2638977280 (263879733205081 / 100000) (6597318788211 / 2500) := by
  exact
    packedTile65536 2638846208 2638977280 14 6001 51369 31 _ _ (2169359 / 100000) (1084681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2638977280 :
    ThetaLowerSegment 2638977280 2639108352 (6597318788211 / 2500) (659764365047 / 250) := by
  exact
    packedTile65536 2638977280 2639108352 14 5990 51370 31 _ _ (542341 / 25000) (2169367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639108352 :
    ThetaLowerSegment 2639108352 2639239424 (659764365047 / 250) (65979692727569 / 25000) := by
  exact
    packedTile65536 2639108352 2639239424 14 6004 51372 31 _ _ (2169369 / 100000) (542343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639239424 :
    ThetaLowerSegment 2639239424 2639370496 (65979692727569 / 25000) (131965946726801 / 50000) := by
  exact
    packedTile65536 2639239424 2639370496 14 6049 51373 31 _ _ (1084687 / 50000) (2169377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639370496 :
    ThetaLowerSegment 2639370496 2639501568 (131965946726801 / 50000) (52789002337683 / 20000) := by
  exact
    packedTile65536 2639370496 2639501568 14 6047 51374 31 _ _ (2169379 / 100000) (1084691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639501568 :
    ThetaLowerSegment 2639501568 2639632640 (52789002337683 / 20000) (52791659833083 / 20000) := by
  exact
    packedTile65536 2639501568 2639632640 14 6125 51376 31 _ _ (271173 / 12500) (2169387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639632640 :
    ThetaLowerSegment 2639632640 2639763712 (52791659833083 / 20000)
      (263971176658519 / 100000) := by
  exact
    packedTile65536 2639632640 2639763712 14 5936 51377 31 _ _ (2169389 / 100000) (135587 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639763712 :
    ThetaLowerSegment 2639763712 2639894784 (263971176658519 / 100000)
      (263984357896463 / 100000) := by
  exact
    packedTile65536 2639763712 2639894784 14 6076 51378 31 _ _ (1084697 / 50000) (2169397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2639894784 :
    ThetaLowerSegment 2639894784 2640025856 (263984357896463 / 100000)
      (263997664989929 / 100000) := by
  exact
    packedTile65536 2639894784 2640025856 14 6134 51379 31 _ _ (2169399 / 100000) (1084701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640025856 :
    ThetaLowerSegment 2640025856 2640156928 (263997664989929 / 100000)
      (264010941742409 / 100000) := by
  exact
    packedTile65536 2640025856 2640156928 14 6120 51381 31 _ _ (542351 / 25000) (2169407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640156928 :
    ThetaLowerSegment 2640156928 2640288000 (264010941742409 / 100000)
      (33002968470467 / 12500) := by
  exact
    packedTile65536 2640156928 2640288000 14 5903 51382 31 _ _ (2169409 / 100000) (542353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640288000 :
    ThetaLowerSegment 2640288000 2640419072 (33002968470467 / 12500) (66009229026679 / 25000) := by
  exact
    packedTile65536 2640288000 2640419072 14 6070 51383 31 _ _ (1084707 / 50000) (2169417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640419072 :
    ThetaLowerSegment 2640419072 2640550144 (66009229026679 / 25000)
      (264049921773621 / 100000) := by
  exact
    packedTile65536 2640419072 2640550144 14 5995 51385 31 _ _ (2169419 / 100000) (1084711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640550144 :
    ThetaLowerSegment 2640550144 2640681216 (264049921773621 / 100000)
      (264063074991333 / 100000) := by
  exact
    packedTile65536 2640550144 2640681216 14 6063 51386 31 _ _ (135589 / 6250) (2169427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640681216 :
    ThetaLowerSegment 2640681216 2640812288 (264063074991333 / 100000) (10563043489059 / 4000) := by
  exact
    packedTile65536 2640681216 2640812288 14 5998 51387 31 _ _ (2169429 / 100000) (271179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640812288 :
    ThetaLowerSegment 2640812288 2640943360 (10563043489059 / 4000) (264089227488213 / 100000) := by
  exact
    packedTile65536 2640812288 2640943360 14 6057 51388 31 _ _ (1084717 / 50000) (2169437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2640943360 :
    ThetaLowerSegment 2640943360 2641074432 (264089227488213 / 100000)
      (66025570250669 / 25000) := by
  exact
    packedTile65536 2640943360 2641074432 14 6017 51390 31 _ _ (2169439 / 100000) (1084721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641074432 :
    ThetaLowerSegment 2641074432 2641205504 (66025570250669 / 25000) (66028850449997 / 25000) := by
  exact
    packedTile65536 2641074432 2641205504 14 6048 51391 31 _ _ (542361 / 25000) (2169447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641205504 :
    ThetaLowerSegment 2641205504 2641336576 (66028850449997 / 25000)
      (264128438019029 / 100000) := by
  exact
    packedTile65536 2641205504 2641336576 14 6009 51392 31 _ _ (2169449 / 100000) (542363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641336576 :
    ThetaLowerSegment 2641336576 2641467648 (264128438019029 / 100000)
      (264141587079723 / 100000) := by
  exact
    packedTile65536 2641336576 2641467648 14 6061 51393 31 _ _ (1084727 / 50000) (2169457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641467648 :
    ThetaLowerSegment 2641467648 2641598720 (264141587079723 / 100000)
      (264154764373689 / 100000) := by
  exact
    packedTile65536 2641467648 2641598720 14 6074 51395 31 _ _ (2169459 / 100000) (1084731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641598720 :
    ThetaLowerSegment 2641598720 2641729792 (264154764373689 / 100000) (2113343967477 / 800) := by
  exact
    packedTile65536 2641598720 2641729792 14 6099 51396 31 _ _ (271183 / 12500) (2169467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641729792 :
    ThetaLowerSegment 2641729792 2641860864 (2113343967477 / 800) (264181082165601 / 100000) := by
  exact
    packedTile65536 2641729792 2641860864 14 6032 51397 31 _ _ (542367 / 25000) (2169471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641860864 :
    ThetaLowerSegment 2641860864 2641991936 (264181082165601 / 100000)
      (66048535055897 / 25000) := by
  exact
    packedTile65536 2641860864 2641991936 14 6019 51399 31 _ _ (2169473 / 100000) (542369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2641991936 :
    ThetaLowerSegment 2641991936 2642123008 (66048535055897 / 25000) (132103618681137 / 50000) := by
  exact
    packedTile65536 2641991936 2642123008 14 6037 51400 31 _ _ (1084739 / 50000) (2169481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642123008 :
    ThetaLowerSegment 2642123008 2642254080 (132103618681137 / 50000)
      (264220434327363 / 100000) := by
  exact
    packedTile65536 2642123008 2642254080 14 6083 51401 31 _ _ (2169483 / 100000) (1084743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642254080 :
    ThetaLowerSegment 2642254080 2642385152 (264220434327363 / 100000)
      (264233531526419 / 100000) := by
  exact
    packedTile65536 2642254080 2642385152 14 6037 51402 31 _ _ (135593 / 6250) (2169491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642385152 :
    ThetaLowerSegment 2642385152 2642516224 (264233531526419 / 100000)
      (264246643942111 / 100000) := by
  exact
    packedTile65536 2642385152 2642516224 14 6044 51404 31 _ _ (2169493 / 100000) (271187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642516224 :
    ThetaLowerSegment 2642516224 2642647296 (264246643942111 / 100000)
      (264259712998063 / 100000) := by
  exact
    packedTile65536 2642516224 2642647296 14 6024 51405 31 _ _ (1084749 / 50000) (2169501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642647296 :
    ThetaLowerSegment 2642647296 2642778368 (264259712998063 / 100000)
      (264272925271333 / 100000) := by
  exact
    packedTile65536 2642647296 2642778368 14 6090 51406 31 _ _ (2169503 / 100000) (1084753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642778368 :
    ThetaLowerSegment 2642778368 2642909440 (264272925271333 / 100000)
      (264285868556061 / 100000) := by
  exact
    packedTile65536 2642778368 2642909440 14 5966 51407 31 _ _ (542377 / 25000) (2169511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2642909440 :
    ThetaLowerSegment 2642909440 2643040512 (264285868556061 / 100000)
      (264299028821919 / 100000) := by
  exact
    packedTile65536 2642909440 2643040512 14 6066 51409 31 _ _ (2169513 / 100000) (542379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643040512 :
    ThetaLowerSegment 2643040512 2643171584 (264299028821919 / 100000)
      (264312152236301 / 100000) := by
  exact
    packedTile65536 2643040512 2643171584 14 6049 51410 31 _ _ (1084759 / 50000) (2169521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643171584 :
    ThetaLowerSegment 2643171584 2643302656 (264312152236301 / 100000)
      (264325191069531 / 100000) := by
  exact
    packedTile65536 2643171584 2643302656 14 6010 51411 31 _ _ (2169523 / 100000) (1084763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643302656 :
    ThetaLowerSegment 2643302656 2643433728 (264325191069531 / 100000)
      (264338262475731 / 100000) := by
  exact
    packedTile65536 2643302656 2643433728 14 6025 51413 31 _ _ (271191 / 12500) (2169531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643433728 :
    ThetaLowerSegment 2643433728 2643564800 (264338262475731 / 100000)
      (132175712516221 / 50000) := by
  exact
    packedTile65536 2643433728 2643564800 14 6067 51414 31 _ _ (2169533 / 100000) (67798 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643564800 :
    ThetaLowerSegment 2643564800 2643695872 (132175712516221 / 50000) (16522785641449 / 6250) := by
  exact
    packedTile65536 2643564800 2643695872 14 6059 51415 31 _ _ (1084769 / 50000) (2169541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643695872 :
    ThetaLowerSegment 2643695872 2643826944 (16522785641449 / 6250) (264377633081587 / 100000) := by
  exact
    packedTile65536 2643695872 2643826944 14 6021 51416 31 _ _ (2169543 / 100000) (1084773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643826944 :
    ThetaLowerSegment 2643826944 2643958016 (264377633081587 / 100000)
      (264390633013203 / 100000) := by
  exact
    packedTile65536 2643826944 2643958016 14 5992 51418 31 _ _ (542387 / 25000) (2169551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2643958016 :
    ThetaLowerSegment 2643958016 2644089088 (264390633013203 / 100000) (3305046415603 / 1250) := by
  exact
    packedTile65536 2643958016 2644089088 14 6029 51419 31 _ _ (2169553 / 100000) (542389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644089088 :
    ThetaLowerSegment 2644089088 2644220160 (3305046415603 / 1250) (132208357704667 / 50000) := by
  exact
    packedTile65536 2644089088 2644220160 14 5993 51420 31 _ _ (1084779 / 50000) (2169561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644220160 :
    ThetaLowerSegment 2644220160 2644351232 (132208357704667 / 50000)
      (264429843435047 / 100000) := by
  exact
    packedTile65536 2644220160 2644351232 14 6051 51421 31 _ _ (2169563 / 100000) (1084783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644351232 :
    ThetaLowerSegment 2644351232 2644482304 (264429843435047 / 100000)
      (264442737177671 / 100000) := by
  exact
    packedTile65536 2644351232 2644482304 14 5943 51423 31 _ _ (67799 / 3125) (2169571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644482304 :
    ThetaLowerSegment 2644482304 2644613376 (264442737177671 / 100000)
      (264455832720299 / 100000) := by
  exact
    packedTile65536 2644482304 2644613376 14 6036 51424 31 _ _ (2169573 / 100000) (271197 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644613376 :
    ThetaLowerSegment 2644613376 2644744448 (264455832720299 / 100000)
      (264469156098797 / 100000) := by
  exact
    packedTile65536 2644613376 2644744448 14 6141 51425 31 _ _ (1084789 / 50000) (2169581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644744448 :
    ThetaLowerSegment 2644744448 2644875520 (264469156098797 / 100000)
      (132241042321947 / 50000) := by
  exact
    packedTile65536 2644744448 2644875520 14 5959 51427 31 _ _ (2169583 / 100000) (1084793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2644875520 :
    ThetaLowerSegment 2644875520 2645006592 (132241042321947 / 50000) (33061906754623 / 12500) := by
  exact
    packedTile65536 2644875520 2645006592 14 6070 51428 31 _ _ (2169587 / 100000) (216959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645006592 :
    ThetaLowerSegment 2645006592 2645137664 (33061906754623 / 12500) (33063540999797 / 12500) := by
  exact
    packedTile65536 2645006592 2645137664 14 6026 51429 31 _ _ (271199 / 12500) (433919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645137664 :
    ThetaLowerSegment 2645137664 2645268736 (33063540999797 / 12500)
      (264521326054003 / 100000) := by
  exact
    packedTile65536 2645137664 2645268736 14 5991 51430 31 _ _ (2169597 / 100000) (2712 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645268736 :
    ThetaLowerSegment 2645268736 2645399808 (264521326054003 / 100000)
      (52906869167121 / 20000) := by
  exact
    packedTile65536 2645268736 2645399808 14 6001 51432 31 _ _ (1084801 / 50000) (433921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645399808 :
    ThetaLowerSegment 2645399808 2645530880 (52906869167121 / 20000) (33068430469133 / 12500) := by
  exact
    packedTile65536 2645399808 2645530880 14 6037 51433 31 _ _ (2169607 / 100000) (216961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645530880 :
    ThetaLowerSegment 2645530880 2645661952 (33068430469133 / 12500) (33070073950223 / 12500) := by
  exact
    packedTile65536 2645530880 2645661952 14 6060 51434 31 _ _ (542403 / 25000) (433923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645661952 :
    ThetaLowerSegment 2645661952 2645793024 (33070073950223 / 12500)
      (264573672222677 / 100000) := by
  exact
    packedTile65536 2645661952 2645793024 14 6029 51435 31 _ _ (2169617 / 100000) (108481 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645793024 :
    ThetaLowerSegment 2645793024 2645924096 (264573672222677 / 100000)
      (264586837488973 / 100000) := by
  exact
    packedTile65536 2645793024 2645924096 14 6068 51437 31 _ _ (1084811 / 50000) (17357 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2645924096 :
    ThetaLowerSegment 2645924096 2646055168 (264586837488973 / 100000)
      (52919999689271 / 20000) := by
  exact
    packedTile65536 2645924096 2646055168 14 6066 51438 31 _ _ (2169627 / 100000) (216963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646055168 :
    ThetaLowerSegment 2646055168 2646186240 (52919999689271 / 20000)
      (264613152925171 / 100000) := by
  exact
    packedTile65536 2646055168 2646186240 14 6063 51439 31 _ _ (67801 / 3125) (433927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646186240 :
    ThetaLowerSegment 2646186240 2646317312 (264613152925171 / 100000)
      (264626179425719 / 100000) := by
  exact
    packedTile65536 2646186240 2646317312 14 6004 51441 31 _ _ (2169637 / 100000) (54241 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646317312 :
    ThetaLowerSegment 2646317312 2646448384 (264626179425719 / 100000)
      (264639251518769 / 100000) := by
  exact
    packedTile65536 2646317312 2646448384 14 6025 51442 31 _ _ (1084821 / 50000) (433929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646448384 :
    ThetaLowerSegment 2646448384 2646579456 (264639251518769 / 100000)
      (132326220401441 / 50000) := by
  exact
    packedTile65536 2646448384 2646579456 14 6079 51443 31 _ _ (2169647 / 100000) (43393 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646579456 :
    ThetaLowerSegment 2646579456 2646710528 (132326220401441 / 50000)
      (132332751053961 / 50000) := by
  exact
    packedTile65536 2646579456 2646710528 14 6020 51444 31 _ _ (542413 / 25000) (433931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646710528 :
    ThetaLowerSegment 2646710528 2646841600 (132332751053961 / 50000) (10587147658113 / 4000) := by
  exact
    packedTile65536 2646710528 2646841600 14 6079 51446 31 _ _ (2169657 / 100000) (108483 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646841600 :
    ThetaLowerSegment 2646841600 2646972672 (10587147658113 / 4000) (264691737630431 / 100000) := by
  exact
    packedTile65536 2646841600 2646972672 14 6013 51447 31 _ _ (1084831 / 50000) (433933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2646972672 :
    ThetaLowerSegment 2646972672 2647103744 (264691737630431 / 100000)
      (132352344186377 / 50000) := by
  exact
    packedTile65536 2646972672 2647103744 14 5969 51448 31 _ _ (2169667 / 100000) (216967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647103744 :
    ThetaLowerSegment 2647103744 2647234816 (132352344186377 / 50000)
      (132358941074093 / 50000) := by
  exact
    packedTile65536 2647103744 2647234816 14 6081 51450 31 _ _ (271209 / 12500) (86787 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647234816 :
    ThetaLowerSegment 2647234816 2647365888 (132358941074093 / 50000)
      (264731036899837 / 100000) := by
  exact
    packedTile65536 2647234816 2647365888 14 6063 51451 31 _ _ (2169677 / 100000) (27121 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647365888 :
    ThetaLowerSegment 2647365888 2647496960 (264731036899837 / 100000)
      (264744174324347 / 100000) := by
  exact
    packedTile65536 2647365888 2647496960 14 6055 51452 31 _ _ (1084841 / 50000) (433937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647496960 :
    ThetaLowerSegment 2647496960 2647628032 (264744174324347 / 100000)
      (264757153391981 / 100000) := by
  exact
    packedTile65536 2647496960 2647628032 14 5982 51453 31 _ _ (2169687 / 100000) (216969 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647628032 :
    ThetaLowerSegment 2647628032 2647759104 (264757153391981 / 100000)
      (66192610687339 / 25000) := by
  exact
    packedTile65536 2647628032 2647759104 14 6125 51455 31 _ _ (2169691 / 100000) (1084847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647759104 :
    ThetaLowerSegment 2647759104 2647890176 (66192610687339 / 25000) (66195857094979 / 25000) := by
  exact
    packedTile65536 2647759104 2647890176 14 5985 51456 31 _ _ (67803 / 3125) (2169699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2647890176 :
    ThetaLowerSegment 2647890176 2648021248 (66195857094979 / 25000)
      (264796670065119 / 100000) := by
  exact
    packedTile65536 2647890176 2648021248 14 6103 51457 31 _ _ (2169701 / 100000) (271213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648021248 :
    ThetaLowerSegment 2648021248 2648152320 (264796670065119 / 100000)
      (264809705658767 / 100000) := by
  exact
    packedTile65536 2648021248 2648152320 14 6008 51458 31 _ _ (1084853 / 50000) (2169709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648152320 :
    ThetaLowerSegment 2648152320 2648283392 (264809705658767 / 100000)
      (33102872765047 / 12500) := by
  exact
    packedTile65536 2648152320 2648283392 14 6119 51460 31 _ _ (2169711 / 100000) (1084857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648283392 :
    ThetaLowerSegment 2648283392 2648414464 (33102872765047 / 12500) (66209000646523 / 25000) := by
  exact
    packedTile65536 2648283392 2648414464 14 6001 51461 31 _ _ (542429 / 25000) (2169719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648414464 :
    ThetaLowerSegment 2648414464 2648545536 (66209000646523 / 25000) (26484905996707 / 10000) := by
  exact
    packedTile65536 2648414464 2648545536 14 6018 51462 31 _ _ (2169721 / 100000) (542431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648545536 :
    ThetaLowerSegment 2648545536 2648676608 (26484905996707 / 10000) (132430982748659 / 50000) := by
  exact
    packedTile65536 2648545536 2648676608 14 5948 51464 31 _ _ (1084863 / 50000) (2169729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648676608 :
    ThetaLowerSegment 2648676608 2648807680 (132430982748659 / 50000) (52974991135363 / 20000) := by
  exact
    packedTile65536 2648676608 2648807680 14 5987 51465 31 _ _ (2169731 / 100000) (1084867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648807680 :
    ThetaLowerSegment 2648807680 2648938752 (52974991135363 / 20000)
      (264888130313807 / 100000) := by
  exact
    packedTile65536 2648807680 2648938752 14 6072 51466 31 _ _ (271217 / 12500) (2169739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2648938752 :
    ThetaLowerSegment 2648938752 2649069824 (264888130313807 / 100000)
      (26490124205867 / 10000) := by
  exact
    packedTile65536 2648938752 2649069824 14 6043 51467 31 _ _ (2169741 / 100000) (135609 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649069824 :
    ThetaLowerSegment 2649069824 2649200896 (26490124205867 / 10000) (2649141628961 / 1000) := by
  exact
    packedTile65536 2649069824 2649200896 14 5955 51469 31 _ _ (1084873 / 50000) (2169749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649200896 :
    ThetaLowerSegment 2649200896 2649331968 (2649141628961 / 1000) (33115909608893 / 12500) := by
  exact
    packedTile65536 2649200896 2649331968 14 6044 51470 31 _ _ (2169751 / 100000) (1084877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649331968 :
    ThetaLowerSegment 2649331968 2649463040 (33115909608893 / 12500) (66235113449833 / 25000) := by
  exact
    packedTile65536 2649331968 2649463040 14 6073 51471 31 _ _ (542439 / 25000) (2169759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649463040 :
    ThetaLowerSegment 2649463040 2649594112 (66235113449833 / 25000) (132476812124301 / 50000) := by
  exact
    packedTile65536 2649463040 2649594112 14 6070 51472 31 _ _ (2169761 / 100000) (542441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649594112 :
    ThetaLowerSegment 2649594112 2649725184 (132476812124301 / 50000)
      (132483323592067 / 50000) := by
  exact
    packedTile65536 2649594112 2649725184 14 6002 51474 31 _ _ (1084883 / 50000) (2169769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649725184 :
    ThetaLowerSegment 2649725184 2649856256 (132483323592067 / 50000)
      (264979780807997 / 100000) := by
  exact
    packedTile65536 2649725184 2649856256 14 6053 51475 31 _ _ (2169771 / 100000) (1084887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649856256 :
    ThetaLowerSegment 2649856256 2649987328 (264979780807997 / 100000)
      (52998591571529 / 20000) := by
  exact
    packedTile65536 2649856256 2649987328 14 6073 51476 31 _ _ (135611 / 6250) (2169779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2649987328 :
    ThetaLowerSegment 2649987328 2650118400 (52998591571529 / 20000) (33125777173667 / 12500) := by
  exact
    packedTile65536 2649987328 2650118400 14 6111 51478 31 _ _ (2169781 / 100000) (271223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650118400 :
    ThetaLowerSegment 2650118400 2650249472 (33125777173667 / 12500) (132509699419643 / 50000) := by
  exact
    packedTile65536 2650118400 2650249472 14 6075 51479 31 _ _ (1084893 / 50000) (2169789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650249472 :
    ThetaLowerSegment 2650249472 2650380544 (132509699419643 / 50000)
      (132516295581243 / 50000) := by
  exact
    packedTile65536 2650249472 2650380544 14 6080 51480 31 _ _ (216979 / 10000) (2169793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650380544 :
    ThetaLowerSegment 2650380544 2650511616 (132516295581243 / 50000)
      (265045733610801 / 100000) := by
  exact
    packedTile65536 2650380544 2650511616 14 6057 51481 31 _ _ (433959 / 20000) (1084899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650511616 :
    ThetaLowerSegment 2650511616 2650642688 (265045733610801 / 100000)
      (265058726373201 / 100000) := by
  exact
    packedTile65536 2650511616 2650642688 14 5988 51483 31 _ _ (10849 / 500) (2169803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650642688 :
    ThetaLowerSegment 2650642688 2650773760 (265058726373201 / 100000)
      (66267987833669 / 25000) := by
  exact
    packedTile65536 2650642688 2650773760 14 6095 51484 31 _ _ (433961 / 20000) (135613 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650773760 :
    ThetaLowerSegment 2650773760 2650904832 (66267987833669 / 25000) (132542516559583 / 50000) := by
  exact
    packedTile65536 2650773760 2650904832 14 6029 51485 31 _ _ (216981 / 10000) (2169813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2650904832 :
    ThetaLowerSegment 2650904832 2651035904 (132542516559583 / 50000) (66274535785349 / 25000) := by
  exact
    packedTile65536 2650904832 2651035904 14 6042 51486 31 _ _ (433963 / 20000) (1084909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651035904 :
    ThetaLowerSegment 2651035904 2651166976 (66274535785349 / 25000) (66277790515349 / 25000) := by
  exact
    packedTile65536 2651035904 2651166976 14 6000 51488 31 _ _ (108491 / 5000) (2169823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651166976 :
    ThetaLowerSegment 2651166976 2651298048 (66277790515349 / 25000)
      (265124105067521 / 100000) := by
  exact
    packedTile65536 2651166976 2651298048 14 5965 51489 31 _ _ (86793 / 4000) (542457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651298048 :
    ThetaLowerSegment 2651298048 2651429120 (265124105067521 / 100000)
      (265137006876701 / 100000) := by
  exact
    packedTile65536 2651298048 2651429120 14 5946 51490 31 _ _ (216983 / 10000) (2169833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651429120 :
    ThetaLowerSegment 2651429120 2651560192 (265137006876701 / 100000)
      (265150234190861 / 100000) := by
  exact
    packedTile65536 2651429120 2651560192 14 6096 51492 31 _ _ (433967 / 20000) (1084919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651560192 :
    ThetaLowerSegment 2651560192 2651691264 (265150234190861 / 100000)
      (265163455025981 / 100000) := by
  exact
    packedTile65536 2651560192 2651691264 14 6093 51493 31 _ _ (27123 / 1250) (2169843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651691264 :
    ThetaLowerSegment 2651691264 2651822336 (265163455025981 / 100000)
      (265176387302181 / 100000) := by
  exact
    packedTile65536 2651691264 2651822336 14 5960 51494 31 _ _ (433969 / 20000) (271231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651822336 :
    ThetaLowerSegment 2651822336 2651953408 (265176387302181 / 100000)
      (265189443289631 / 100000) := by
  exact
    packedTile65536 2651822336 2651953408 14 6017 51495 31 _ _ (43397 / 2000) (2169853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2651953408 :
    ThetaLowerSegment 2651953408 2652084480 (265189443289631 / 100000)
      (265202557893251 / 100000) := by
  exact
    packedTile65536 2651953408 2652084480 14 6044 51497 31 _ _ (433971 / 20000) (1084929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652084480 :
    ThetaLowerSegment 2652084480 2652215552 (265202557893251 / 100000)
      (265215596581991 / 100000) := by
  exact
    packedTile65536 2652084480 2652215552 14 6009 51498 31 _ _ (108493 / 5000) (2169863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652215552 :
    ThetaLowerSegment 2652215552 2652346624 (265215596581991 / 100000)
      (265228641810371 / 100000) := by
  exact
    packedTile65536 2652215552 2652346624 14 6012 51499 31 _ _ (433973 / 20000) (542467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652346624 :
    ThetaLowerSegment 2652346624 2652477696 (265228641810371 / 100000)
      (265241776033481 / 100000) := by
  exact
    packedTile65536 2652346624 2652477696 14 6053 51500 31 _ _ (216987 / 10000) (2169873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652477696 :
    ThetaLowerSegment 2652477696 2652608768 (265241776033481 / 100000)
      (132627444294053 / 50000) := by
  exact
    packedTile65536 2652477696 2652608768 14 6043 51502 31 _ _ (17359 / 800) (1084939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652608768 :
    ThetaLowerSegment 2652608768 2652739840 (132627444294053 / 50000)
      (265268009846419 / 100000) := by
  exact
    packedTile65536 2652608768 2652739840 14 6047 51503 31 _ _ (2169879 / 100000) (1084941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652739840 :
    ThetaLowerSegment 2652739840 2652870912 (265268009846419 / 100000)
      (265280992262391 / 100000) := by
  exact
    packedTile65536 2652739840 2652870912 14 5983 51504 31 _ _ (542471 / 25000) (2169887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2652870912 :
    ThetaLowerSegment 2652870912 2653001984 (265280992262391 / 100000) (8290443897391 / 3125) := by
  exact
    packedTile65536 2652870912 2653001984 14 6089 51506 31 _ _ (2169889 / 100000) (542473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653001984 :
    ThetaLowerSegment 2653001984 2653133056 (8290443897391 / 3125) (132653578406899 / 50000) := by
  exact
    packedTile65536 2653001984 2653133056 14 5969 51507 31 _ _ (1084947 / 50000) (2169897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653133056 :
    ThetaLowerSegment 2653133056 2653264128 (132653578406899 / 50000) (10612813384417 / 4000) := by
  exact
    packedTile65536 2653133056 2653264128 14 6073 51508 31 _ _ (2169899 / 100000) (1084951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653264128 :
    ThetaLowerSegment 2653264128 2653395200 (10612813384417 / 4000) (265333575364633 / 100000) := by
  exact
    packedTile65536 2653264128 2653395200 14 6102 51509 31 _ _ (135619 / 6250) (2169907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653395200 :
    ThetaLowerSegment 2653395200 2653526272 (265333575364633 / 100000)
      (265346707653901 / 100000) := by
  exact
    packedTile65536 2653395200 2653526272 14 6052 51511 31 _ _ (2169909 / 100000) (271239 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653526272 :
    ThetaLowerSegment 2653526272 2653657344 (265346707653901 / 100000)
      (265359922430161 / 100000) := by
  exact
    packedTile65536 2653526272 2653657344 14 6090 51512 31 _ _ (1084957 / 50000) (2169917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653657344 :
    ThetaLowerSegment 2653657344 2653788416 (265359922430161 / 100000)
      (132686478566797 / 50000) := by
  exact
    packedTile65536 2653657344 2653788416 14 6007 51513 31 _ _ (2169919 / 100000) (1084961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653788416 :
    ThetaLowerSegment 2653788416 2653919488 (132686478566797 / 50000)
      (132692991593683 / 50000) := by
  exact
    packedTile65536 2653788416 2653919488 14 6003 51514 31 _ _ (542481 / 25000) (2169927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2653919488 :
    ThetaLowerSegment 2653919488 2654050560 (132692991593683 / 50000)
      (265399169845899 / 100000) := by
  exact
    packedTile65536 2653919488 2654050560 14 6077 51516 31 _ _ (2169929 / 100000) (542483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654050560 :
    ThetaLowerSegment 2654050560 2654181632 (265399169845899 / 100000)
      (265412213319173 / 100000) := by
  exact
    packedTile65536 2654050560 2654181632 14 6011 51517 31 _ _ (1084967 / 50000) (2169937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654181632 :
    ThetaLowerSegment 2654181632 2654312704 (265412213319173 / 100000)
      (26542528286177 / 10000) := by
  exact
    packedTile65536 2654181632 2654312704 14 6023 51518 31 _ _ (2169939 / 100000) (1084971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654312704 :
    ThetaLowerSegment 2654312704 2654443776 (26542528286177 / 10000) (132719192491821 / 50000) := by
  exact
    packedTile65536 2654312704 2654443776 14 6038 51520 31 _ _ (271243 / 12500) (2169947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654443776 :
    ThetaLowerSegment 2654443776 2654574848 (132719192491821 / 50000) (16590729880701 / 6250) := by
  exact
    packedTile65536 2654443776 2654574848 14 6126 51521 31 _ _ (2169949 / 100000) (67811 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654574848 :
    ThetaLowerSegment 2654574848 2654705920 (16590729880701 / 6250) (6636619398339 / 2500) := by
  exact
    packedTile65536 2654574848 2654705920 14 6036 51522 31 _ _ (1084977 / 50000) (2169957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654705920 :
    ThetaLowerSegment 2654705920 2654836992 (6636619398339 / 2500) (132738955344667 / 50000) := by
  exact
    packedTile65536 2654705920 2654836992 14 6053 51523 31 _ _ (1084979 / 50000) (2169961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654836992 :
    ThetaLowerSegment 2654836992 2654968064 (132738955344667 / 50000)
      (132745517312779 / 50000) := by
  exact
    packedTile65536 2654836992 2654968064 14 6048 51525 31 _ _ (2169963 / 100000) (1084983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2654968064 :
    ThetaLowerSegment 2654968064 2655099136 (132745517312779 / 50000)
      (132752132460227 / 50000) := by
  exact
    packedTile65536 2654968064 2655099136 14 6097 51526 31 _ _ (135623 / 6250) (2169971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655099136 :
    ThetaLowerSegment 2655099136 2655230208 (132752132460227 / 50000) (8297417454298 / 3125) := by
  exact
    packedTile65536 2655099136 2655230208 14 6034 51527 31 _ _ (2169973 / 100000) (271247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655230208 :
    ThetaLowerSegment 2655230208 2655361280 (8297417454298 / 3125) (33191328765373 / 12500) := by
  exact
    packedTile65536 2655230208 2655361280 14 6116 51528 31 _ _ (1084989 / 50000) (2169981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655361280 :
    ThetaLowerSegment 2655361280 2655492352 (33191328765373 / 12500)
      (265543760690117 / 100000) := by
  exact
    packedTile65536 2655361280 2655492352 14 6051 51530 31 _ _ (2169983 / 100000) (1084993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655492352 :
    ThetaLowerSegment 2655492352 2655623424 (265543760690117 / 100000)
      (265556867417637 / 100000) := by
  exact
    packedTile65536 2655492352 2655623424 14 6040 51531 31 _ _ (542497 / 25000) (2169991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655623424 :
    ThetaLowerSegment 2655623424 2655754496 (265556867417637 / 100000)
      (265570134754839 / 100000) := by
  exact
    packedTile65536 2655623424 2655754496 14 6114 51532 31 _ _ (2169993 / 100000) (542499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655754496 :
    ThetaLowerSegment 2655754496 2655885568 (265570134754839 / 100000)
      (265583356552653 / 100000) := by
  exact
    packedTile65536 2655754496 2655885568 14 6093 51534 31 _ _ (1084999 / 50000) (2170001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2655885568 :
    ThetaLowerSegment 2655885568 2656016640 (265583356552653 / 100000)
      (26559650460083 / 10000) := by
  exact
    packedTile65536 2655885568 2656016640 14 6059 51535 31 _ _ (2170003 / 100000) (1085003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656016640 :
    ThetaLowerSegment 2656016640 2656147712 (26559650460083 / 10000) (132804872994823 / 50000) := by
  exact
    packedTile65536 2656016640 2656147712 14 6102 51536 31 _ _ (271251 / 12500) (2170011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656147712 :
    ThetaLowerSegment 2656147712 2656278784 (132804872994823 / 50000) (1660141989546 / 625) := by
  exact
    packedTile65536 2656147712 2656278784 14 5978 51537 31 _ _ (2170013 / 100000) (67813 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656278784 :
    ThetaLowerSegment 2656278784 2656409856 (1660141989546 / 625) (16602241247273 / 6250) := by
  exact
    packedTile65536 2656278784 2656409856 14 6056 51539 31 _ _ (1085009 / 50000) (2170021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656409856 :
    ThetaLowerSegment 2656409856 2656540928 (16602241247273 / 6250) (132824450897299 / 50000) := by
  exact
    packedTile65536 2656409856 2656540928 14 6010 51540 31 _ _ (2170023 / 100000) (1085013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656540928 :
    ThetaLowerSegment 2656540928 2656672000 (132824450897299 / 50000)
      (132830982681579 / 50000) := by
  exact
    packedTile65536 2656540928 2656672000 14 6020 51541 31 _ _ (542507 / 25000) (2170031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656672000 :
    ThetaLowerSegment 2656672000 2656803072 (132830982681579 / 50000)
      (265675109253039 / 100000) := by
  exact
    packedTile65536 2656672000 2656803072 14 6057 51542 31 _ _ (2170033 / 100000) (542509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656803072 :
    ThetaLowerSegment 2656803072 2656934144 (265675109253039 / 100000)
      (265688207596371 / 100000) := by
  exact
    packedTile65536 2656803072 2656934144 14 6036 51544 31 _ _ (2170037 / 100000) (54251 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2656934144 :
    ThetaLowerSegment 2656934144 2657065216 (265688207596371 / 100000)
      (265701540334419 / 100000) := by
  exact
    packedTile65536 2656934144 2657065216 14 6144 51545 31 _ _ (1085021 / 50000) (434009 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657065216 :
    ThetaLowerSegment 2657065216 2657196288 (265701540334419 / 100000)
      (265714612697547 / 100000) := by
  exact
    packedTile65536 2657065216 2657196288 14 6024 51546 31 _ _ (2170047 / 100000) (43401 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657196288 :
    ThetaLowerSegment 2657196288 2657327360 (265714612697547 / 100000)
      (265727871715267 / 100000) := by
  exact
    packedTile65536 2657196288 2657327360 14 6110 51547 31 _ _ (542513 / 25000) (434011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657327360 :
    ThetaLowerSegment 2657327360 2657458432 (265727871715267 / 100000)
      (132870457963947 / 50000) := by
  exact
    packedTile65536 2657327360 2657458432 14 6011 51549 31 _ _ (2170057 / 100000) (108503 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657458432 :
    ThetaLowerSegment 2657458432 2657589504 (132870457963947 / 50000)
      (132876996360753 / 50000) := by
  exact
    packedTile65536 2657458432 2657589504 14 6026 51550 31 _ _ (1085031 / 50000) (434013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657589504 :
    ThetaLowerSegment 2657589504 2657720576 (132876996360753 / 50000) (53153414343063 / 20000) := by
  exact
    packedTile65536 2657589504 2657720576 14 6027 51551 31 _ _ (2170067 / 100000) (217007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657720576 :
    ThetaLowerSegment 2657720576 2657851648 (53153414343063 / 20000)
      (265780096487459 / 100000) := by
  exact
    packedTile65536 2657720576 2657851648 14 6002 51553 31 _ _ (271259 / 12500) (86803 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657851648 :
    ThetaLowerSegment 2657851648 2657982720 (265780096487459 / 100000)
      (265793116949459 / 100000) := by
  exact
    packedTile65536 2657851648 2657982720 14 6000 51554 31 _ _ (2170077 / 100000) (13563 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2657982720 :
    ThetaLowerSegment 2657982720 2658113792 (265793116949459 / 100000)
      (265806020257031 / 100000) := by
  exact
    packedTile65536 2657982720 2658113792 14 5946 51555 31 _ _ (1085041 / 50000) (434017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658113792 :
    ThetaLowerSegment 2658113792 2658244864 (265806020257031 / 100000)
      (265819205705643 / 100000) := by
  exact
    packedTile65536 2658113792 2658244864 14 6076 51556 31 _ _ (2170087 / 100000) (217009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658244864 :
    ThetaLowerSegment 2658244864 2658375936 (265819205705643 / 100000)
      (265832287020219 / 100000) := by
  exact
    packedTile65536 2658244864 2658375936 14 6028 51558 31 _ _ (542523 / 25000) (434019 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658375936 :
    ThetaLowerSegment 2658375936 2658507008 (265832287020219 / 100000)
      (132922730839553 / 50000) := by
  exact
    packedTile65536 2658375936 2658507008 14 6071 51559 31 _ _ (2170097 / 100000) (21701 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658507008 :
    ThetaLowerSegment 2658507008 2658638080 (132922730839553 / 50000) (66464611349843 / 25000) := by
  exact
    packedTile65536 2658507008 2658638080 14 5983 51560 31 _ _ (1085051 / 50000) (434021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658638080 :
    ThetaLowerSegment 2658638080 2658769152 (66464611349843 / 25000) (5317434225147 / 2000) := by
  exact
    packedTile65536 2658638080 2658769152 14 6113 51561 31 _ _ (1085053 / 50000) (2170109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658769152 :
    ThetaLowerSegment 2658769152 2658900224 (5317434225147 / 2000) (66471192746337 / 25000) := by
  exact
    packedTile65536 2658769152 2658900224 14 6018 51563 31 _ _ (2170111 / 100000) (1085057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2658900224 :
    ThetaLowerSegment 2658900224 2659031296 (66471192746337 / 25000) (66474506513469 / 25000) := by
  exact
    packedTile65536 2658900224 2659031296 14 6108 51564 31 _ _ (542529 / 25000) (2170119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659031296 :
    ThetaLowerSegment 2659031296 2659162368 (66474506513469 / 25000)
      (265911257281613 / 100000) := by
  exact
    packedTile65536 2659031296 2659162368 14 6097 51565 31 _ _ (2170121 / 100000) (542531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659162368 :
    ThetaLowerSegment 2659162368 2659293440 (265911257281613 / 100000)
      (265924236805219 / 100000) := by
  exact
    packedTile65536 2659162368 2659293440 14 5981 51567 31 _ _ (1085063 / 50000) (2170129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659293440 :
    ThetaLowerSegment 2659293440 2659424512 (265924236805219 / 100000) (16621076293687 / 6250) := by
  exact
    packedTile65536 2659293440 2659424512 14 5983 51568 31 _ _ (2170131 / 100000) (1085067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659424512 :
    ThetaLowerSegment 2659424512 2659555584 (16621076293687 / 6250) (3324379321019 / 1250) := by
  exact
    packedTile65536 2659424512 2659555584 14 6048 51569 31 _ _ (271267 / 12500) (2170139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659555584 :
    ThetaLowerSegment 2659555584 2659686656 (3324379321019 / 1250) (265963394739353 / 100000) := by
  exact
    packedTile65536 2659555584 2659686656 14 6013 51570 31 _ _ (2170141 / 100000) (67817 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659686656 :
    ThetaLowerSegment 2659686656 2659817728 (265963394739353 / 100000)
      (265976328809513 / 100000) := by
  exact
    packedTile65536 2659686656 2659817728 14 5960 51572 31 _ _ (1085073 / 50000) (2170149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659817728 :
    ThetaLowerSegment 2659817728 2659948800 (265976328809513 / 100000)
      (66497348822171 / 25000) := by
  exact
    packedTile65536 2659817728 2659948800 14 6021 51573 31 _ _ (2170151 / 100000) (1085077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2659948800 :
    ThetaLowerSegment 2659948800 2660079872 (66497348822171 / 25000) (16625156846337 / 6250) := by
  exact
    packedTile65536 2659948800 2660079872 14 6043 51574 31 _ _ (542539 / 25000) (2170159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660079872 :
    ThetaLowerSegment 2660079872 2660210944 (16625156846337 / 6250) (266015593442061 / 100000) := by
  exact
    packedTile65536 2660079872 2660210944 14 6029 51575 31 _ _ (2170161 / 100000) (542541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660210944 :
    ThetaLowerSegment 2660210944 2660342016 (266015593442061 / 100000)
      (266028627459057 / 100000) := by
  exact
    packedTile65536 2660210944 2660342016 14 6006 51577 31 _ _ (1085083 / 50000) (2170169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660342016 :
    ThetaLowerSegment 2660342016 2660473088 (266028627459057 / 100000)
      (66510438705859 / 25000) := by
  exact
    packedTile65536 2660342016 2660473088 14 6049 51578 31 _ _ (2170171 / 100000) (1085087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660473088 :
    ThetaLowerSegment 2660473088 2660604160 (66510438705859 / 25000) (66513689628009 / 25000) := by
  exact
    packedTile65536 2660473088 2660604160 14 5992 51579 31 _ _ (86807 / 4000) (1085089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660604160 :
    ThetaLowerSegment 2660604160 2660735232 (66513689628009 / 25000) (66516973110349 / 25000) := by
  exact
    packedTile65536 2660604160 2660735232 14 6052 51581 31 _ _ (108509 / 5000) (2170183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660735232 :
    ThetaLowerSegment 2660735232 2660866304 (66516973110349 / 25000) (133040393840333 / 50000) := by
  exact
    packedTile65536 2660735232 2660866304 14 5942 51582 31 _ _ (434037 / 20000) (542547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660866304 :
    ThetaLowerSegment 2660866304 2660997376 (133040393840333 / 50000)
      (133046943473753 / 50000) := by
  exact
    packedTile65536 2660866304 2660997376 14 6036 51583 31 _ _ (217019 / 10000) (2170193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2660997376 :
    ThetaLowerSegment 2660997376 2661128448 (133046943473753 / 50000)
      (266107088243691 / 100000) := by
  exact
    packedTile65536 2660997376 2661128448 14 6083 51584 31 _ _ (434039 / 20000) (1085099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661128448 :
    ThetaLowerSegment 2661128448 2661259520 (266107088243691 / 100000)
      (266120324293491 / 100000) := by
  exact
    packedTile65536 2661128448 2661259520 14 6099 51586 31 _ _ (10851 / 500) (2170203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661259520 :
    ThetaLowerSegment 2661259520 2661390592 (266120324293491 / 100000)
      (266133276076931 / 100000) := by
  exact
    packedTile65536 2661259520 2661390592 14 5968 51587 31 _ _ (434041 / 20000) (67819 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661390592 :
    ThetaLowerSegment 2661390592 2661521664 (266133276076931 / 100000)
      (266146416698481 / 100000) := by
  exact
    packedTile65536 2661390592 2661521664 14 6055 51588 31 _ _ (217021 / 10000) (2170213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661521664 :
    ThetaLowerSegment 2661521664 2661652736 (266146416698481 / 100000)
      (266159589903531 / 100000) := by
  exact
    packedTile65536 2661521664 2661652736 14 6070 51589 31 _ _ (434043 / 20000) (1085109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661652736 :
    ThetaLowerSegment 2661652736 2661783808 (266159589903531 / 100000)
      (266172841266851 / 100000) := by
  exact
    packedTile65536 2661652736 2661783808 14 6106 51591 31 _ _ (108511 / 5000) (2170223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661783808 :
    ThetaLowerSegment 2661783808 2661914880 (266172841266851 / 100000)
      (66546461856319 / 25000) := by
  exact
    packedTile65536 2661783808 2661914880 14 5993 51592 31 _ _ (86809 / 4000) (542557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2661914880 :
    ThetaLowerSegment 2661914880 2662045952 (66546461856319 / 25000) (33274883015747 / 12500) := by
  exact
    packedTile65536 2661914880 2662045952 14 6090 51593 31 _ _ (217023 / 10000) (2170233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662045952 :
    ThetaLowerSegment 2662045952 2662177024 (33274883015747 / 12500) (33276510691997 / 12500) := by
  exact
    packedTile65536 2662045952 2662177024 14 6000 51595 31 _ _ (434047 / 20000) (1085119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662177024 :
    ThetaLowerSegment 2662177024 2662308096 (33276510691997 / 12500) (33278142441197 / 12500) := by
  exact
    packedTile65536 2662177024 2662308096 14 6015 51596 31 _ _ (13564 / 625) (2170243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662308096 :
    ThetaLowerSegment 2662308096 2662439168 (33278142441197 / 12500) (16639892929233 / 6250) := by
  exact
    packedTile65536 2662308096 2662439168 14 6058 51597 31 _ _ (542561 / 25000) (2170247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662439168 :
    ThetaLowerSegment 2662439168 2662570240 (16639892929233 / 6250) (26625152104613 / 10000) := by
  exact
    packedTile65536 2662439168 2662570240 14 6098 51598 31 _ _ (2170249 / 100000) (542563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662570240 :
    ThetaLowerSegment 2662570240 2662701312 (26625152104613 / 10000) (5325287813047 / 2000) := by
  exact
    packedTile65536 2662570240 2662701312 14 5930 51600 31 _ _ (1085127 / 50000) (2170257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662701312 :
    ThetaLowerSegment 2662701312 2662832384 (5325287813047 / 2000) (66569397541897 / 25000) := by
  exact
    packedTile65536 2662701312 2662832384 14 6082 51601 31 _ _ (2170259 / 100000) (1085131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662832384 :
    ThetaLowerSegment 2662832384 2662963456 (66569397541897 / 25000) (66572651310199 / 25000) := by
  exact
    packedTile65536 2662832384 2662963456 14 5997 51602 31 _ _ (271283 / 12500) (2170267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2662963456 :
    ThetaLowerSegment 2662963456 2663094528 (66572651310199 / 25000) (53260747507703 / 20000) := by
  exact
    packedTile65536 2662963456 2663094528 14 6051 51603 31 _ _ (2170269 / 100000) (67821 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663094528 :
    ThetaLowerSegment 2663094528 2663225600 (53260747507703 / 20000)
      (266316876377311 / 100000) := by
  exact
    packedTile65536 2663094528 2663225600 14 6054 51605 31 _ _ (1085137 / 50000) (2170277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663225600 :
    ThetaLowerSegment 2663225600 2663356672 (266316876377311 / 100000)
      (66582454437747 / 25000) := by
  exact
    packedTile65536 2663225600 2663356672 14 5963 51606 31 _ _ (2170279 / 100000) (1085141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663356672 :
    ThetaLowerSegment 2663356672 2663487744 (66582454437747 / 25000) (33292871480289 / 12500) := by
  exact
    packedTile65536 2663356672 2663487744 14 6061 51607 31 _ _ (542571 / 25000) (2170287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663487744 :
    ThetaLowerSegment 2663487744 2663618816 (33292871480289 / 12500) (16647257194531 / 6250) := by
  exact
    packedTile65536 2663487744 2663618816 14 6056 51608 31 _ _ (2170289 / 100000) (542573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663618816 :
    ThetaLowerSegment 2663618816 2663749888 (16647257194531 / 6250) (13318461835501 / 5000) := by
  exact
    packedTile65536 2663618816 2663749888 14 6046 51610 31 _ _ (1085147 / 50000) (2170297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663749888 :
    ThetaLowerSegment 2663749888 2663880960 (13318461835501 / 5000) (16648885188179 / 6250) := by
  exact
    packedTile65536 2663749888 2663880960 14 5956 51611 31 _ _ (2170299 / 100000) (1085151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2663880960 :
    ThetaLowerSegment 2663880960 2664012032 (16648885188179 / 6250) (266395143593107 / 100000) := by
  exact
    packedTile65536 2663880960 2664012032 14 5981 51612 31 _ _ (2170303 / 100000) (1085153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664012032 :
    ThetaLowerSegment 2664012032 2664143104 (266395143593107 / 100000)
      (266408230550347 / 100000) := by
  exact
    packedTile65536 2664012032 2664143104 14 6030 51614 31 _ _ (542577 / 25000) (2170311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664143104 :
    ThetaLowerSegment 2664143104 2664274176 (266408230550347 / 100000)
      (266421191659583 / 100000) := by
  exact
    packedTile65536 2664143104 2664274176 14 5972 51615 31 _ _ (2170313 / 100000) (542579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664274176 :
    ThetaLowerSegment 2664274176 2664405248 (266421191659583 / 100000)
      (266434400214931 / 100000) := by
  exact
    packedTile65536 2664274176 2664405248 14 6086 51616 31 _ _ (1085159 / 50000) (2170321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664405248 :
    ThetaLowerSegment 2664405248 2664536320 (266434400214931 / 100000) (16652985452143 / 6250) := by
  exact
    packedTile65536 2664405248 2664536320 14 6159 51617 31 _ _ (2170323 / 100000) (1085163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664536320 :
    ThetaLowerSegment 2664536320 2664667392 (16652985452143 / 6250) (16653800410307 / 6250) := by
  exact
    packedTile65536 2664536320 2664667392 14 6008 51619 31 _ _ (271291 / 12500) (2170331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664667392 :
    ThetaLowerSegment 2664667392 2664798464 (16653800410307 / 6250) (266474021722549 / 100000) := by
  exact
    packedTile65536 2664667392 2664798464 14 6089 51620 31 _ _ (2170333 / 100000) (67823 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664798464 :
    ThetaLowerSegment 2664798464 2664929536 (266474021722549 / 100000)
      (266487271636039 / 100000) := by
  exact
    packedTile65536 2664798464 2664929536 14 6105 51621 31 _ _ (1085169 / 50000) (2170341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2664929536 :
    ThetaLowerSegment 2664929536 2665060608 (266487271636039 / 100000)
      (53300089991747 / 20000) := by
  exact
    packedTile65536 2664929536 2665060608 14 6072 51622 31 _ _ (2170343 / 100000) (1085173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665060608 :
    ThetaLowerSegment 2665060608 2665191680 (53300089991747 / 20000) (53302709601783 / 20000) := by
  exact
    packedTile65536 2665060608 2665191680 14 6035 51624 31 _ _ (542587 / 25000) (2170351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665191680 :
    ThetaLowerSegment 2665191680 2665322752 (53302709601783 / 20000) (16657914566697 / 6250) := by
  exact
    packedTile65536 2665191680 2665322752 14 6029 51625 31 _ _ (2170353 / 100000) (542589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665322752 :
    ThetaLowerSegment 2665322752 2665339136 (16657914566697 / 6250) (133264166228733 / 50000) := by
  exact
    packedTile65536 2665322752 2665339136 11 783 51626 31 _ _ (1085179 / 50000) (2170361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2665339136 :
    ThetaLowerSegment 2665339136 2665341184 (133264166228733 / 50000) (8329016425604 / 3125) := by
  exact
    packedTile65536 2665339136 2665341184 8 89 51626 31 _ _ (1085179 / 50000) (2170361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2633341184_2665341184 :
    ThetaLowerSegment 2633341184 2665341184 (65832433071487 / 25000) (8329016425604 / 3125) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2633341184 cell2633472256)
                  (ThetaLowerSegment.join cell2633603328 cell2633734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2633865472 cell2633996544)
                  (ThetaLowerSegment.join cell2634127616 cell2634258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2634389760 cell2634520832)
                  (ThetaLowerSegment.join cell2634651904 cell2634782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2634914048 cell2635045120)
                  (ThetaLowerSegment.join cell2635176192 cell2635307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2635438336 cell2635569408)
                  (ThetaLowerSegment.join cell2635700480 cell2635831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2635962624 cell2636093696)
                  (ThetaLowerSegment.join cell2636224768 cell2636355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2636486912 cell2636617984)
                  (ThetaLowerSegment.join cell2636749056 cell2636880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2637011200 cell2637142272)
                  (ThetaLowerSegment.join cell2637273344 cell2637404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2637535488 cell2637666560)
                  (ThetaLowerSegment.join cell2637797632 cell2637928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2638059776 cell2638190848)
                  (ThetaLowerSegment.join cell2638321920 cell2638452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2638584064 cell2638715136)
                  (ThetaLowerSegment.join cell2638846208 cell2638977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2639108352 cell2639239424)
                  (ThetaLowerSegment.join cell2639370496 cell2639501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2639632640 cell2639763712)
                  (ThetaLowerSegment.join cell2639894784 cell2640025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2640156928 cell2640288000)
                  (ThetaLowerSegment.join cell2640419072 cell2640550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2640681216 cell2640812288)
                  (ThetaLowerSegment.join cell2640943360 cell2641074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2641205504 cell2641336576)
                  (ThetaLowerSegment.join cell2641467648 cell2641598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2641729792 cell2641860864)
                  (ThetaLowerSegment.join cell2641991936 cell2642123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2642254080 cell2642385152)
                  (ThetaLowerSegment.join cell2642516224 cell2642647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2642778368 cell2642909440)
                  (ThetaLowerSegment.join cell2643040512 cell2643171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2643302656 cell2643433728)
                  (ThetaLowerSegment.join cell2643564800 cell2643695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2643826944 cell2643958016)
                  (ThetaLowerSegment.join cell2644089088 cell2644220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2644351232 cell2644482304)
                  (ThetaLowerSegment.join cell2644613376 cell2644744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2644875520 cell2645006592)
                  (ThetaLowerSegment.join cell2645137664 cell2645268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2645399808 cell2645530880)
                  (ThetaLowerSegment.join cell2645661952 cell2645793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2645924096 cell2646055168)
                  (ThetaLowerSegment.join cell2646186240 cell2646317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2646448384 cell2646579456)
                  (ThetaLowerSegment.join cell2646710528 cell2646841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2646972672 cell2647103744)
                  (ThetaLowerSegment.join cell2647234816 cell2647365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2647496960 cell2647628032)
                  (ThetaLowerSegment.join cell2647759104 cell2647890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2648021248 cell2648152320)
                  (ThetaLowerSegment.join cell2648283392 cell2648414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2648545536 cell2648676608)
                  (ThetaLowerSegment.join cell2648807680 cell2648938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2649069824 cell2649200896)
                  (ThetaLowerSegment.join cell2649331968 cell2649463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2649594112 cell2649725184)
                  (ThetaLowerSegment.join cell2649856256 cell2649987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2650118400 cell2650249472)
                  (ThetaLowerSegment.join cell2650380544 cell2650511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2650642688 cell2650773760)
                  (ThetaLowerSegment.join cell2650904832 cell2651035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2651166976 cell2651298048)
                  (ThetaLowerSegment.join cell2651429120 cell2651560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2651691264 cell2651822336)
                  (ThetaLowerSegment.join cell2651953408 cell2652084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2652215552 cell2652346624)
                  (ThetaLowerSegment.join cell2652477696 cell2652608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2652739840 cell2652870912)
                  (ThetaLowerSegment.join cell2653001984 cell2653133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2653264128 cell2653395200)
                  (ThetaLowerSegment.join cell2653526272 cell2653657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2653788416 cell2653919488)
                  (ThetaLowerSegment.join cell2654050560 cell2654181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2654312704 cell2654443776)
                  (ThetaLowerSegment.join cell2654574848 cell2654705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2654836992 cell2654968064)
                  (ThetaLowerSegment.join cell2655099136 cell2655230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2655361280 cell2655492352)
                  (ThetaLowerSegment.join cell2655623424 cell2655754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2655885568 cell2656016640)
                  (ThetaLowerSegment.join cell2656147712 cell2656278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2656409856 cell2656540928)
                  (ThetaLowerSegment.join cell2656672000 cell2656803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2656934144 cell2657065216)
                  (ThetaLowerSegment.join cell2657196288 cell2657327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2657458432 cell2657589504)
                  (ThetaLowerSegment.join cell2657720576 cell2657851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2657982720 cell2658113792)
                  (ThetaLowerSegment.join cell2658244864 cell2658375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2658507008 cell2658638080)
                  (ThetaLowerSegment.join cell2658769152 cell2658900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2659031296 cell2659162368)
                  (ThetaLowerSegment.join cell2659293440 cell2659424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2659555584 cell2659686656)
                  (ThetaLowerSegment.join cell2659817728 cell2659948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2660079872 cell2660210944)
                  (ThetaLowerSegment.join cell2660342016 cell2660473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2660604160 cell2660735232)
                  (ThetaLowerSegment.join cell2660866304 cell2660997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2661128448 cell2661259520)
                  (ThetaLowerSegment.join cell2661390592 cell2661521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2661652736 cell2661783808)
                  (ThetaLowerSegment.join cell2661914880 cell2662045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2662177024 cell2662308096)
                  (ThetaLowerSegment.join cell2662439168 cell2662570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2662701312 cell2662832384)
                  (ThetaLowerSegment.join cell2662963456 cell2663094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2663225600 cell2663356672)
                  (ThetaLowerSegment.join cell2663487744 cell2663618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2663749888 cell2663880960)
                  (ThetaLowerSegment.join cell2664012032 cell2664143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2664274176 cell2664405248)
                  (ThetaLowerSegment.join cell2664536320 cell2664667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2664798464 cell2664929536)
                (ThetaLowerSegment.join cell2665060608 cell2665191680))
              (ThetaLowerSegment.join cell2665322752 cell2665339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
