/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1193341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1161341184 :
    ThetaLowerSegment 1161341184 1161406720 (3629048640001 / 3125) (116136204476387 / 100000) := by
  exact
    packedTile65536 1161341184 1161406720 13 3185 34078 30 _ _ (2087283 / 100000) (1043643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161406720 :
    ThetaLowerSegment 1161406720 1161472256 (116136204476387 / 100000)
      (116142819092059 / 100000) := by
  exact
    packedTile65536 1161406720 1161472256 13 3169 34079 30 _ _ (260911 / 12500) (2087291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161472256 :
    ThetaLowerSegment 1161472256 1161537792 (116142819092059 / 100000)
      (23229897181819 / 20000) := by
  exact
    packedTile65536 1161472256 1161537792 13 3194 34080 30 _ _ (1043647 / 50000) (2087297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161537792 :
    ThetaLowerSegment 1161537792 1161603328 (23229897181819 / 20000) (23231216355419 / 20000) := by
  exact
    packedTile65536 1161537792 1161603328 13 3160 34081 30 _ _ (20873 / 1000) (2087303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161603328 :
    ThetaLowerSegment 1161603328 1161668864 (23231216355419 / 20000) (23232543881399 / 20000) := by
  exact
    packedTile65536 1161603328 1161668864 13 3180 34082 30 _ _ (417461 / 20000) (521827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161668864 :
    ThetaLowerSegment 1161668864 1161734400 (23232543881399 / 20000) (58084587729959 / 50000) := by
  exact
    packedTile65536 1161668864 1161734400 13 3093 34083 30 _ _ (2087311 / 100000) (1043657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161734400 :
    ThetaLowerSegment 1161734400 1161799936 (58084587729959 / 50000) (58087863772421 / 50000) := by
  exact
    packedTile65536 1161734400 1161799936 13 3139 34084 30 _ _ (521829 / 25000) (2087319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161799936 :
    ThetaLowerSegment 1161799936 1161865472 (58087863772421 / 50000) (58091180527079 / 50000) := by
  exact
    packedTile65536 1161799936 1161865472 13 3178 34085 30 _ _ (1043661 / 50000) (83493 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161865472 :
    ThetaLowerSegment 1161865472 1161931008 (58091180527079 / 50000) (58094433627767 / 50000) := by
  exact
    packedTile65536 1161865472 1161931008 13 3117 34086 30 _ _ (65229 / 3125) (2087331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161931008 :
    ThetaLowerSegment 1161931008 1161996544 (58094433627767 / 50000) (11619540478249 / 10000) := by
  exact
    packedTile65536 1161931008 1161996544 13 3132 34087 30 _ _ (2087333 / 100000) (260917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161996544 :
    ThetaLowerSegment 1161996544 1162062080 (11619540478249 / 10000) (3631310045464 / 3125) := by
  exact
    packedTile65536 1161996544 1162062080 13 3122 34088 30 _ _ (2087339 / 100000) (1043671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162062080 :
    ThetaLowerSegment 1162062080 1162127616 (3631310045464 / 3125) (116208411010453 / 100000) := by
  exact
    packedTile65536 1162062080 1162127616 13 3109 34089 30 _ _ (417469 / 20000) (521837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162127616 :
    ThetaLowerSegment 1162127616 1162193152 (116208411010453 / 100000)
      (116215155238303 / 100000) := by
  exact
    packedTile65536 1162127616 1162193152 13 3231 34089 30 _ _ (41747 / 2000) (2087353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162193152 :
    ThetaLowerSegment 1162193152 1162258688 (116215155238303 / 100000)
      (23244357353663 / 20000) := by
  exact
    packedTile65536 1162193152 1162258688 13 3177 34090 30 _ _ (521839 / 25000) (2087359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162258688 :
    ThetaLowerSegment 1162258688 1162324224 (23244357353663 / 20000)
      (116228387006959 / 100000) := by
  exact
    packedTile65536 1162258688 1162324224 13 3162 34091 30 _ _ (1043681 / 50000) (417473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162324224 :
    ThetaLowerSegment 1162324224 1162389760 (116228387006959 / 100000)
      (116234945514073 / 100000) := by
  exact
    packedTile65536 1162324224 1162389760 13 3142 34092 30 _ _ (2087367 / 100000) (208737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162389760 :
    ThetaLowerSegment 1162389760 1162455296 (116234945514073 / 100000)
      (116241504040039 / 100000) := by
  exact
    packedTile65536 1162389760 1162455296 13 3142 34093 30 _ _ (2087373 / 100000) (130461 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162455296 :
    ThetaLowerSegment 1162455296 1162520832 (116241504040039 / 100000)
      (116247995788729 / 100000) := by
  exact
    packedTile65536 1162455296 1162520832 13 3110 34094 30 _ _ (2087379 / 100000) (1043691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162520832 :
    ThetaLowerSegment 1162520832 1162586368 (116247995788729 / 100000)
      (116254583572633 / 100000) := by
  exact
    packedTile65536 1162520832 1162586368 13 3156 34095 30 _ _ (260923 / 12500) (2087387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162586368 :
    ThetaLowerSegment 1162586368 1162651904 (116254583572633 / 100000)
      (116261098316823 / 100000) := by
  exact
    packedTile65536 1162586368 1162651904 13 3121 34096 30 _ _ (208739 / 10000) (2087393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162651904 :
    ThetaLowerSegment 1162651904 1162717440 (116261098316823 / 100000)
      (58133794013939 / 50000) := by
  exact
    packedTile65536 1162651904 1162717440 13 3109 34097 30 _ _ (417479 / 20000) (1043699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162717440 :
    ThetaLowerSegment 1162717440 1162782976 (58133794013939 / 50000) (58137075408311 / 50000) := by
  exact
    packedTile65536 1162717440 1162782976 13 3144 34098 30 _ _ (2087401 / 100000) (521851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162782976 :
    ThetaLowerSegment 1162782976 1162848512 (58137075408311 / 50000) (29070200323831 / 25000) := by
  exact
    packedTile65536 1162782976 1162848512 13 3186 34099 30 _ _ (2087407 / 100000) (208741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162848512 :
    ThetaLowerSegment 1162848512 1162914048 (29070200323831 / 25000) (3633980454866 / 3125) := by
  exact
    packedTile65536 1162848512 1162914048 13 3149 34100 30 _ _ (521853 / 25000) (417483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162914048 :
    ThetaLowerSegment 1162914048 1162979584 (3633980454866 / 3125) (1453672965023 / 1250) := by
  exact
    packedTile65536 1162914048 1162979584 13 3096 34101 30 _ _ (1043709 / 50000) (2087421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1162979584 :
    ThetaLowerSegment 1162979584 1163045120 (1453672965023 / 1250) (7268767567483 / 6250) := by
  exact
    packedTile65536 1162979584 1163045120 13 3087 34102 30 _ _ (65232 / 3125) (2087427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163045120 :
    ThetaLowerSegment 1163045120 1163110656 (7268767567483 / 6250) (11630687318051 / 10000) := by
  exact
    packedTile65536 1163045120 1163110656 13 3158 34103 30 _ _ (2087429 / 100000) (260929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163110656 :
    ThetaLowerSegment 1163110656 1163176192 (11630687318051 / 10000) (23262675943081 / 20000) := by
  exact
    packedTile65536 1163110656 1163176192 13 3117 34104 30 _ _ (417487 / 20000) (1043719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163176192 :
    ThetaLowerSegment 1163176192 1163241728 (23262675943081 / 20000) (58159980708439 / 50000) := by
  exact
    packedTile65536 1163176192 1163241728 13 3153 34105 30 _ _ (2087441 / 100000) (521861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163241728 :
    ThetaLowerSegment 1163241728 1163307264 (58159980708439 / 50000) (5816325486749 / 5000) := by
  exact
    packedTile65536 1163241728 1163307264 13 3137 34106 30 _ _ (1043723 / 50000) (2087449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163307264 :
    ThetaLowerSegment 1163307264 1163372800 (5816325486749 / 5000) (14541627562221 / 12500) := by
  exact
    packedTile65536 1163307264 1163372800 13 3119 34107 30 _ _ (521863 / 25000) (417491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163372800 :
    ThetaLowerSegment 1163372800 1163438336 (14541627562221 / 12500) (23267911265127 / 20000) := by
  exact
    packedTile65536 1163372800 1163438336 13 3131 34108 30 _ _ (2087457 / 100000) (104373 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163438336 :
    ThetaLowerSegment 1163438336 1163503872 (23267911265127 / 20000) (58173056523459 / 50000) := by
  exact
    packedTile65536 1163438336 1163503872 13 3141 34109 30 _ _ (2087463 / 100000) (1043733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163503872 :
    ThetaLowerSegment 1163503872 1163569408 (58173056523459 / 50000) (727204147029 / 625) := by
  exact
    packedTile65536 1163503872 1163569408 13 3138 34110 30 _ _ (2087469 / 100000) (130467 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163569408 :
    ThetaLowerSegment 1163569408 1163634944 (727204147029 / 625) (58179601790341 / 50000) := by
  exact
    packedTile65536 1163569408 1163634944 13 3133 34111 30 _ _ (1043737 / 50000) (2087477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163634944 :
    ThetaLowerSegment 1163634944 1163700480 (58179601790341 / 50000) (58182914621101 / 50000) := by
  exact
    packedTile65536 1163634944 1163700480 13 3174 34112 30 _ _ (52187 / 2500) (2087483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163700480 :
    ThetaLowerSegment 1163700480 1163766016 (58182914621101 / 50000) (58186175274233 / 50000) := by
  exact
    packedTile65536 1163700480 1163766016 13 3124 34113 30 _ _ (1043743 / 50000) (2087489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163766016 :
    ThetaLowerSegment 1163766016 1163831552 (58186175274233 / 50000)
      (116379032607157 / 100000) := by
  exact
    packedTile65536 1163766016 1163831552 13 3201 34114 30 _ _ (2087491 / 100000) (1043747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163831552 :
    ThetaLowerSegment 1163831552 1163897088 (116379032607157 / 100000)
      (116385666672623 / 100000) := by
  exact
    packedTile65536 1163831552 1163897088 13 3178 34114 30 _ _ (2087497 / 100000) (167 / 8)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163897088 :
    ThetaLowerSegment 1163897088 1163962624 (116385666672623 / 100000)
      (23278465578301 / 20000) := by
  exact
    packedTile65536 1163897088 1163962624 13 3191 34115 30 _ _ (1043751 / 50000) (417501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163962624 :
    ThetaLowerSegment 1163962624 1164093696 (23278465578301 / 20000)
      (116405483366921 / 100000) := by
  exact
    packedTile65536 1163962624 1164093696 14 6302 34116 30 _ _ (521877 / 25000) (2087511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164093696 :
    ThetaLowerSegment 1164093696 1164224768 (116405483366921 / 100000)
      (29104650855959 / 25000) := by
  exact
    packedTile65536 1164093696 1164224768 14 6285 34118 30 _ _ (2087519 / 100000) (1043761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164224768 :
    ThetaLowerSegment 1164224768 1164355840 (29104650855959 / 25000)
      (116431623354683 / 100000) := by
  exact
    packedTile65536 1164224768 1164355840 14 6237 34120 30 _ _ (2087531 / 100000) (1043767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164355840 :
    ThetaLowerSegment 1164355840 1164421376 (116431623354683 / 100000)
      (116438126048013 / 100000) := by
  exact
    packedTile65536 1164355840 1164421376 13 3115 34122 30 _ _ (1043771 / 50000) (417509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164421376 :
    ThetaLowerSegment 1164421376 1164486912 (116438126048013 / 100000)
      (116444799938969 / 100000) := by
  exact
    packedTile65536 1164421376 1164486912 13 3197 34123 30 _ _ (521887 / 25000) (2087551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164486912 :
    ThetaLowerSegment 1164486912 1164617984 (116444799938969 / 100000)
      (116457951522869 / 100000) := by
  exact
    packedTile65536 1164486912 1164617984 14 6300 34124 30 _ _ (2087553 / 100000) (521889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164617984 :
    ThetaLowerSegment 1164617984 1164749056 (116457951522869 / 100000)
      (116471040549149 / 100000) := by
  exact
    packedTile65536 1164617984 1164749056 14 6270 34126 30 _ _ (521891 / 25000) (2087567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164749056 :
    ThetaLowerSegment 1164749056 1164880128 (116471040549149 / 100000)
      (116484133825821 / 100000) := by
  exact
    packedTile65536 1164749056 1164880128 14 6272 34128 30 _ _ (260947 / 12500) (2087579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1164880128 :
    ThetaLowerSegment 1164880128 1165011200 (116484133825821 / 100000)
      (116497210470789 / 100000) := by
  exact
    packedTile65536 1164880128 1165011200 14 6264 34130 30 _ _ (2087587 / 100000) (208759 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165011200 :
    ThetaLowerSegment 1165011200 1165142272 (116497210470789 / 100000)
      (116510362338189 / 100000) := by
  exact
    packedTile65536 1165011200 1165142272 14 6300 34132 30 _ _ (1043799 / 50000) (2087601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165142272 :
    ThetaLowerSegment 1165142272 1165273344 (116510362338189 / 100000) (2330471496311 / 2000) := by
  exact
    packedTile65536 1165142272 1165273344 14 6329 34134 30 _ _ (2087609 / 100000) (521903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165273344 :
    ThetaLowerSegment 1165273344 1165404416 (2330471496311 / 2000) (116537004481443 / 100000) := by
  exact
    packedTile65536 1165273344 1165404416 14 6433 34136 30 _ _ (2087621 / 100000) (260953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165404416 :
    ThetaLowerSegment 1165404416 1165535488 (116537004481443 / 100000)
      (23309971188807 / 20000) := by
  exact
    packedTile65536 1165404416 1165535488 14 6156 34138 30 _ _ (130477 / 6250) (417527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165535488 :
    ThetaLowerSegment 1165535488 1165666560 (23309971188807 / 20000) (23312584917843 / 20000) := by
  exact
    packedTile65536 1165535488 1165666560 14 6260 34139 30 _ _ (2087643 / 100000) (1043823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165666560 :
    ThetaLowerSegment 1165666560 1165797632 (23312584917843 / 20000) (23315236238423 / 20000) := by
  exact
    packedTile65536 1165666560 1165797632 14 6350 34141 30 _ _ (1043827 / 50000) (2087657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165797632 :
    ThetaLowerSegment 1165797632 1165928704 (23315236238423 / 20000)
      (116589199877291 / 100000) := by
  exact
    packedTile65536 1165797632 1165928704 14 6236 34143 30 _ _ (1043833 / 50000) (2087669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165928704 :
    ThetaLowerSegment 1165928704 1166059776 (116589199877291 / 100000) (3643819136501 / 3125) := by
  exact
    packedTile65536 1165928704 1166059776 14 6233 34145 30 _ _ (2087677 / 100000) (13048 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166059776 :
    ThetaLowerSegment 1166059776 1166190848 (3643819136501 / 3125) (14576922427031 / 12500) := by
  exact
    packedTile65536 1166059776 1166190848 14 6307 34147 30 _ _ (260961 / 12500) (2087691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166190848 :
    ThetaLowerSegment 1166190848 1166321920 (14576922427031 / 12500) (58314172013519 / 50000) := by
  exact
    packedTile65536 1166190848 1166321920 14 6210 34149 30 _ _ (2087699 / 100000) (1043851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166321920 :
    ThetaLowerSegment 1166321920 1166452992 (58314172013519 / 50000) (58320735776903 / 50000) := by
  exact
    packedTile65536 1166321920 1166452992 14 6288 34151 30 _ _ (2087711 / 100000) (1043857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166452992 :
    ThetaLowerSegment 1166452992 1166584064 (58320735776903 / 50000) (58327245294099 / 50000) := by
  exact
    packedTile65536 1166452992 1166584064 14 6236 34153 30 _ _ (1043861 / 50000) (83509 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166584064 :
    ThetaLowerSegment 1166584064 1166715136 (58327245294099 / 50000)
      (116667762306879 / 100000) := by
  exact
    packedTile65536 1166584064 1166715136 14 6357 34155 30 _ _ (2087733 / 100000) (260967 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166715136 :
    ThetaLowerSegment 1166715136 1166846208 (116667762306879 / 100000)
      (116680664564799 / 100000) := by
  exact
    packedTile65536 1166715136 1166846208 14 6180 34157 30 _ _ (65242 / 3125) (2087747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166846208 :
    ThetaLowerSegment 1166846208 1166977280 (116680664564799 / 100000)
      (116693953131739 / 100000) := by
  exact
    packedTile65536 1166846208 1166977280 14 6365 34159 30 _ _ (521939 / 25000) (2087759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1166977280 :
    ThetaLowerSegment 1166977280 1167108352 (116693953131739 / 100000)
      (116707151994713 / 100000) := by
  exact
    packedTile65536 1166977280 1167108352 14 6322 34161 30 _ _ (2087767 / 100000) (208777 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167108352 :
    ThetaLowerSegment 1167108352 1167239424 (116707151994713 / 100000) (4668804182777 / 4000) := by
  exact
    packedTile65536 1167108352 1167239424 14 6204 34162 30 _ _ (1043889 / 50000) (2087781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167239424 :
    ThetaLowerSegment 1167239424 1167370496 (4668804182777 / 4000) (116733224235501 / 100000) := by
  exact
    packedTile65536 1167239424 1167370496 14 6284 34164 30 _ _ (2087789 / 100000) (130487 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167370496 :
    ThetaLowerSegment 1167370496 1167501568 (116733224235501 / 100000)
      (116746220790501 / 100000) := by
  exact
    packedTile65536 1167370496 1167501568 14 6225 34166 30 _ _ (10439 / 500) (2087803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167501568 :
    ThetaLowerSegment 1167501568 1167632640 (116746220790501 / 100000)
      (116759442903897 / 100000) := by
  exact
    packedTile65536 1167501568 1167632640 14 6333 34168 30 _ _ (521953 / 25000) (417563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167632640 :
    ThetaLowerSegment 1167632640 1167763712 (116759442903897 / 100000)
      (116772433338603 / 100000) := by
  exact
    packedTile65536 1167632640 1167763712 14 6222 34170 30 _ _ (2087823 / 100000) (1043913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167763712 :
    ThetaLowerSegment 1167763712 1167894784 (116772433338603 / 100000)
      (23357124854763 / 20000) := by
  exact
    packedTile65536 1167763712 1167894784 14 6318 34172 30 _ _ (1043917 / 50000) (2087837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167894784 :
    ThetaLowerSegment 1167894784 1168025856 (23357124854763 / 20000) (23359728815047 / 20000) := by
  exact
    packedTile65536 1167894784 1168025856 14 6236 34174 30 _ _ (417569 / 20000) (260981 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168025856 :
    ThetaLowerSegment 1168025856 1168156928 (23359728815047 / 20000) (584058413711 / 500) := by
  exact
    packedTile65536 1168025856 1168156928 14 6245 34176 30 _ _ (2087857 / 100000) (104393 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168156928 :
    ThetaLowerSegment 1168156928 1168222464 (584058413711 / 500) (7301139654499 / 6250) := by
  exact
    packedTile65536 1168156928 1168222464 13 3138 34178 30 _ _ (521967 / 25000) (2087871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168222464 :
    ThetaLowerSegment 1168222464 1168288000 (7301139654499 / 6250) (3650773394867 / 3125) := by
  exact
    packedTile65536 1168222464 1168288000 13 3120 34179 30 _ _ (2087873 / 100000) (521969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168288000 :
    ThetaLowerSegment 1168288000 1168353536 (3650773394867 / 3125) (116831335893989 / 100000) := by
  exact
    packedTile65536 1168288000 1168353536 13 3155 34180 30 _ _ (2087879 / 100000) (1043941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168353536 :
    ThetaLowerSegment 1168353536 1168419072 (116831335893989 / 100000)
      (116837950313669 / 100000) := by
  exact
    packedTile65536 1168353536 1168419072 13 3168 34181 30 _ _ (417577 / 20000) (130493 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168419072 :
    ThetaLowerSegment 1168419072 1168550144 (116837950313669 / 100000)
      (116850989186719 / 100000) := by
  exact
    packedTile65536 1168419072 1168550144 14 6245 34182 30 _ _ (208789 / 10000) (2087893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168550144 :
    ThetaLowerSegment 1168550144 1168615680 (116850989186719 / 100000) (1460719341047 / 1250) := by
  exact
    packedTile65536 1168550144 1168615680 13 3141 34184 30 _ _ (2087901 / 100000) (65247 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168615680 :
    ThetaLowerSegment 1168615680 1168681216 (1460719341047 / 1250) (116864076168949 / 100000) := by
  exact
    packedTile65536 1168615680 1168681216 13 3127 34185 30 _ _ (2087907 / 100000) (208791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168681216 :
    ThetaLowerSegment 1168681216 1168746752 (116864076168949 / 100000)
      (116870653094899 / 100000) := by
  exact
    packedTile65536 1168681216 1168746752 13 3150 34185 30 _ _ (2087913 / 100000) (521979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168746752 :
    ThetaLowerSegment 1168746752 1168812288 (116870653094899 / 100000)
      (116877169486977 / 100000) := by
  exact
    packedTile65536 1168746752 1168812288 13 3121 34186 30 _ _ (1043959 / 50000) (2087921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168812288 :
    ThetaLowerSegment 1168812288 1168877824 (116877169486977 / 100000)
      (116883811173221 / 100000) := by
  exact
    packedTile65536 1168812288 1168877824 13 3181 34187 30 _ _ (521981 / 25000) (2087927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1168877824 :
    ThetaLowerSegment 1168877824 1169008896 (116883811173221 / 100000)
      (116896818977121 / 100000) := by
  exact
    packedTile65536 1168877824 1169008896 14 6230 34188 30 _ _ (208793 / 10000) (2087933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169008896 :
    ThetaLowerSegment 1169008896 1169074432 (116896818977121 / 100000)
      (11690335214451 / 10000) := by
  exact
    packedTile65536 1169008896 1169074432 13 3129 34190 30 _ _ (2087941 / 100000) (260993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169074432 :
    ThetaLowerSegment 1169074432 1169139968 (11690335214451 / 10000) (58454989642557 / 50000) := by
  exact
    packedTile65536 1169074432 1169139968 13 3174 34191 30 _ _ (1043973 / 50000) (2087949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169139968 :
    ThetaLowerSegment 1169139968 1169205504 (58454989642557 / 50000) (58458324101901 / 50000) := by
  exact
    packedTile65536 1169139968 1169205504 13 3194 34192 30 _ _ (130497 / 6250) (417591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169205504 :
    ThetaLowerSegment 1169205504 1169336576 (58458324101901 / 50000) (58464817651281 / 50000) := by
  exact
    packedTile65536 1169205504 1169336576 14 6220 34193 30 _ _ (1043979 / 50000) (2087961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169336576 :
    ThetaLowerSegment 1169336576 1169402112 (58464817651281 / 50000)
      (116936181085377 / 100000) := by
  exact
    packedTile65536 1169336576 1169402112 13 3135 34195 30 _ _ (2087969 / 100000) (521993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169402112 :
    ThetaLowerSegment 1169402112 1169467648 (116936181085377 / 100000)
      (116942643364907 / 100000) := by
  exact
    packedTile65536 1169402112 1169467648 13 3095 34196 30 _ _ (1043987 / 50000) (2087977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169467648 :
    ThetaLowerSegment 1169467648 1169533184 (116942643364907 / 100000)
      (116949170390387 / 100000) := by
  exact
    packedTile65536 1169467648 1169533184 13 3126 34197 30 _ _ (104399 / 5000) (2087983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169533184 :
    ThetaLowerSegment 1169533184 1169598720 (116949170390387 / 100000)
      (116955678642749 / 100000) := by
  exact
    packedTile65536 1169533184 1169598720 13 3117 34198 30 _ _ (1043993 / 50000) (2087989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169598720 :
    ThetaLowerSegment 1169598720 1169664256 (116955678642749 / 100000)
      (116962259990381 / 100000) := by
  exact
    packedTile65536 1169598720 1169664256 13 3152 34199 30 _ _ (2087991 / 100000) (1043997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169664256 :
    ThetaLowerSegment 1169664256 1169729792 (116962259990381 / 100000) (2339377871137 / 2000) := by
  exact
    packedTile65536 1169664256 1169729792 13 3177 34200 30 _ _ (2087997 / 100000) (522 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169729792 :
    ThetaLowerSegment 1169729792 1169795328 (2339377871137 / 2000) (58487814725651 / 50000) := by
  exact
    packedTile65536 1169729792 1169795328 13 3226 34201 30 _ _ (1044001 / 50000) (417601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169795328 :
    ThetaLowerSegment 1169795328 1169926400 (58487814725651 / 50000) (11698875466959 / 10000) := by
  exact
    packedTile65536 1169795328 1169926400 14 6286 34202 30 _ _ (261001 / 12500) (2088011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169926400 :
    ThetaLowerSegment 1169926400 1170057472 (11698875466959 / 10000)
      (117001882045043 / 100000) := by
  exact
    packedTile65536 1169926400 1170057472 14 6287 34204 30 _ _ (2088019 / 100000) (1044011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170057472 :
    ThetaLowerSegment 1170057472 1170188544 (117001882045043 / 100000)
      (117015044986163 / 100000) := by
  exact
    packedTile65536 1170057472 1170188544 14 6304 34206 30 _ _ (208803 / 10000) (2088033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170188544 :
    ThetaLowerSegment 1170188544 1170319616 (117015044986163 / 100000) (4681120552601 / 4000) := by
  exact
    packedTile65536 1170188544 1170319616 14 6211 34208 30 _ _ (1044021 / 50000) (417609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170319616 :
    ThetaLowerSegment 1170319616 1170450688 (4681120552601 / 4000) (58520572790171 / 50000) := by
  exact
    packedTile65536 1170319616 1170450688 14 6289 34209 30 _ _ (2088053 / 100000) (261007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170450688 :
    ThetaLowerSegment 1170450688 1170581760 (58520572790171 / 50000) (58527119914843 / 50000) := by
  exact
    packedTile65536 1170450688 1170581760 14 6271 34211 30 _ _ (65252 / 3125) (2088067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170581760 :
    ThetaLowerSegment 1170581760 1170712832 (58527119914843 / 50000) (58533688998793 / 50000) := by
  exact
    packedTile65536 1170581760 1170712832 14 6292 34213 30 _ _ (83523 / 4000) (1044039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170712832 :
    ThetaLowerSegment 1170712832 1170843904 (58533688998793 / 50000) (29270145241341 / 25000) := by
  exact
    packedTile65536 1170712832 1170843904 14 6323 34215 30 _ _ (1044043 / 50000) (2088089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170843904 :
    ThetaLowerSegment 1170843904 1170974976 (29270145241341 / 25000) (58546806392491 / 50000) := by
  exact
    packedTile65536 1170843904 1170974976 14 6241 34217 30 _ _ (1044049 / 50000) (2088101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1170974976 :
    ThetaLowerSegment 1170974976 1171106048 (58546806392491 / 50000) (2342133352849 / 2000) := by
  exact
    packedTile65536 1170974976 1171106048 14 6252 34219 30 _ _ (2088109 / 100000) (130507 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171106048 :
    ThetaLowerSegment 1171106048 1171237120 (2342133352849 / 2000) (11711976224297 / 10000) := by
  exact
    packedTile65536 1171106048 1171237120 14 6271 34221 30 _ _ (52203 / 2500) (2088123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171237120 :
    ThetaLowerSegment 1171237120 1171368192 (11711976224297 / 10000) (29283222058609 / 25000) := by
  exact
    packedTile65536 1171237120 1171368192 14 6286 34223 30 _ _ (2088131 / 100000) (1044067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171368192 :
    ThetaLowerSegment 1171368192 1171499264 (29283222058609 / 25000) (58573035337441 / 50000) := by
  exact
    packedTile65536 1171368192 1171499264 14 6313 34225 30 _ _ (1044071 / 50000) (417629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171499264 :
    ThetaLowerSegment 1171499264 1171630336 (58573035337441 / 50000) (5857958900877 / 5000) := by
  exact
    packedTile65536 1171499264 1171630336 14 6277 34227 30 _ _ (1044077 / 50000) (2088157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171630336 :
    ThetaLowerSegment 1171630336 1171761408 (5857958900877 / 5000) (23434472955903 / 20000) := by
  exact
    packedTile65536 1171630336 1171761408 14 6315 34229 30 _ _ (417633 / 20000) (261021 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171761408 :
    ThetaLowerSegment 1171761408 1171892480 (23434472955903 / 20000)
      (117185534905547 / 100000) := by
  exact
    packedTile65536 1171761408 1171892480 14 6307 34231 30 _ _ (130511 / 6250) (2088179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171892480 :
    ThetaLowerSegment 1171892480 1172023552 (117185534905547 / 100000)
      (117198723894639 / 100000) := by
  exact
    packedTile65536 1171892480 1172023552 14 6316 34232 30 _ _ (2088187 / 100000) (208819 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172023552 :
    ThetaLowerSegment 1172023552 1172154624 (117198723894639 / 100000)
      (117211858660059 / 100000) := by
  exact
    packedTile65536 1172023552 1172154624 14 6290 34234 30 _ _ (1044099 / 50000) (2088201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172154624 :
    ThetaLowerSegment 1172154624 1172285696 (117211858660059 / 100000)
      (14653127058121 / 12500) := by
  exact
    packedTile65536 1172154624 1172285696 14 6301 34236 30 _ _ (2088209 / 100000) (522053 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172285696 :
    ThetaLowerSegment 1172285696 1172416768 (14653127058121 / 12500) (58619117451949 / 50000) := by
  exact
    packedTile65536 1172285696 1172416768 14 6330 34238 30 _ _ (2088221 / 100000) (65257 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172416768 :
    ThetaLowerSegment 1172416768 1172547840 (58619117451949 / 50000) (58625681809241 / 50000) := by
  exact
    packedTile65536 1172416768 1172547840 14 6287 34240 30 _ _ (261029 / 12500) (417647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172547840 :
    ThetaLowerSegment 1172547840 1172678912 (58625681809241 / 50000) (5863224515699 / 5000) := by
  exact
    packedTile65536 1172547840 1172678912 14 6286 34242 30 _ _ (2088243 / 100000) (1044123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172678912 :
    ThetaLowerSegment 1172678912 1172809984 (5863224515699 / 5000) (58638707258993 / 50000) := by
  exact
    packedTile65536 1172678912 1172809984 14 6189 34244 30 _ _ (1044127 / 50000) (2088257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172809984 :
    ThetaLowerSegment 1172809984 1172941056 (58638707258993 / 50000) (14661315580707 / 12500) := by
  exact
    packedTile65536 1172809984 1172941056 14 6278 34246 30 _ _ (417653 / 20000) (522067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1172941056 :
    ThetaLowerSegment 1172941056 1173072128 (14661315580707 / 12500) (58651792365007 / 50000) := by
  exact
    packedTile65536 1172941056 1173072128 14 6254 34248 30 _ _ (2088277 / 100000) (52207 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173072128 :
    ThetaLowerSegment 1173072128 1173203200 (58651792365007 / 50000) (11731674512099 / 10000) := by
  exact
    packedTile65536 1173072128 1173203200 14 6302 34250 30 _ _ (65259 / 3125) (2088291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173203200 :
    ThetaLowerSegment 1173203200 1173334272 (11731674512099 / 10000)
      (117329732252471 / 100000) := by
  exact
    packedTile65536 1173203200 1173334272 14 6219 34252 30 _ _ (2088299 / 100000) (1044151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173334272 :
    ThetaLowerSegment 1173334272 1173465344 (117329732252471 / 100000)
      (117342932459981 / 100000) := by
  exact
    packedTile65536 1173334272 1173465344 14 6321 34253 30 _ _ (208831 / 10000) (2088313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173465344 :
    ThetaLowerSegment 1173465344 1173596416 (117342932459981 / 100000)
      (11735598237791 / 10000) := by
  exact
    packedTile65536 1173465344 1173596416 14 6249 34255 30 _ _ (2088321 / 100000) (522081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173596416 :
    ThetaLowerSegment 1173596416 1173727488 (11735598237791 / 10000) (58684587185577 / 50000) := by
  exact
    packedTile65536 1173596416 1173727488 14 6317 34257 30 _ _ (522083 / 25000) (417667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173727488 :
    ThetaLowerSegment 1173727488 1173858560 (58684587185577 / 50000) (11738231840829 / 10000) := by
  exact
    packedTile65536 1173727488 1173858560 14 6294 34259 30 _ _ (261043 / 12500) (2088347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173858560 :
    ThetaLowerSegment 1173858560 1173989632 (11738231840829 / 10000) (11739539151059 / 10000) := by
  exact
    packedTile65536 1173858560 1173989632 14 6260 34261 30 _ _ (417671 / 20000) (1044179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173989632 :
    ThetaLowerSegment 1173989632 1174120704 (11739539151059 / 10000) (2348173470367 / 2000) := by
  exact
    packedTile65536 1173989632 1174120704 14 6360 34263 30 _ _ (1044183 / 50000) (2088369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174120704 :
    ThetaLowerSegment 1174120704 1174251776 (2348173470367 / 2000) (117421753023501 / 100000) := by
  exact
    packedTile65536 1174120704 1174251776 14 6263 34265 30 _ _ (2088377 / 100000) (104419 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174251776 :
    ThetaLowerSegment 1174251776 1174382848 (117421753023501 / 100000)
      (117434684321997 / 100000) := by
  exact
    packedTile65536 1174251776 1174382848 14 6192 34267 30 _ _ (522097 / 25000) (2088391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174382848 :
    ThetaLowerSegment 1174382848 1174513920 (117434684321997 / 100000)
      (117447791114121 / 100000) := by
  exact
    packedTile65536 1174382848 1174513920 14 6276 34269 30 _ _ (2088399 / 100000) (1044201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174513920 :
    ThetaLowerSegment 1174513920 1174644992 (117447791114121 / 100000)
      (117460948103421 / 100000) := by
  exact
    packedTile65536 1174513920 1174644992 14 6300 34271 30 _ _ (2088411 / 100000) (1044207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174644992 :
    ThetaLowerSegment 1174644992 1174776064 (117460948103421 / 100000)
      (117473996564077 / 100000) := by
  exact
    packedTile65536 1174644992 1174776064 14 6248 34273 30 _ _ (1044211 / 50000) (83537 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174776064 :
    ThetaLowerSegment 1174776064 1174907136 (117473996564077 / 100000)
      (117487295705421 / 100000) := by
  exact
    packedTile65536 1174776064 1174907136 14 6368 34275 30 _ _ (2088433 / 100000) (522109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1174907136 :
    ThetaLowerSegment 1174907136 1175038208 (117487295705421 / 100000)
      (117500415310629 / 100000) := by
  exact
    packedTile65536 1174907136 1175038208 14 6282 34276 30 _ _ (522111 / 25000) (2088447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175038208 :
    ThetaLowerSegment 1175038208 1175169280 (117500415310629 / 100000)
      (58756743475237 / 50000) := by
  exact
    packedTile65536 1175038208 1175169280 14 6259 34278 30 _ _ (417691 / 20000) (1044229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175169280 :
    ThetaLowerSegment 1175169280 1175300352 (58756743475237 / 50000) (3672703913866 / 3125) := by
  exact
    packedTile65536 1175169280 1175300352 14 6243 34280 30 _ _ (1044233 / 50000) (2088469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175300352 :
    ThetaLowerSegment 1175300352 1175431424 (3672703913866 / 3125) (117539559428669 / 100000) := by
  exact
    packedTile65536 1175300352 1175431424 14 6241 34282 30 _ _ (2088477 / 100000) (13053 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175431424 :
    ThetaLowerSegment 1175431424 1175562496 (117539559428669 / 100000)
      (29388134846951 / 25000) := by
  exact
    packedTile65536 1175431424 1175562496 14 6215 34284 30 _ _ (2088489 / 100000) (522123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175562496 :
    ThetaLowerSegment 1175562496 1175693568 (29388134846951 / 25000) (3673928616697 / 3125) := by
  exact
    packedTile65536 1175562496 1175693568 14 6309 34286 30 _ _ (4177 / 200) (2088503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175693568 :
    ThetaLowerSegment 1175693568 1175824640 (3673928616697 / 3125) (58789355224873 / 50000) := by
  exact
    packedTile65536 1175693568 1175824640 14 6222 34288 30 _ _ (2088511 / 100000) (1044257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175824640 :
    ThetaLowerSegment 1175824640 1175955712 (58789355224873 / 50000) (58795927803607 / 50000) := by
  exact
    packedTile65536 1175824640 1175955712 14 6294 34290 30 _ _ (1044261 / 50000) (83541 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175955712 :
    ThetaLowerSegment 1175955712 1176086784 (58795927803607 / 50000) (58802523390821 / 50000) := by
  exact
    packedTile65536 1175955712 1176086784 14 6316 34292 30 _ _ (2088533 / 100000) (261067 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176086784 :
    ThetaLowerSegment 1176086784 1176217856 (58802523390821 / 50000) (58809063666357 / 50000) := by
  exact
    packedTile65536 1176086784 1176217856 14 6263 34294 30 _ _ (65267 / 3125) (2088547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176217856 :
    ThetaLowerSegment 1176217856 1176348928 (58809063666357 / 50000) (14703943548393 / 12500) := by
  exact
    packedTile65536 1176217856 1176348928 14 6426 34296 30 _ _ (417711 / 20000) (1044279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176348928 :
    ThetaLowerSegment 1176348928 1176480000 (14703943548393 / 12500)
      (117644578956657 / 100000) := by
  exact
    packedTile65536 1176348928 1176480000 14 6239 34297 30 _ _ (2088567 / 100000) (208857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176480000 :
    ThetaLowerSegment 1176480000 1176611072 (117644578956657 / 100000)
      (117657678517873 / 100000) := by
  exact
    packedTile65536 1176480000 1176611072 14 6272 34299 30 _ _ (1044289 / 50000) (2088581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176611072 :
    ThetaLowerSegment 1176611072 1176742144 (117657678517873 / 100000)
      (58835394295513 / 50000) := by
  exact
    packedTile65536 1176611072 1176742144 14 6277 34301 30 _ _ (2088589 / 100000) (130537 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176742144 :
    ThetaLowerSegment 1176742144 1176873216 (58835394295513 / 50000) (58841986961413 / 50000) := by
  exact
    packedTile65536 1176742144 1176873216 14 6313 34303 30 _ _ (10443 / 500) (2088603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1176873216 :
    ThetaLowerSegment 1176873216 1177004288 (58841986961413 / 50000) (23539421839481 / 20000) := by
  exact
    packedTile65536 1176873216 1177004288 14 6289 34305 30 _ _ (2088611 / 100000) (1044307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177004288 :
    ThetaLowerSegment 1177004288 1177135360 (23539421839481 / 20000)
      (117710242452541 / 100000) := by
  exact
    packedTile65536 1177004288 1177135360 14 6288 34307 30 _ _ (1044311 / 50000) (16709 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177135360 :
    ThetaLowerSegment 1177135360 1177266432 (117710242452541 / 100000) (3678856210994 / 3125) := by
  exact
    packedTile65536 1177135360 1177266432 14 6299 34309 30 _ _ (2088633 / 100000) (522159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177266432 :
    ThetaLowerSegment 1177266432 1177397504 (3678856210994 / 3125) (58868276519009 / 50000) := by
  exact
    packedTile65536 1177266432 1177397504 14 6298 34311 30 _ _ (417729 / 20000) (261081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177397504 :
    ThetaLowerSegment 1177397504 1177528576 (58868276519009 / 50000) (58874791037073 / 50000) := by
  exact
    packedTile65536 1177397504 1177528576 14 6238 34313 30 _ _ (130541 / 6250) (2088659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177528576 :
    ThetaLowerSegment 1177528576 1177659648 (58874791037073 / 50000) (3680081338257 / 3125) := by
  exact
    packedTile65536 1177528576 1177659648 14 6234 34315 30 _ _ (2088667 / 100000) (208867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177659648 :
    ThetaLowerSegment 1177659648 1177790720 (3680081338257 / 3125) (29443912176753 / 25000) := by
  exact
    packedTile65536 1177659648 1177790720 14 6246 34317 30 _ _ (1044339 / 50000) (2088681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177790720 :
    ThetaLowerSegment 1177790720 1177921792 (29443912176753 / 25000) (29447162176837 / 25000) := by
  exact
    packedTile65536 1177790720 1177921792 14 6224 34318 30 _ _ (2088689 / 100000) (522173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177921792 :
    ThetaLowerSegment 1177921792 1178052864 (29447162176837 / 25000) (29450435169737 / 25000) := by
  exact
    packedTile65536 1177921792 1178052864 14 6268 34320 30 _ _ (20887 / 1000) (2088703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178052864 :
    ThetaLowerSegment 1178052864 1178183936 (29450435169737 / 25000) (58907330722597 / 50000) := by
  exact
    packedTile65536 1178052864 1178183936 14 6186 34322 30 _ _ (2088711 / 100000) (1044357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178183936 :
    ThetaLowerSegment 1178183936 1178315008 (58907330722597 / 50000) (14728456140601 / 12500) := by
  exact
    packedTile65536 1178183936 1178315008 14 6218 34324 30 _ _ (2088723 / 100000) (1044363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178315008 :
    ThetaLowerSegment 1178315008 1178446080 (14728456140601 / 12500) (7365044243111 / 6250) := by
  exact
    packedTile65536 1178315008 1178446080 14 6252 34326 30 _ _ (1044367 / 50000) (2088737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178446080 :
    ThetaLowerSegment 1178446080 1178577152 (7365044243111 / 6250) (29463475100799 / 25000) := by
  exact
    packedTile65536 1178446080 1178577152 14 6316 34328 30 _ _ (417749 / 20000) (522187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178577152 :
    ThetaLowerSegment 1178577152 1178708224 (29463475100799 / 25000) (29466736693293 / 25000) := by
  exact
    packedTile65536 1178577152 1178708224 14 6246 34330 30 _ _ (522189 / 25000) (2088759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178708224 :
    ThetaLowerSegment 1178708224 1178839296 (29466736693293 / 25000) (23575999895631 / 20000) := by
  exact
    packedTile65536 1178708224 1178839296 14 6249 34332 30 _ _ (2088767 / 100000) (208877 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178839296 :
    ThetaLowerSegment 1178839296 1178970368 (23575999895631 / 20000)
      (117893152513221 / 100000) := by
  exact
    packedTile65536 1178839296 1178970368 14 6297 34334 30 _ _ (1044389 / 50000) (2088781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1178970368 :
    ThetaLowerSegment 1178970368 1179101440 (117893152513221 / 100000)
      (29476598336673 / 25000) := by
  exact
    packedTile65536 1178970368 1179101440 14 6339 34336 30 _ _ (2088789 / 100000) (261099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179101440 :
    ThetaLowerSegment 1179101440 1179232512 (29476598336673 / 25000) (29479847465073 / 25000) := by
  exact
    packedTile65536 1179101440 1179232512 14 6222 34338 30 _ _ (2611 / 125) (2088803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179232512 :
    ThetaLowerSegment 1179232512 1179363584 (29479847465073 / 25000) (29483164496941 / 25000) := by
  exact
    packedTile65536 1179232512 1179363584 14 6352 34339 30 _ _ (2088811 / 100000) (1044407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179363584 :
    ThetaLowerSegment 1179363584 1179494656 (29483164496941 / 25000)
      (117945944990867 / 100000) := by
  exact
    packedTile65536 1179363584 1179494656 14 6361 34341 30 _ _ (2088823 / 100000) (1044413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179494656 :
    ThetaLowerSegment 1179494656 1179625728 (117945944990867 / 100000)
      (117959031535877 / 100000) := by
  exact
    packedTile65536 1179494656 1179625728 14 6265 34343 30 _ _ (1044417 / 50000) (2088837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179625728 :
    ThetaLowerSegment 1179625728 1179756800 (117959031535877 / 100000)
      (117972011618707 / 100000) := by
  exact
    packedTile65536 1179625728 1179756800 14 6214 34345 30 _ _ (417769 / 20000) (130553 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179756800 :
    ThetaLowerSegment 1179756800 1179887872 (117972011618707 / 100000)
      (117985225721763 / 100000) := by
  exact
    packedTile65536 1179756800 1179887872 14 6326 34347 30 _ _ (261107 / 12500) (2088859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179887872 :
    ThetaLowerSegment 1179887872 1180018944 (117985225721763 / 100000)
      (117998260251843 / 100000) := by
  exact
    packedTile65536 1179887872 1180018944 14 6240 34349 30 _ _ (2088867 / 100000) (208887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180018944 :
    ThetaLowerSegment 1180018944 1180150016 (117998260251843 / 100000) (944090007873 / 800) := by
  exact
    packedTile65536 1180018944 1180150016 14 6219 34351 30 _ _ (1044439 / 50000) (2088881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180150016 :
    ThetaLowerSegment 1180150016 1180281088 (944090007873 / 800) (118024365029267 / 100000) := by
  exact
    packedTile65536 1180150016 1180281088 14 6278 34353 30 _ _ (2088889 / 100000) (522223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180281088 :
    ThetaLowerSegment 1180281088 1180412160 (118024365029267 / 100000)
      (118037493765767 / 100000) := by
  exact
    packedTile65536 1180281088 1180412160 14 6285 34355 30 _ _ (20889 / 1000) (2088903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180412160 :
    ThetaLowerSegment 1180412160 1180543232 (118037493765767 / 100000)
      (118050637193779 / 100000) := by
  exact
    packedTile65536 1180412160 1180543232 14 6292 34357 30 _ _ (2088911 / 100000) (1044457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180543232 :
    ThetaLowerSegment 1180543232 1180674304 (118050637193779 / 100000)
      (118063734740989 / 100000) := by
  exact
    packedTile65536 1180543232 1180674304 14 6270 34359 30 _ _ (2088923 / 100000) (1044463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180674304 :
    ThetaLowerSegment 1180674304 1180805376 (118063734740989 / 100000)
      (23615366053647 / 20000) := by
  exact
    packedTile65536 1180674304 1180805376 14 6269 34360 30 _ _ (1044467 / 50000) (2088937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180805376 :
    ThetaLowerSegment 1180805376 1180936448 (23615366053647 / 20000) (5904485012919 / 5000) := by
  exact
    packedTile65536 1180805376 1180936448 14 6161 34362 30 _ _ (417789 / 20000) (522237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1180936448 :
    ThetaLowerSegment 1180936448 1181067520 (5904485012919 / 5000) (3690714331007 / 3125) := by
  exact
    packedTile65536 1180936448 1181067520 14 6299 34364 30 _ _ (522239 / 25000) (2088959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181067520 :
    ThetaLowerSegment 1181067520 1181198592 (3690714331007 / 3125) (118115799742789 / 100000) := by
  exact
    packedTile65536 1181067520 1181198592 14 6195 34366 30 _ _ (2088967 / 100000) (208897 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181198592 :
    ThetaLowerSegment 1181198592 1181329664 (118115799742789 / 100000)
      (118128868389157 / 100000) := by
  exact
    packedTile65536 1181198592 1181329664 14 6256 34368 30 _ _ (1044489 / 50000) (2088981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181329664 :
    ThetaLowerSegment 1181329664 1181395200 (118128868389157 / 100000)
      (59067748375627 / 50000) := by
  exact
    packedTile65536 1181329664 1181395200 13 3173 34370 30 _ _ (2088989 / 100000) (65281 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181395200 :
    ThetaLowerSegment 1181395200 1181526272 (59067748375627 / 50000) (14768568076753 / 12500) := by
  exact
    packedTile65536 1181395200 1181526272 14 6246 34371 30 _ _ (417799 / 20000) (1044499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181526272 :
    ThetaLowerSegment 1181526272 1181591808 (14768568076753 / 12500) (59077580248013 / 50000) := by
  exact
    packedTile65536 1181526272 1181591808 13 3167 34373 30 _ _ (1044503 / 50000) (2089009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181591808 :
    ThetaLowerSegment 1181591808 1181722880 (59077580248013 / 50000) (59084106318377 / 50000) := by
  exact
    packedTile65536 1181591808 1181722880 14 6248 34374 30 _ _ (2089011 / 100000) (1044507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181722880 :
    ThetaLowerSegment 1181722880 1181853952 (59084106318377 / 50000) (738632709443 / 625) := by
  exact
    packedTile65536 1181722880 1181853952 14 6233 34376 30 _ _ (1044511 / 50000) (83561 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181853952 :
    ThetaLowerSegment 1181853952 1181919488 (738632709443 / 625) (3693369317064 / 3125) := by
  exact
    packedTile65536 1181853952 1181919488 13 3152 34378 30 _ _ (1044517 / 50000) (2089037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181919488 :
    ThetaLowerSegment 1181919488 1181985024 (3693369317064 / 3125) (118194304612143 / 100000) := by
  exact
    packedTile65536 1181919488 1181985024 13 3105 34379 30 _ _ (2089039 / 100000) (1044521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181985024 :
    ThetaLowerSegment 1181985024 1182050560 (118194304612143 / 100000)
      (59100405993659 / 50000) := by
  exact
    packedTile65536 1181985024 1182050560 13 3115 34380 30 _ _ (417809 / 20000) (261131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182050560 :
    ThetaLowerSegment 1182050560 1182116096 (59100405993659 / 50000) (3693983822624 / 3125) := by
  exact
    packedTile65536 1182050560 1182116096 13 3193 34380 30 _ _ (41781 / 2000) (2089053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182116096 :
    ThetaLowerSegment 1182116096 1182181632 (3693983822624 / 3125) (738837592513 / 625) := by
  exact
    packedTile65536 1182116096 1182181632 13 3127 34381 30 _ _ (65283 / 3125) (2089059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182181632 :
    ThetaLowerSegment 1182181632 1182247168 (738837592513 / 625) (14777560316867 / 12500) := by
  exact
    packedTile65536 1182181632 1182247168 13 3096 34382 30 _ _ (2089061 / 100000) (261133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182247168 :
    ThetaLowerSegment 1182247168 1182312704 (14777560316867 / 12500)
      (118227094431991 / 100000) := by
  exact
    packedTile65536 1182247168 1182312704 13 3165 34383 30 _ _ (2089067 / 100000) (208907 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182312704 :
    ThetaLowerSegment 1182312704 1182378240 (118227094431991 / 100000) (4729344660591 / 4000) := by
  exact
    packedTile65536 1182312704 1182378240 13 3122 34384 30 _ _ (130567 / 6250) (83563 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182378240 :
    ThetaLowerSegment 1182378240 1182443776 (4729344660591 / 4000) (118240182486929 / 100000) := by
  exact
    packedTile65536 1182378240 1182443776 13 3143 34385 30 _ _ (1044539 / 50000) (2089081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182443776 :
    ThetaLowerSegment 1182443776 1182509312 (118240182486929 / 100000)
      (59123344990237 / 50000) := by
  exact
    packedTile65536 1182443776 1182509312 13 3115 34386 30 _ _ (2089083 / 100000) (1044543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182509312 :
    ThetaLowerSegment 1182509312 1182574848 (59123344990237 / 50000) (23650649526169 / 20000) := by
  exact
    packedTile65536 1182509312 1182574848 13 3139 34387 30 _ _ (2089089 / 100000) (522273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182574848 :
    ThetaLowerSegment 1182574848 1182640384 (23650649526169 / 20000) (23651959388107 / 20000) := by
  exact
    packedTile65536 1182574848 1182640384 13 3135 34388 30 _ _ (1044547 / 50000) (2089097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182640384 :
    ThetaLowerSegment 1182640384 1182705920 (23651959388107 / 20000) (23653271342907 / 20000) := by
  exact
    packedTile65536 1182640384 1182705920 13 3140 34389 30 _ _ (20891 / 1000) (2089103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182705920 :
    ThetaLowerSegment 1182705920 1182771456 (23653271342907 / 20000)
      (118272939487541 / 100000) := by
  exact
    packedTile65536 1182705920 1182771456 13 3151 34390 30 _ _ (1044553 / 50000) (2089109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182771456 :
    ThetaLowerSegment 1182771456 1182836992 (118272939487541 / 100000) (4731180306101 / 4000) := by
  exact
    packedTile65536 1182771456 1182836992 13 3144 34391 30 _ _ (2089111 / 100000) (1044557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182836992 :
    ThetaLowerSegment 1182836992 1182902528 (4731180306101 / 4000) (3696436148647 / 3125) := by
  exact
    packedTile65536 1182836992 1182902528 13 3087 34392 30 _ _ (2089117 / 100000) (13057 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182902528 :
    ThetaLowerSegment 1182902528 1182968064 (3696436148647 / 3125) (29573111392409 / 25000) := by
  exact
    packedTile65536 1182902528 1182968064 13 3106 34393 30 _ _ (1044561 / 50000) (16713 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1182968064 :
    ThetaLowerSegment 1182968064 1183033600 (29573111392409 / 25000) (29574764937221 / 25000) := by
  exact
    packedTile65536 1182968064 1183033600 13 3166 34394 30 _ _ (261141 / 12500) (2089131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183033600 :
    ThetaLowerSegment 1183033600 1183099136 (29574764937221 / 25000)
      (118305575754711 / 100000) := by
  exact
    packedTile65536 1183033600 1183099136 13 3119 34395 30 _ _ (2089133 / 100000) (130571 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183099136 :
    ThetaLowerSegment 1183099136 1183164672 (118305575754711 / 100000)
      (14789018784393 / 12500) := by
  exact
    packedTile65536 1183099136 1183164672 13 3147 34396 30 _ _ (2089139 / 100000) (1044571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183164672 :
    ThetaLowerSegment 1183164672 1183230208 (14789018784393 / 12500) (2957967963597 / 2500) := by
  exact
    packedTile65536 1183164672 1183230208 13 3144 34397 30 _ _ (261143 / 12500) (2089147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183230208 :
    ThetaLowerSegment 1183230208 1183295744 (2957967963597 / 2500) (739533408298 / 625) := by
  exact
    packedTile65536 1183230208 1183295744 13 3172 34398 30 _ _ (41783 / 2000) (2089153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183295744 :
    ThetaLowerSegment 1183295744 1183361280 (739533408298 / 625) (23666394007637 / 20000) := by
  exact
    packedTile65536 1183295744 1183361280 13 3171 34399 30 _ _ (417831 / 20000) (1044579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183361280 :
    ThetaLowerSegment 1183361280 1183426816 (23666394007637 / 20000) (59169257689799 / 50000) := by
  exact
    packedTile65536 1183361280 1183426816 13 3133 34400 30 _ _ (2089161 / 100000) (522291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183426816 :
    ThetaLowerSegment 1183426816 1183492352 (59169257689799 / 50000) (59172537681989 / 50000) := by
  exact
    packedTile65536 1183426816 1183492352 13 3140 34400 30 _ _ (2089167 / 100000) (208917 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183492352 :
    ThetaLowerSegment 1183492352 1183557888 (59172537681989 / 50000) (59175764408143 / 50000) := by
  exact
    packedTile65536 1183492352 1183557888 13 3089 34401 30 _ _ (522293 / 25000) (83567 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183557888 :
    ThetaLowerSegment 1183557888 1183623424 (59175764408143 / 50000) (29589500794727 / 25000) := by
  exact
    packedTile65536 1183557888 1183623424 13 3099 34402 30 _ _ (1044589 / 50000) (2089181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183623424 :
    ThetaLowerSegment 1183623424 1183688960 (29589500794727 / 25000) (59182246090653 / 50000) := by
  exact
    packedTile65536 1183623424 1183688960 13 3106 34403 30 _ _ (2089183 / 100000) (1044593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183688960 :
    ThetaLowerSegment 1183688960 1183754496 (59182246090653 / 50000) (7398189981227 / 6250) := by
  exact
    packedTile65536 1183688960 1183754496 13 3134 34404 30 _ _ (2089189 / 100000) (261149 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183754496 :
    ThetaLowerSegment 1183754496 1183820032 (7398189981227 / 6250) (29594403075989 / 25000) := by
  exact
    packedTile65536 1183754496 1183820032 13 3146 34405 30 _ _ (1044597 / 50000) (2089197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183820032 :
    ThetaLowerSegment 1183820032 1183885568 (29594403075989 / 25000) (29596041531089 / 25000) := by
  exact
    packedTile65536 1183820032 1183885568 13 3137 34406 30 _ _ (5223 / 250) (2089203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183885568 :
    ThetaLowerSegment 1183885568 1183951104 (29596041531089 / 25000)
      (118390636392241 / 100000) := by
  exact
    packedTile65536 1183885568 1183951104 13 3097 34407 30 _ _ (417841 / 20000) (261151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183951104 :
    ThetaLowerSegment 1183951104 1184016640 (118390636392241 / 100000)
      (118397280083221 / 100000) := by
  exact
    packedTile65536 1183951104 1184016640 13 3180 34408 30 _ _ (2089211 / 100000) (1044607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184016640 :
    ThetaLowerSegment 1184016640 1184082176 (118397280083221 / 100000)
      (118403861113621 / 100000) := by
  exact
    packedTile65536 1184016640 1184082176 13 3150 34409 30 _ _ (65288 / 3125) (2089219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184082176 :
    ThetaLowerSegment 1184082176 1184147712 (118403861113621 / 100000)
      (23682078822163 / 20000) := by
  exact
    packedTile65536 1184082176 1184147712 13 3127 34410 30 _ _ (1044611 / 50000) (83569 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184147712 :
    ThetaLowerSegment 1184147712 1184213248 (23682078822163 / 20000)
      (118416858179153 / 100000) := by
  exact
    packedTile65536 1184147712 1184213248 13 3094 34411 30 _ _ (2089227 / 100000) (208923 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184213248 :
    ThetaLowerSegment 1184213248 1184278784 (118416858179153 / 100000)
      (118423418370773 / 100000) := by
  exact
    packedTile65536 1184213248 1184278784 13 3140 34412 30 _ _ (2089233 / 100000) (522309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184278784 :
    ThetaLowerSegment 1184278784 1184344320 (118423418370773 / 100000)
      (118429993202759 / 100000) := by
  exact
    packedTile65536 1184278784 1184344320 13 3147 34413 30 _ _ (1044619 / 50000) (2089241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184344320 :
    ThetaLowerSegment 1184344320 1184409856 (118429993202759 / 100000)
      (118436601481531 / 100000) := by
  exact
    packedTile65536 1184344320 1184409856 13 3163 34414 30 _ _ (522311 / 25000) (2089247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184409856 :
    ThetaLowerSegment 1184409856 1184475392 (118436601481531 / 100000)
      (118443067710281 / 100000) := by
  exact
    packedTile65536 1184409856 1184475392 13 3095 34415 30 _ _ (8357 / 400) (2089253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184475392 :
    ThetaLowerSegment 1184475392 1184540928 (118443067710281 / 100000)
      (118449749147771 / 100000) := by
  exact
    packedTile65536 1184475392 1184540928 13 3198 34416 30 _ _ (417851 / 20000) (1044629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184540928 :
    ThetaLowerSegment 1184540928 1184606464 (118449749147771 / 100000)
      (59228145311981 / 50000) := by
  exact
    packedTile65536 1184540928 1184606464 13 3131 34417 30 _ _ (2089261 / 100000) (130579 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184606464 :
    ThetaLowerSegment 1184606464 1184672000 (59228145311981 / 50000) (2369258188373 / 2000) := by
  exact
    packedTile65536 1184606464 1184672000 13 3168 34418 30 _ _ (1044633 / 50000) (2089269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184672000 :
    ThetaLowerSegment 1184672000 1184737536 (2369258188373 / 2000) (59234668009661 / 50000) := by
  exact
    packedTile65536 1184672000 1184737536 13 3076 34419 30 _ _ (261159 / 12500) (83571 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184737536 :
    ThetaLowerSegment 1184737536 1184803072 (59234668009661 / 50000) (14809483387403 / 12500) := by
  exact
    packedTile65536 1184737536 1184803072 13 3126 34420 30 _ _ (2089277 / 100000) (13058 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184803072 :
    ThetaLowerSegment 1184803072 1184868608 (14809483387403 / 12500)
      (118482454608523 / 100000) := by
  exact
    packedTile65536 1184803072 1184868608 13 3153 34420 30 _ _ (2089283 / 100000) (1044643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184868608 :
    ThetaLowerSegment 1184868608 1184934144 (118482454608523 / 100000)
      (118489019151419 / 100000) := by
  exact
    packedTile65536 1184868608 1184934144 13 3142 34421 30 _ _ (261161 / 12500) (2089291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184934144 :
    ThetaLowerSegment 1184934144 1184999680 (118489019151419 / 100000)
      (23699096685411 / 20000) := by
  exact
    packedTile65536 1184934144 1184999680 13 3094 34422 30 _ _ (1044647 / 50000) (2089297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1184999680 :
    ThetaLowerSegment 1184999680 1185065216 (23699096685411 / 20000) (7406376563889 / 6250) := by
  exact
    packedTile65536 1184999680 1185065216 13 3131 34423 30 _ _ (2089299 / 100000) (1044651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185065216 :
    ThetaLowerSegment 1185065216 1185130752 (7406376563889 / 6250) (29627125466931 / 25000) := by
  exact
    packedTile65536 1185065216 1185130752 13 3100 34424 30 _ _ (417861 / 20000) (522327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185130752 :
    ThetaLowerSegment 1185130752 1185196288 (29627125466931 / 25000) (29628778111141 / 25000) := by
  exact
    packedTile65536 1185130752 1185196288 13 3164 34425 30 _ _ (208931 / 10000) (2089313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185196288 :
    ThetaLowerSegment 1185196288 1185261824 (29628778111141 / 25000) (29630414045569 / 25000) := by
  exact
    packedTile65536 1185196288 1185261824 13 3132 34426 30 _ _ (522329 / 25000) (2089319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185261824 :
    ThetaLowerSegment 1185261824 1185327360 (29630414045569 / 25000) (23705667984031 / 20000) := by
  exact
    packedTile65536 1185261824 1185327360 13 3199 34427 30 _ _ (2089321 / 100000) (522331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185327360 :
    ThetaLowerSegment 1185327360 1185392896 (23705667984031 / 20000) (59267401104283 / 50000) := by
  exact
    packedTile65536 1185327360 1185392896 13 3093 34428 30 _ _ (2089327 / 100000) (208933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185392896 :
    ThetaLowerSegment 1185392896 1185458432 (59267401104283 / 50000) (7408832819137 / 6250) := by
  exact
    packedTile65536 1185392896 1185458432 13 3122 34429 30 _ _ (2089333 / 100000) (261167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185458432 :
    ThetaLowerSegment 1185458432 1185523968 (7408832819137 / 6250) (59273931322397 / 50000) := by
  exact
    packedTile65536 1185458432 1185523968 13 3129 34430 30 _ _ (1044669 / 50000) (2089341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185523968 :
    ThetaLowerSegment 1185523968 1185589504 (59273931322397 / 50000) (59277193833053 / 50000) := by
  exact
    packedTile65536 1185523968 1185589504 13 3123 34431 30 _ _ (65292 / 3125) (2089347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185589504 :
    ThetaLowerSegment 1185589504 1185655040 (59277193833053 / 50000) (59280403073117 / 50000) := by
  exact
    packedTile65536 1185589504 1185655040 13 3072 34432 30 _ _ (2089349 / 100000) (261169 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185655040 :
    ThetaLowerSegment 1185655040 1185720576 (59280403073117 / 50000) (14820930764553 / 12500) := by
  exact
    packedTile65536 1185655040 1185720576 13 3178 34433 30 _ _ (417871 / 20000) (1044679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185720576 :
    ThetaLowerSegment 1185720576 1185786112 (14820930764553 / 12500) (14821751883033 / 12500) := by
  exact
    packedTile65536 1185720576 1185786112 13 3144 34434 30 _ _ (26117 / 1250) (2089363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185786112 :
    ThetaLowerSegment 1185786112 1185851648 (14821751883033 / 12500) (59290313953827 / 50000) := by
  exact
    packedTile65536 1185786112 1185851648 13 3165 34435 30 _ _ (1044683 / 50000) (2089369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185851648 :
    ThetaLowerSegment 1185851648 1185917184 (59290313953827 / 50000) (29646783552237 / 25000) := by
  exact
    packedTile65536 1185851648 1185917184 13 3114 34436 30 _ _ (2089371 / 100000) (1044687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185917184 :
    ThetaLowerSegment 1185917184 1185982720 (29646783552237 / 25000)
      (118593600830763 / 100000) := by
  exact
    packedTile65536 1185917184 1185982720 13 3095 34437 30 _ _ (2089377 / 100000) (104469 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1185982720 :
    ThetaLowerSegment 1185982720 1186048256 (118593600830763 / 100000)
      (118600197009737 / 100000) := by
  exact
    packedTile65536 1185982720 1186048256 13 3157 34438 30 _ _ (1044691 / 50000) (417877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186048256 :
    ThetaLowerSegment 1186048256 1186113792 (118600197009737 / 100000)
      (118606736794177 / 100000) := by
  exact
    packedTile65536 1186048256 1186113792 13 3130 34439 30 _ _ (522347 / 25000) (2089391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186113792 :
    ThetaLowerSegment 1186113792 1186179328 (118606736794177 / 100000)
      (59306695755441 / 50000) := by
  exact
    packedTile65536 1186113792 1186179328 13 3185 34440 30 _ _ (2089393 / 100000) (522349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186179328 :
    ThetaLowerSegment 1186179328 1186244864 (59306695755441 / 50000) (7413738395213 / 6250) := by
  exact
    packedTile65536 1186179328 1186244864 13 3074 34440 30 _ _ (2089399 / 100000) (1044701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186244864 :
    ThetaLowerSegment 1186244864 1186310400 (7413738395213 / 6250) (29656572346601 / 25000) := by
  exact
    packedTile65536 1186244864 1186310400 13 3099 34441 30 _ _ (522351 / 25000) (2089407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186310400 :
    ThetaLowerSegment 1186310400 1186375936 (29656572346601 / 25000) (59316457452757 / 50000) := by
  exact
    packedTile65536 1186310400 1186375936 13 3171 34442 30 _ _ (208941 / 10000) (2089413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186375936 :
    ThetaLowerSegment 1186375936 1186441472 (59316457452757 / 50000) (59319708582497 / 50000) := by
  exact
    packedTile65536 1186375936 1186441472 13 3112 34443 30 _ _ (417883 / 20000) (1044709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186441472 :
    ThetaLowerSegment 1186441472 1186507008 (59319708582497 / 50000) (59323034940729 / 50000) := by
  exact
    packedTile65536 1186441472 1186507008 13 3184 34444 30 _ _ (2089421 / 100000) (130589 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186507008 :
    ThetaLowerSegment 1186507008 1186572544 (59323034940729 / 50000) (29663164460409 / 25000) := by
  exact
    packedTile65536 1186507008 1186572544 13 3153 34445 30 _ _ (1044713 / 50000) (2089429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186572544 :
    ThetaLowerSegment 1186572544 1186638080 (29663164460409 / 25000) (29664807798677 / 25000) := by
  exact
    packedTile65536 1186572544 1186638080 13 3146 34446 30 _ _ (261179 / 12500) (417887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186638080 :
    ThetaLowerSegment 1186638080 1186703616 (29664807798677 / 25000) (11866581083497 / 10000) := by
  exact
    packedTile65536 1186638080 1186703616 13 3149 34447 30 _ _ (1044719 / 50000) (2089441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186703616 :
    ThetaLowerSegment 1186703616 1186769152 (11866581083497 / 10000)
      (118672390490977 / 100000) := by
  exact
    packedTile65536 1186703616 1186769152 13 3149 34448 30 _ _ (2089443 / 100000) (1044723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186769152 :
    ThetaLowerSegment 1186769152 1186834688 (118672390490977 / 100000) (4747154878471 / 4000) := by
  exact
    packedTile65536 1186769152 1186834688 13 3102 34449 30 _ _ (2089449 / 100000) (522363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186834688 :
    ThetaLowerSegment 1186834688 1186900224 (4747154878471 / 4000) (118685445384059 / 100000) := by
  exact
    packedTile65536 1186834688 1186900224 13 3146 34450 30 _ _ (1044727 / 50000) (2089457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186900224 :
    ThetaLowerSegment 1186900224 1186965760 (118685445384059 / 100000)
      (118691878831399 / 100000) := by
  exact
    packedTile65536 1186900224 1186965760 13 3079 34451 30 _ _ (104473 / 5000) (2089463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186965760 :
    ThetaLowerSegment 1186965760 1187031296 (118691878831399 / 100000)
      (29674585386661 / 25000) := by
  exact
    packedTile65536 1186965760 1187031296 13 3093 34452 30 _ _ (417893 / 20000) (522367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187031296 :
    ThetaLowerSegment 1187031296 1187096832 (29674585386661 / 25000)
      (118704933827649 / 100000) := by
  exact
    packedTile65536 1187031296 1187096832 13 3155 34453 30 _ _ (2089471 / 100000) (1044737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187096832 :
    ThetaLowerSegment 1187096832 1187162368 (118704933827649 / 100000)
      (23742270121689 / 20000) := by
  exact
    packedTile65536 1187096832 1187162368 13 3071 34454 30 _ _ (522369 / 25000) (2089479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187162368 :
    ThetaLowerSegment 1187162368 1187227904 (23742270121689 / 20000)
      (118717924118817 / 100000) := by
  exact
    packedTile65536 1187162368 1187227904 13 3146 34455 30 _ _ (1044741 / 50000) (417897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187227904 :
    ThetaLowerSegment 1187227904 1187293440 (118717924118817 / 100000)
      (59362266583099 / 50000) := by
  exact
    packedTile65536 1187227904 1187293440 13 3163 34456 30 _ _ (2089487 / 100000) (208949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187293440 :
    ThetaLowerSegment 1187293440 1187358976 (59362266583099 / 50000) (59365522013193 / 50000) := by
  exact
    packedTile65536 1187293440 1187358976 13 3116 34457 30 _ _ (2089493 / 100000) (261187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187358976 :
    ThetaLowerSegment 1187358976 1187424512 (59365522013193 / 50000) (14842216041311 / 12500) := by
  exact
    packedTile65536 1187358976 1187424512 13 3199 34458 30 _ _ (1044749 / 50000) (2089501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187424512 :
    ThetaLowerSegment 1187424512 1187490048 (14842216041311 / 12500) (2968611308859 / 2500) := by
  exact
    packedTile65536 1187424512 1187490048 13 3218 34459 30 _ _ (65297 / 3125) (2089507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187490048 :
    ThetaLowerSegment 1187490048 1187555584 (2968611308859 / 2500) (59375500437783 / 50000) := by
  exact
    packedTile65536 1187490048 1187555584 13 3134 34459 30 _ _ (2089509 / 100000) (261189 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187555584 :
    ThetaLowerSegment 1187555584 1187621120 (59375500437783 / 50000)
      (118757584937331 / 100000) := by
  exact
    packedTile65536 1187555584 1187621120 13 3151 34460 30 _ _ (417903 / 20000) (1044759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187621120 :
    ThetaLowerSegment 1187621120 1187686656 (118757584937331 / 100000)
      (118764114687331 / 100000) := by
  exact
    packedTile65536 1187621120 1187686656 13 3125 34461 30 _ _ (26119 / 1250) (2089523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187686656 :
    ThetaLowerSegment 1187686656 1187752192 (118764114687331 / 100000) (4750823187231 / 4000) := by
  exact
    packedTile65536 1187686656 1187752192 13 3094 34462 30 _ _ (1044763 / 50000) (2089529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187752192 :
    ThetaLowerSegment 1187752192 1187817728 (4750823187231 / 4000) (118777216031231 / 100000) := by
  exact
    packedTile65536 1187752192 1187817728 13 3176 34463 30 _ _ (2089531 / 100000) (1044767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187817728 :
    ThetaLowerSegment 1187817728 1187883264 (118777216031231 / 100000)
      (118783890012409 / 100000) := by
  exact
    packedTile65536 1187817728 1187883264 13 3194 34464 30 _ _ (2089537 / 100000) (104477 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187883264 :
    ThetaLowerSegment 1187883264 1187948800 (118783890012409 / 100000)
      (118790459532457 / 100000) := by
  exact
    packedTile65536 1187883264 1187948800 13 3144 34465 30 _ _ (1044771 / 50000) (417909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1187948800 :
    ThetaLowerSegment 1187948800 1188014336 (118790459532457 / 100000)
      (23759392023257 / 20000) := by
  exact
    packedTile65536 1187948800 1188014336 13 3111 34466 30 _ _ (522387 / 25000) (2089551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188014336 :
    ThetaLowerSegment 1188014336 1188079872 (23759392023257 / 20000)
      (118803475342539 / 100000) := by
  exact
    packedTile65536 1188014336 1188079872 13 3118 34467 30 _ _ (2089553 / 100000) (522389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188079872 :
    ThetaLowerSegment 1188079872 1188145408 (118803475342539 / 100000)
      (118809911184259 / 100000) := by
  exact
    packedTile65536 1188079872 1188145408 13 3080 34468 30 _ _ (2089559 / 100000) (1044781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188145408 :
    ThetaLowerSegment 1188145408 1188210944 (118809911184259 / 100000)
      (118816566445599 / 100000) := by
  exact
    packedTile65536 1188145408 1188210944 13 3185 34469 30 _ _ (522391 / 25000) (2089567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188210944 :
    ThetaLowerSegment 1188210944 1188276480 (118816566445599 / 100000)
      (118823096351849 / 100000) := by
  exact
    packedTile65536 1188210944 1188276480 13 3125 34470 30 _ _ (208957 / 10000) (2089573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188276480 :
    ThetaLowerSegment 1188276480 1188342016 (118823096351849 / 100000) (3713425559857 / 3125) := by
  exact
    packedTile65536 1188276480 1188342016 13 3121 34471 30 _ _ (83583 / 4000) (1044789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188342016 :
    ThetaLowerSegment 1188342016 1188407552 (3713425559857 / 3125) (59418087510301 / 50000) := by
  exact
    packedTile65536 1188342016 1188407552 13 3138 34472 30 _ _ (2089581 / 100000) (130599 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188407552 :
    ThetaLowerSegment 1188407552 1188473088 (59418087510301 / 50000) (23768576101057 / 20000) := by
  exact
    packedTile65536 1188407552 1188473088 13 3209 34473 30 _ _ (2089587 / 100000) (208959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188473088 :
    ThetaLowerSegment 1188473088 1188538624 (23768576101057 / 20000)
      (118849406301101 / 100000) := by
  exact
    packedTile65536 1188473088 1188538624 13 3123 34474 30 _ _ (261199 / 12500) (417919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188538624 :
    ThetaLowerSegment 1188538624 1188604160 (118849406301101 / 100000)
      (23771188512729 / 20000) := by
  exact
    packedTile65536 1188538624 1188604160 13 3128 34475 30 _ _ (1044799 / 50000) (2089601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188604160 :
    ThetaLowerSegment 1188604160 1188669696 (23771188512729 / 20000) (29715613964049 / 25000) := by
  exact
    packedTile65536 1188604160 1188669696 13 3117 34476 30 _ _ (2089603 / 100000) (1044803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188669696 :
    ThetaLowerSegment 1188669696 1188735232 (29715613964049 / 25000) (59434544137581 / 50000) := by
  exact
    packedTile65536 1188669696 1188735232 13 3174 34477 30 _ _ (2089609 / 100000) (522403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188735232 :
    ThetaLowerSegment 1188735232 1188800768 (59434544137581 / 50000) (29718934879131 / 25000) := by
  exact
    packedTile65536 1188735232 1188800768 13 3183 34478 30 _ _ (1044807 / 50000) (2089617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188800768 :
    ThetaLowerSegment 1188800768 1188866304 (29718934879131 / 25000) (29720580454881 / 25000) := by
  exact
    packedTile65536 1188800768 1188866304 13 3150 34478 30 _ _ (104481 / 5000) (2089623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188866304 :
    ThetaLowerSegment 1188866304 1188931840 (29720580454881 / 25000) (59444456248387 / 50000) := by
  exact
    packedTile65536 1188866304 1188931840 13 3154 34479 30 _ _ (16717 / 800) (522407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188931840 :
    ThetaLowerSegment 1188931840 1188997376 (59444456248387 / 50000) (14861928495779 / 12500) := by
  exact
    packedTile65536 1188931840 1188997376 13 3118 34480 30 _ _ (2089631 / 100000) (1044817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1188997376 :
    ThetaLowerSegment 1188997376 1189062912 (14861928495779 / 12500) (14862739274547 / 12500) := by
  exact
    packedTile65536 1188997376 1189062912 13 3104 34481 30 _ _ (522409 / 25000) (2089639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189062912 :
    ThetaLowerSegment 1189062912 1189128448 (14862739274547 / 12500) (3715889864758 / 3125) := by
  exact
    packedTile65536 1189062912 1189128448 13 3140 34482 30 _ _ (1044821 / 50000) (417929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189128448 :
    ThetaLowerSegment 1189128448 1189193984 (3715889864758 / 3125) (2972874466343 / 2500) := by
  exact
    packedTile65536 1189128448 1189193984 13 3112 34483 30 _ _ (2089647 / 100000) (41793 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189193984 :
    ThetaLowerSegment 1189193984 1189259520 (2972874466343 / 2500) (118921504640039 / 100000) := by
  exact
    packedTile65536 1189193984 1189259520 13 3123 34484 30 _ _ (2089653 / 100000) (261207 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189259520 :
    ThetaLowerSegment 1189259520 1189325056 (118921504640039 / 100000)
      (118928095421371 / 100000) := by
  exact
    packedTile65536 1189259520 1189325056 13 3154 34485 30 _ _ (1044829 / 50000) (2089661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189325056 :
    ThetaLowerSegment 1189325056 1189390592 (118928095421371 / 100000)
      (118934613083387 / 100000) := by
  exact
    packedTile65536 1189325056 1189390592 13 3119 34486 30 _ _ (65302 / 3125) (2089667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189390592 :
    ThetaLowerSegment 1189390592 1189456128 (118934613083387 / 100000) (7433825113109 / 6250) := by
  exact
    packedTile65536 1189390592 1189456128 13 3153 34487 30 _ _ (2089669 / 100000) (261209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189456128 :
    ThetaLowerSegment 1189456128 1189521664 (7433825113109 / 6250) (59473887963647 / 50000) := by
  exact
    packedTile65536 1189456128 1189521664 13 3146 34488 30 _ _ (83587 / 4000) (1044839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189521664 :
    ThetaLowerSegment 1189521664 1189587200 (59473887963647 / 50000) (59477243989727 / 50000) := by
  exact
    packedTile65536 1189521664 1189587200 13 3212 34489 30 _ _ (26121 / 1250) (2089683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189587200 :
    ThetaLowerSegment 1189587200 1189652736 (59477243989727 / 50000) (59480462106167 / 50000) := by
  exact
    packedTile65536 1189587200 1189652736 13 3080 34490 30 _ _ (1044843 / 50000) (2089689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189652736 :
    ThetaLowerSegment 1189652736 1189718272 (59480462106167 / 50000)
      (118967546443113 / 100000) := by
  exact
    packedTile65536 1189652736 1189718272 13 3169 34491 30 _ _ (2089691 / 100000) (1044847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189718272 :
    ThetaLowerSegment 1189718272 1189783808 (118967546443113 / 100000)
      (59486996579179 / 50000) := by
  exact
    packedTile65536 1189718272 1189783808 13 3085 34492 30 _ _ (2089697 / 100000) (20897 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189783808 :
    ThetaLowerSegment 1189783808 1189849344 (59486996579179 / 50000) (59490266962809 / 50000) := by
  exact
    packedTile65536 1189783808 1189849344 13 3130 34493 30 _ _ (1044851 / 50000) (417941 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189849344 :
    ThetaLowerSegment 1189849344 1189914880 (59490266962809 / 50000) (59493500785939 / 50000) := by
  exact
    packedTile65536 1189849344 1189914880 13 3095 34494 30 _ _ (522427 / 25000) (2089711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189914880 :
    ThetaLowerSegment 1189914880 1189980416 (59493500785939 / 50000)
      (118993544463281 / 100000) := by
  exact
    packedTile65536 1189914880 1189980416 13 3131 34495 30 _ _ (2089713 / 100000) (522429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1189980416 :
    ThetaLowerSegment 1189980416 1190045952 (118993544463281 / 100000)
      (59500060404487 / 50000) := by
  exact
    packedTile65536 1189980416 1190045952 13 3147 34496 30 _ _ (2089719 / 100000) (1044861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190045952 :
    ThetaLowerSegment 1190045952 1190111488 (59500060404487 / 50000) (59503322463651 / 50000) := by
  exact
    packedTile65536 1190045952 1190111488 13 3122 34497 30 _ _ (522431 / 25000) (2089727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190111488 :
    ThetaLowerSegment 1190111488 1190177024 (59503322463651 / 50000) (14876639602639 / 12500) := by
  exact
    packedTile65536 1190111488 1190177024 13 3097 34497 30 _ _ (208973 / 10000) (2089733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190177024 :
    ThetaLowerSegment 1190177024 1190242560 (14876639602639 / 12500)
      (119019797703907 / 100000) := by
  exact
    packedTile65536 1190177024 1190242560 13 3197 34498 30 _ _ (417947 / 20000) (1044869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190242560 :
    ThetaLowerSegment 1190242560 1190308096 (119019797703907 / 100000)
      (59513195418381 / 50000) := by
  exact
    packedTile65536 1190242560 1190308096 13 3155 34499 30 _ _ (2089741 / 100000) (130609 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190308096 :
    ThetaLowerSegment 1190308096 1190373632 (59513195418381 / 50000) (59516509755537 / 50000) := by
  exact
    packedTile65536 1190308096 1190373632 13 3172 34500 30 _ _ (1044873 / 50000) (2089749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190373632 :
    ThetaLowerSegment 1190373632 1190439168 (59516509755537 / 50000) (59519754095517 / 50000) := by
  exact
    packedTile65536 1190373632 1190439168 13 3105 34501 30 _ _ (261219 / 12500) (417951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190439168 :
    ThetaLowerSegment 1190439168 1190504704 (59519754095517 / 50000) (14880775993997 / 12500) := by
  exact
    packedTile65536 1190439168 1190504704 13 3206 34502 30 _ _ (2089757 / 100000) (13061 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190504704 :
    ThetaLowerSegment 1190504704 1190570240 (14880775993997 / 12500) (1488159309133 / 1250) := by
  exact
    packedTile65536 1190504704 1190570240 13 3128 34503 30 _ _ (2089763 / 100000) (1044883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190570240 :
    ThetaLowerSegment 1190570240 1190635776 (1488159309133 / 1250) (1488241854969 / 1250) := by
  exact
    packedTile65536 1190570240 1190635776 13 3160 34504 30 _ _ (261221 / 12500) (2089771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190635776 :
    ThetaLowerSegment 1190635776 1190701312 (1488241854969 / 1250) (11906566996387 / 10000) := by
  exact
    packedTile65536 1190635776 1190701312 13 3025 34505 30 _ _ (1044887 / 50000) (2089777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190701312 :
    ThetaLowerSegment 1190701312 1190766848 (11906566996387 / 10000)
      (119072175445897 / 100000) := by
  exact
    packedTile65536 1190701312 1190766848 13 3113 34506 30 _ _ (2089779 / 100000) (1044891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190766848 :
    ThetaLowerSegment 1190766848 1190832384 (119072175445897 / 100000)
      (119078712293377 / 100000) := by
  exact
    packedTile65536 1190766848 1190832384 13 3128 34507 30 _ _ (417957 / 20000) (522447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190832384 :
    ThetaLowerSegment 1190832384 1190897920 (119078712293377 / 100000)
      (119085259605447 / 100000) := by
  exact
    packedTile65536 1190832384 1190897920 13 3133 34508 30 _ _ (208979 / 10000) (2089793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190897920 :
    ThetaLowerSegment 1190897920 1190963456 (119085259605447 / 100000)
      (23818363477059 / 20000) := by
  exact
    packedTile65536 1190897920 1190963456 13 3138 34509 30 _ _ (522449 / 25000) (2089799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190963456 :
    ThetaLowerSegment 1190963456 1191028992 (23818363477059 / 20000) (23819675872087 / 20000) := by
  exact
    packedTile65536 1190963456 1191028992 13 3140 34510 30 _ _ (2089801 / 100000) (522451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191028992 :
    ThetaLowerSegment 1191028992 1191094528 (23819675872087 / 20000) (23820975732041 / 20000) := by
  exact
    packedTile65536 1191028992 1191094528 13 3110 34511 30 _ _ (2089807 / 100000) (208981 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191094528 :
    ThetaLowerSegment 1191094528 1191160064 (23820975732041 / 20000) (4764457208833 / 4000) := by
  exact
    packedTile65536 1191094528 1191160064 13 3135 34512 30 _ _ (522453 / 25000) (417963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191160064 :
    ThetaLowerSegment 1191160064 1191225600 (4764457208833 / 4000) (23823588000779 / 20000) := by
  exact
    packedTile65536 1191160064 1191225600 13 3115 34513 30 _ _ (1044909 / 50000) (2089821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191225600 :
    ThetaLowerSegment 1191225600 1191291136 (23823588000779 / 20000) (14890565629521 / 12500) := by
  exact
    packedTile65536 1191225600 1191291136 13 3151 34514 30 _ _ (2089823 / 100000) (1044913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191291136 :
    ThetaLowerSegment 1191291136 1191356672 (14890565629521 / 12500) (23826218673743 / 20000) := by
  exact
    packedTile65536 1191291136 1191356672 13 3143 34515 30 _ _ (2089829 / 100000) (261229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191356672 :
    ThetaLowerSegment 1191356672 1191422208 (23826218673743 / 20000) (4765506217899 / 4000) := by
  exact
    packedTile65536 1191356672 1191422208 13 3140 34516 30 _ _ (1044917 / 50000) (2089837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191422208 :
    ThetaLowerSegment 1191422208 1191487744 (4765506217899 / 4000) (23828858973831 / 20000) := by
  exact
    packedTile65536 1191422208 1191487744 13 3177 34516 30 _ _ (26123 / 1250) (2089843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191487744 :
    ThetaLowerSegment 1191487744 1191553280 (23828858973831 / 20000) (23830151333979 / 20000) := by
  exact
    packedTile65536 1191487744 1191553280 13 3092 34517 30 _ _ (417969 / 20000) (261231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191553280 :
    ThetaLowerSegment 1191553280 1191618816 (23830151333979 / 20000)
      (119157176692167 / 100000) := by
  exact
    packedTile65536 1191553280 1191618816 13 3072 34518 30 _ _ (2089851 / 100000) (1044927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191618816 :
    ThetaLowerSegment 1191618816 1191684352 (119157176692167 / 100000)
      (23832753201627 / 20000) := by
  exact
    packedTile65536 1191618816 1191684352 13 3153 34519 30 _ _ (65308 / 3125) (2089859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191684352 :
    ThetaLowerSegment 1191684352 1191749888 (23832753201627 / 20000)
      (119170215322267 / 100000) := by
  exact
    packedTile65536 1191684352 1191749888 13 3086 34520 30 _ _ (1044931 / 50000) (417973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191749888 :
    ThetaLowerSegment 1191749888 1191815424 (119170215322267 / 100000)
      (119176727347839 / 100000) := by
  exact
    packedTile65536 1191749888 1191815424 13 3116 34521 30 _ _ (2089867 / 100000) (208987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191815424 :
    ThetaLowerSegment 1191815424 1191880960 (119176727347839 / 100000)
      (29795814550241 / 25000) := by
  exact
    packedTile65536 1191815424 1191880960 13 3125 34522 30 _ _ (2089873 / 100000) (522469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191880960 :
    ThetaLowerSegment 1191880960 1191946496 (29795814550241 / 25000) (59594973950221 / 50000) := by
  exact
    packedTile65536 1191880960 1191946496 13 3201 34523 30 _ _ (1044939 / 50000) (2089881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1191946496 :
    ThetaLowerSegment 1191946496 1192012032 (59594973950221 / 50000) (59598260292811 / 50000) := by
  exact
    packedTile65536 1191946496 1192012032 13 3145 34524 30 _ _ (522471 / 25000) (2089887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192012032 :
    ThetaLowerSegment 1192012032 1192077568 (59598260292811 / 50000) (7450191371137 / 6250) := by
  exact
    packedTile65536 1192012032 1192077568 13 3130 34525 30 _ _ (2089889 / 100000) (522473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192077568 :
    ThetaLowerSegment 1192077568 1192143104 (7450191371137 / 6250) (119209647197337 / 100000) := by
  exact
    packedTile65536 1192077568 1192143104 13 3151 34526 30 _ _ (417979 / 20000) (1044949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192143104 :
    ThetaLowerSegment 1192143104 1192208640 (119209647197337 / 100000)
      (119216061100437 / 100000) := by
  exact
    packedTile65536 1192143104 1192208640 13 3069 34527 30 _ _ (20899 / 1000) (2089903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192208640 :
    ThetaLowerSegment 1192208640 1192274176 (119216061100437 / 100000)
      (119222721630859 / 100000) := by
  exact
    packedTile65536 1192208640 1192274176 13 3187 34528 30 _ _ (1044953 / 50000) (2089909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192274176 :
    ThetaLowerSegment 1192274176 1192339712 (119222721630859 / 100000)
      (119229271411933 / 100000) := by
  exact
    packedTile65536 1192274176 1192339712 13 3134 34529 30 _ _ (2089911 / 100000) (1044957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192339712 :
    ThetaLowerSegment 1192339712 1192405248 (119229271411933 / 100000)
      (29808987174187 / 25000) := by
  exact
    packedTile65536 1192339712 1192405248 13 3195 34530 30 _ _ (2089917 / 100000) (13062 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192405248 :
    ThetaLowerSegment 1192405248 1192470784 (29808987174187 / 25000) (59621187603449 / 50000) := by
  exact
    packedTile65536 1192405248 1192470784 13 3075 34531 30 _ _ (1044961 / 50000) (83597 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192470784 :
    ThetaLowerSegment 1192470784 1192536320 (59621187603449 / 50000) (11924894594053 / 10000) := by
  exact
    packedTile65536 1192470784 1192536320 13 3144 34532 30 _ _ (261241 / 12500) (2089931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192536320 :
    ThetaLowerSegment 1192536320 1192601856 (11924894594053 / 10000) (11925559192747 / 10000) := by
  exact
    packedTile65536 1192536320 1192601856 13 3180 34533 30 _ _ (2089933 / 100000) (130621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192601856 :
    ThetaLowerSegment 1192601856 1192667392 (11925559192747 / 10000) (745388072736 / 625) := by
  exact
    packedTile65536 1192601856 1192667392 13 3110 34534 30 _ _ (2089939 / 100000) (1044971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192667392 :
    ThetaLowerSegment 1192667392 1192732928 (745388072736 / 625) (14908587243843 / 12500) := by
  exact
    packedTile65536 1192667392 1192732928 13 3161 34535 30 _ _ (261243 / 12500) (2089947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192732928 :
    ThetaLowerSegment 1192732928 1192798464 (14908587243843 / 12500) (59637618702147 / 50000) := by
  exact
    packedTile65536 1192732928 1192798464 13 3129 34535 30 _ _ (41799 / 2000) (2089953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192798464 :
    ThetaLowerSegment 1192798464 1192864000 (59637618702147 / 50000)
      (119281814492679 / 100000) := by
  exact
    packedTile65536 1192798464 1192864000 13 3147 34536 30 _ _ (417991 / 20000) (1044979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192864000 :
    ThetaLowerSegment 1192864000 1192929536 (119281814492679 / 100000)
      (119288293371779 / 100000) := by
  exact
    packedTile65536 1192864000 1192929536 13 3100 34537 30 _ _ (2089961 / 100000) (522491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192929536 :
    ThetaLowerSegment 1192929536 1192995072 (119288293371779 / 100000)
      (119294926923863 / 100000) := by
  exact
    packedTile65536 1192929536 1192995072 13 3174 34538 30 _ _ (1044983 / 50000) (2089969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1192995072 :
    ThetaLowerSegment 1192995072 1193060608 (119294926923863 / 100000)
      (119301422556839 / 100000) := by
  exact
    packedTile65536 1192995072 1193060608 13 3108 34539 30 _ _ (522493 / 25000) (83599 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193060608 :
    ThetaLowerSegment 1193060608 1193126144 (119301422556839 / 100000)
      (119307947465033 / 100000) := by
  exact
    packedTile65536 1193060608 1193126144 13 3122 34540 30 _ _ (2089977 / 100000) (104499 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193126144 :
    ThetaLowerSegment 1193126144 1193191680 (119307947465033 / 100000)
      (14914325507611 / 12500) := by
  exact
    packedTile65536 1193126144 1193191680 13 3185 34541 30 _ _ (2089983 / 100000) (1044993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193191680 :
    ThetaLowerSegment 1193191680 1193257216 (14914325507611 / 12500) (29830284863341 / 25000) := by
  exact
    packedTile65536 1193191680 1193257216 13 3127 34542 30 _ _ (522497 / 25000) (2089991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193257216 :
    ThetaLowerSegment 1193257216 1193322752 (29830284863341 / 25000) (59663889682151 / 50000) := by
  exact
    packedTile65536 1193257216 1193322752 13 3177 34543 30 _ _ (1044997 / 50000) (2089997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193322752 :
    ThetaLowerSegment 1193322752 1193339136 (59663889682151 / 50000) (14916174627941 / 12500) := by
  exact
    packedTile65536 1193322752 1193339136 11 774 34544 30 _ _ (2089999 / 100000) (1045001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1193339136 :
    ThetaLowerSegment 1193339136 1193341184 (14916174627941 / 12500) (3729049404488 / 3125) := by
  exact
    packedTile65536 1193339136 1193341184 8 88 34544 30 _ _ (2090001 / 100000) (522501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1161341184_1193341184 :
    ThetaLowerSegment 1161341184 1193341184 (3629048640001 / 3125) (3729049404488 / 3125) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1161341184 cell1161406720)
                    (ThetaLowerSegment.join cell1161472256 cell1161537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1161603328 cell1161668864)
                    (ThetaLowerSegment.join cell1161734400 cell1161799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1161865472 cell1161931008)
                    (ThetaLowerSegment.join cell1161996544 cell1162062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1162127616 cell1162193152)
                    (ThetaLowerSegment.join cell1162258688 cell1162324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1162389760 cell1162455296)
                    (ThetaLowerSegment.join cell1162520832 cell1162586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1162651904 cell1162717440)
                    (ThetaLowerSegment.join cell1162782976 cell1162848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1162914048 cell1162979584)
                    (ThetaLowerSegment.join cell1163045120 cell1163110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1163176192 cell1163241728)
                    (ThetaLowerSegment.join cell1163307264 cell1163372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1163438336 cell1163503872)
                    (ThetaLowerSegment.join cell1163569408 cell1163634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1163700480 cell1163766016)
                    (ThetaLowerSegment.join cell1163831552 cell1163897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1163962624 cell1164093696)
                    (ThetaLowerSegment.join cell1164224768 cell1164355840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1164421376 cell1164486912)
                    (ThetaLowerSegment.join cell1164617984 cell1164749056))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1164880128 cell1165011200)
                    (ThetaLowerSegment.join cell1165142272 cell1165273344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1165404416 cell1165535488)
                    (ThetaLowerSegment.join cell1165666560 cell1165797632)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1165928704 cell1166059776)
                    (ThetaLowerSegment.join cell1166190848 cell1166321920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1166452992 cell1166584064)
                    (ThetaLowerSegment.join cell1166715136 cell1166846208))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1166977280 cell1167108352)
                    (ThetaLowerSegment.join cell1167239424 cell1167370496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1167501568 cell1167632640)
                    (ThetaLowerSegment.join cell1167763712 cell1167894784)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1168025856 cell1168156928)
                    (ThetaLowerSegment.join cell1168222464 cell1168288000))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1168353536 cell1168419072)
                    (ThetaLowerSegment.join cell1168550144 cell1168615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1168681216 cell1168746752)
                    (ThetaLowerSegment.join cell1168812288 cell1168877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1169008896 cell1169074432)
                    (ThetaLowerSegment.join cell1169139968 cell1169205504)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1169336576 cell1169402112)
                    (ThetaLowerSegment.join cell1169467648 cell1169533184))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1169598720 cell1169664256)
                    (ThetaLowerSegment.join cell1169729792 cell1169795328)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1169926400 cell1170057472)
                    (ThetaLowerSegment.join cell1170188544 cell1170319616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1170450688 cell1170581760)
                    (ThetaLowerSegment.join cell1170712832 cell1170843904)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1170974976 cell1171106048)
                    (ThetaLowerSegment.join cell1171237120 cell1171368192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1171499264 cell1171630336)
                    (ThetaLowerSegment.join cell1171761408 cell1171892480))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1172023552 cell1172154624)
                    (ThetaLowerSegment.join cell1172285696 cell1172416768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1172547840 cell1172678912)
                    (ThetaLowerSegment.join cell1172809984 cell1172941056)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1173072128 cell1173203200)
                    (ThetaLowerSegment.join cell1173334272 cell1173465344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1173596416 cell1173727488)
                    (ThetaLowerSegment.join cell1173858560 cell1173989632)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1174120704 cell1174251776)
                    (ThetaLowerSegment.join cell1174382848 cell1174513920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1174644992 cell1174776064)
                    (ThetaLowerSegment.join cell1174907136 cell1175038208)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1175169280 cell1175300352)
                    (ThetaLowerSegment.join cell1175431424 cell1175562496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1175693568 cell1175824640)
                    (ThetaLowerSegment.join cell1175955712 cell1176086784))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1176217856 cell1176348928)
                    (ThetaLowerSegment.join cell1176480000 cell1176611072))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1176742144 cell1176873216)
                    (ThetaLowerSegment.join cell1177004288 cell1177135360)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1177266432 cell1177397504)
                    (ThetaLowerSegment.join cell1177528576 cell1177659648))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1177790720 cell1177921792)
                    (ThetaLowerSegment.join cell1178052864 cell1178183936)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1178315008 cell1178446080)
                    (ThetaLowerSegment.join cell1178577152 cell1178708224))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1178839296 cell1178970368)
                    (ThetaLowerSegment.join cell1179101440 cell1179232512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1179363584 cell1179494656)
                    (ThetaLowerSegment.join cell1179625728 cell1179756800))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1179887872 cell1180018944)
                    (ThetaLowerSegment.join cell1180150016 cell1180281088))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1180412160 cell1180543232)
                    (ThetaLowerSegment.join cell1180674304 cell1180805376))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1180936448 cell1181067520)
                    (ThetaLowerSegment.join cell1181198592 cell1181329664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1181395200 cell1181526272)
                    (ThetaLowerSegment.join cell1181591808 cell1181722880))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1181853952 cell1181919488)
                    (ThetaLowerSegment.join cell1181985024 cell1182050560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1182116096 cell1182181632)
                    (ThetaLowerSegment.join cell1182247168 cell1182312704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1182378240 cell1182443776)
                    (ThetaLowerSegment.join cell1182509312 cell1182574848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1182640384 cell1182705920)
                    (ThetaLowerSegment.join cell1182771456 cell1182836992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1182902528 cell1182968064)
                    (ThetaLowerSegment.join cell1183033600 cell1183099136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1183164672 cell1183230208)
                    (ThetaLowerSegment.join cell1183295744 cell1183361280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1183426816 cell1183492352)
                    (ThetaLowerSegment.join cell1183557888 cell1183623424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1183688960 cell1183754496)
                    (ThetaLowerSegment.join cell1183820032 cell1183885568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1183951104 cell1184016640)
                    (ThetaLowerSegment.join cell1184082176 cell1184147712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1184213248 cell1184278784)
                    (ThetaLowerSegment.join cell1184344320 cell1184409856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1184475392 cell1184540928)
                    (ThetaLowerSegment.join cell1184606464 cell1184672000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1184737536 cell1184803072)
                    (ThetaLowerSegment.join cell1184868608 cell1184934144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1184999680 cell1185065216)
                    (ThetaLowerSegment.join cell1185130752 cell1185196288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1185261824 cell1185327360)
                    (ThetaLowerSegment.join cell1185392896 cell1185458432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1185523968 cell1185589504)
                    (ThetaLowerSegment.join cell1185655040 cell1185720576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1185786112 cell1185851648)
                    (ThetaLowerSegment.join cell1185917184 cell1185982720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1186048256 cell1186113792)
                    (ThetaLowerSegment.join cell1186179328 cell1186244864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1186310400 cell1186375936)
                  (ThetaLowerSegment.join cell1186441472 cell1186507008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1186572544 cell1186638080)
                  (ThetaLowerSegment.join cell1186703616 cell1186769152)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1186834688 cell1186900224)
                  (ThetaLowerSegment.join cell1186965760 cell1187031296))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1187096832 cell1187162368)
                  (ThetaLowerSegment.join cell1187227904 cell1187293440))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1187358976 cell1187424512)
                  (ThetaLowerSegment.join cell1187490048 cell1187555584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1187621120 cell1187686656)
                  (ThetaLowerSegment.join cell1187752192 cell1187817728)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1187883264 cell1187948800)
                  (ThetaLowerSegment.join cell1188014336 cell1188079872))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1188145408 cell1188210944)
                  (ThetaLowerSegment.join cell1188276480 cell1188342016)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1188407552 cell1188473088)
                  (ThetaLowerSegment.join cell1188538624 cell1188604160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1188669696 cell1188735232)
                  (ThetaLowerSegment.join cell1188800768 cell1188866304)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1188931840 cell1188997376)
                  (ThetaLowerSegment.join cell1189062912 cell1189128448))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1189193984 cell1189259520)
                  (ThetaLowerSegment.join cell1189325056 cell1189390592))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1189456128 cell1189521664)
                  (ThetaLowerSegment.join cell1189587200 cell1189652736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1189718272 cell1189783808)
                  (ThetaLowerSegment.join cell1189849344 cell1189914880)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1189980416 cell1190045952)
                  (ThetaLowerSegment.join cell1190111488 cell1190177024))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1190242560 cell1190308096)
                  (ThetaLowerSegment.join cell1190373632 cell1190439168))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1190504704 cell1190570240)
                  (ThetaLowerSegment.join cell1190635776 cell1190701312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1190766848 cell1190832384)
                  (ThetaLowerSegment.join cell1190897920 cell1190963456)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1191028992 cell1191094528)
                  (ThetaLowerSegment.join cell1191160064 cell1191225600))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1191291136 cell1191356672)
                  (ThetaLowerSegment.join cell1191422208 cell1191487744))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1191553280 cell1191618816)
                  (ThetaLowerSegment.join cell1191684352 cell1191749888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1191815424 cell1191880960)
                  (ThetaLowerSegment.join cell1191946496 cell1192012032)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1192077568 cell1192143104)
                  (ThetaLowerSegment.join cell1192208640 cell1192274176))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1192339712 cell1192405248)
                  (ThetaLowerSegment.join cell1192470784 cell1192536320)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1192601856 cell1192667392)
                (ThetaLowerSegment.join cell1192732928 cell1192798464))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1192864000 cell1192929536)
                (ThetaLowerSegment.join cell1192995072 cell1193060608)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1193126144 cell1193191680)
                (ThetaLowerSegment.join cell1193257216 cell1193322752))
              cell1193339136)))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
