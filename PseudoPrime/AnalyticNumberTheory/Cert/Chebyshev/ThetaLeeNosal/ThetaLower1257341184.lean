/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1257341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1225341184 :
    ThetaLowerSegment 1225341184 1225406720 (122529402903409 / 100000)
      (12253577082823 / 10000) := by
  exact
    packedTile65536 1225341184 1225406720 13 3043 35004 30 _ _ (2092647 / 100000) (41853 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225406720 :
    ThetaLowerSegment 1225406720 1225472256 (12253577082823 / 10000) (61271183433667 / 50000) := by
  exact
    packedTile65536 1225406720 1225472256 13 3152 35005 30 _ _ (523163 / 25000) (418531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225472256 :
    ThetaLowerSegment 1225472256 1225537792 (61271183433667 / 50000) (61274447980147 / 50000) := by
  exact
    packedTile65536 1225472256 1225537792 13 3120 35006 30 _ _ (1046329 / 50000) (2092661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225537792 :
    ThetaLowerSegment 1225537792 1225603328 (61274447980147 / 50000)
      (122555427161517 / 100000) := by
  exact
    packedTile65536 1225537792 1225603328 13 3121 35007 30 _ _ (2092663 / 100000) (1046333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225603328 :
    ThetaLowerSegment 1225603328 1225668864 (122555427161517 / 100000)
      (122561981397693 / 100000) := by
  exact
    packedTile65536 1225603328 1225668864 13 3132 35008 30 _ _ (523167 / 25000) (2092671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225668864 :
    ThetaLowerSegment 1225668864 1225734400 (122561981397693 / 100000)
      (122568556579401 / 100000) := by
  exact
    packedTile65536 1225668864 1225734400 13 3142 35009 30 _ _ (1046337 / 50000) (2092677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225734400 :
    ThetaLowerSegment 1225734400 1225799936 (122568556579401 / 100000)
      (122575186186473 / 100000) := by
  exact
    packedTile65536 1225734400 1225799936 13 3168 35010 30 _ _ (2092679 / 100000) (1046341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225799936 :
    ThetaLowerSegment 1225799936 1225865472 (122575186186473 / 100000)
      (122581834643541 / 100000) := by
  exact
    packedTile65536 1225799936 1225865472 13 3177 35011 30 _ _ (523171 / 25000) (2092687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225865472 :
    ThetaLowerSegment 1225865472 1225931008 (122581834643541 / 100000)
      (122588215255351 / 100000) := by
  exact
    packedTile65536 1225865472 1225931008 13 3049 35012 30 _ _ (209269 / 10000) (2092693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225931008 :
    ThetaLowerSegment 1225931008 1225996544 (122588215255351 / 100000)
      (122594614716661 / 100000) := by
  exact
    packedTile65536 1225931008 1225996544 13 3058 35013 30 _ _ (418539 / 20000) (1046349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1225996544 :
    ThetaLowerSegment 1225996544 1226062080 (122594614716661 / 100000)
      (122601177423861 / 100000) := by
  exact
    packedTile65536 1225996544 1226062080 13 3136 35014 30 _ _ (20927 / 1000) (2092703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226062080 :
    ThetaLowerSegment 1226062080 1226127616 (122601177423861 / 100000)
      (122607700388463 / 100000) := by
  exact
    packedTile65536 1226062080 1226127616 13 3117 35015 30 _ _ (1046353 / 50000) (2092709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226127616 :
    ThetaLowerSegment 1226127616 1226193152 (122607700388463 / 100000)
      (61307115869747 / 50000) := by
  exact
    packedTile65536 1226127616 1226193152 13 3121 35016 30 _ _ (2092711 / 100000) (1046357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226193152 :
    ThetaLowerSegment 1226193152 1226258688 (61307115869747 / 50000)
      (122620629175363 / 100000) := by
  exact
    packedTile65536 1226193152 1226258688 13 3057 35017 30 _ _ (2092717 / 100000) (26159 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226258688 :
    ThetaLowerSegment 1226258688 1226324224 (122620629175363 / 100000)
      (122627273567713 / 100000) := by
  exact
    packedTile65536 1226258688 1226324224 13 3175 35017 30 _ _ (1046361 / 50000) (83709 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226324224 :
    ThetaLowerSegment 1226324224 1226389760 (122627273567713 / 100000)
      (122633932625027 / 100000) := by
  exact
    packedTile65536 1226324224 1226389760 13 3182 35018 30 _ _ (2092727 / 100000) (209273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226389760 :
    ThetaLowerSegment 1226389760 1226455296 (122633932625027 / 100000)
      (122640399169997 / 100000) := by
  exact
    packedTile65536 1226389760 1226455296 13 3090 35019 30 _ _ (2092733 / 100000) (65398 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226455296 :
    ThetaLowerSegment 1226455296 1226520832 (122640399169997 / 100000)
      (24529381935583 / 20000) := by
  exact
    packedTile65536 1226455296 1226520832 13 3111 35020 30 _ _ (1046369 / 50000) (2092741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226520832 :
    ThetaLowerSegment 1226520832 1226586368 (24529381935583 / 20000) (15331670200573 / 12500) := by
  exact
    packedTile65536 1226520832 1226586368 13 3083 35021 30 _ _ (2092743 / 100000) (1046373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226586368 :
    ThetaLowerSegment 1226586368 1226651904 (15331670200573 / 12500) (15332490558181 / 12500) := by
  exact
    packedTile65536 1226586368 1226651904 13 3136 35022 30 _ _ (2092749 / 100000) (130797 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226651904 :
    ThetaLowerSegment 1226651904 1226717440 (15332490558181 / 12500) (30666585212303 / 25000) := by
  exact
    packedTile65536 1226651904 1226717440 13 3066 35023 30 _ _ (1046377 / 50000) (2092757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226717440 :
    ThetaLowerSegment 1226717440 1226782976 (30666585212303 / 25000)
      (122672855607979 / 100000) := by
  exact
    packedTile65536 1226717440 1226782976 13 3113 35024 30 _ _ (2092759 / 100000) (1046381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226782976 :
    ThetaLowerSegment 1226782976 1226848512 (122672855607979 / 100000)
      (61339637059117 / 50000) := by
  exact
    packedTile65536 1226782976 1226848512 13 3067 35025 30 _ _ (418553 / 20000) (65399 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226848512 :
    ThetaLowerSegment 1226848512 1226914048 (61339637059117 / 50000) (61342889223697 / 50000) := by
  exact
    packedTile65536 1226848512 1226914048 13 3108 35026 30 _ _ (209277 / 10000) (2092773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226914048 :
    ThetaLowerSegment 1226914048 1226979584 (61342889223697 / 50000) (61346216735947 / 50000) := by
  exact
    packedTile65536 1226914048 1226979584 13 3180 35027 30 _ _ (83711 / 4000) (1046389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226979584 :
    ThetaLowerSegment 1226979584 1227045120 (61346216735947 / 50000) (24539813936089 / 20000) := by
  exact
    packedTile65536 1226979584 1227045120 13 3171 35028 30 _ _ (2092781 / 100000) (130799 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227045120 :
    ThetaLowerSegment 1227045120 1227110656 (24539813936089 / 20000)
      (122705674513061 / 100000) := by
  exact
    packedTile65536 1227045120 1227110656 13 3156 35029 30 _ _ (1046393 / 50000) (2092789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227110656 :
    ThetaLowerSegment 1227110656 1227176192 (122705674513061 / 100000)
      (30678068270771 / 25000) := by
  exact
    packedTile65536 1227110656 1227176192 13 3153 35030 30 _ _ (2092791 / 100000) (1046397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227176192 :
    ThetaLowerSegment 1227176192 1227241728 (30678068270771 / 25000) (61359382469689 / 50000) := by
  exact
    packedTile65536 1227176192 1227241728 13 3102 35031 30 _ _ (2092797 / 100000) (2616 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227241728 :
    ThetaLowerSegment 1227241728 1227307264 (61359382469689 / 50000) (15340670966211 / 12500) := by
  exact
    packedTile65536 1227241728 1227307264 13 3155 35032 30 _ _ (1046401 / 50000) (418561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227307264 :
    ThetaLowerSegment 1227307264 1227372800 (15340670966211 / 12500) (61365980035869 / 50000) := by
  exact
    packedTile65536 1227307264 1227372800 13 3150 35032 30 _ _ (2092807 / 100000) (209281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227372800 :
    ThetaLowerSegment 1227372800 1227438336 (61365980035869 / 50000)
      (122738420585469 / 100000) := by
  exact
    packedTile65536 1227372800 1227438336 13 3087 35033 30 _ _ (2092813 / 100000) (130801 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227438336 :
    ThetaLowerSegment 1227438336 1227503872 (122738420585469 / 100000)
      (122744994126807 / 100000) := by
  exact
    packedTile65536 1227438336 1227503872 13 3141 35034 30 _ _ (1046409 / 50000) (2092821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227503872 :
    ThetaLowerSegment 1227503872 1227569408 (122744994126807 / 100000)
      (15343950669333 / 12500) := by
  exact
    packedTile65536 1227503872 1227569408 13 3159 35035 30 _ _ (2092823 / 100000) (1046413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227569408 :
    ThetaLowerSegment 1227569408 1227634944 (15343950669333 / 12500)
      (122758065917787 / 100000) := by
  exact
    packedTile65536 1227569408 1227634944 13 3087 35036 30 _ _ (2092829 / 100000) (65401 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227634944 :
    ThetaLowerSegment 1227634944 1227700480 (122758065917787 / 100000)
      (122764593467033 / 100000) := by
  exact
    packedTile65536 1227634944 1227700480 13 3119 35037 30 _ _ (1046417 / 50000) (2092837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227700480 :
    ThetaLowerSegment 1227700480 1227766016 (122764593467033 / 100000)
      (61385581444327 / 50000) := by
  exact
    packedTile65536 1227700480 1227766016 13 3139 35038 30 _ _ (2092839 / 100000) (1046421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227766016 :
    ThetaLowerSegment 1227766016 1227831552 (61385581444327 / 50000)
      (122777656986689 / 100000) := by
  exact
    packedTile65536 1227766016 1227831552 13 3103 35039 30 _ _ (418569 / 20000) (130803 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227831552 :
    ThetaLowerSegment 1227831552 1227897088 (122777656986689 / 100000)
      (122784088314739 / 100000) := by
  exact
    packedTile65536 1227831552 1227897088 13 3073 35040 30 _ _ (41857 / 2000) (2092853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227897088 :
    ThetaLowerSegment 1227897088 1227962624 (122784088314739 / 100000)
      (122790726850799 / 100000) := by
  exact
    packedTile65536 1227897088 1227962624 13 3172 35041 30 _ _ (418571 / 20000) (1046429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1227962624 :
    ThetaLowerSegment 1227962624 1228028160 (122790726850799 / 100000)
      (61398606313519 / 50000) := by
  exact
    packedTile65536 1227962624 1228028160 13 3099 35042 30 _ _ (2092861 / 100000) (65402 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228028160 :
    ThetaLowerSegment 1228028160 1228093696 (61398606313519 / 50000) (6140192036683 / 5000) := by
  exact
    packedTile65536 1228028160 1228093696 13 3167 35043 30 _ _ (1046433 / 50000) (2092869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228093696 :
    ThetaLowerSegment 1228093696 1228159232 (6140192036683 / 5000) (7675647632481 / 6250) := by
  exact
    packedTile65536 1228093696 1228159232 13 3116 35044 30 _ _ (2092871 / 100000) (1046437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228159232 :
    ThetaLowerSegment 1228159232 1228224768 (7675647632481 / 6250) (122816881431551 / 100000) := by
  exact
    packedTile65536 1228159232 1228224768 13 3115 35045 30 _ _ (2092877 / 100000) (26161 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228224768 :
    ThetaLowerSegment 1228224768 1228290304 (122816881431551 / 100000)
      (122823402851863 / 100000) := by
  exact
    packedTile65536 1228224768 1228290304 13 3116 35046 30 _ _ (1046441 / 50000) (418577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228290304 :
    ThetaLowerSegment 1228290304 1228355840 (122823402851863 / 100000)
      (122829974517043 / 100000) := by
  exact
    packedTile65536 1228290304 1228355840 13 3140 35046 30 _ _ (2092887 / 100000) (209289 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228355840 :
    ThetaLowerSegment 1228355840 1228421376 (122829974517043 / 100000)
      (12283658596603 / 10000) := by
  exact
    packedTile65536 1228355840 1228421376 13 3159 35047 30 _ _ (2092893 / 100000) (65403 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228421376 :
    ThetaLowerSegment 1228421376 1228486912 (12283658596603 / 10000) (61421645805611 / 50000) := by
  exact
    packedTile65536 1228421376 1228486912 13 3204 35048 30 _ _ (1046449 / 50000) (2092901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228486912 :
    ThetaLowerSegment 1228486912 1228552448 (61421645805611 / 50000) (4913987082331 / 4000) := by
  exact
    packedTile65536 1228486912 1228552448 13 3051 35049 30 _ _ (2092903 / 100000) (1046453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228552448 :
    ThetaLowerSegment 1228552448 1228617984 (4913987082331 / 4000) (12285628018617 / 10000) := by
  exact
    packedTile65536 1228552448 1228617984 13 3155 35050 30 _ _ (2092909 / 100000) (130807 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228617984 :
    ThetaLowerSegment 1228617984 1228683520 (12285628018617 / 10000) (7678926022287 / 6250) := by
  exact
    packedTile65536 1228617984 1228683520 13 3123 35051 30 _ _ (1046457 / 50000) (2092917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228683520 :
    ThetaLowerSegment 1228683520 1228749056 (7678926022287 / 6250) (61434587322257 / 50000) := by
  exact
    packedTile65536 1228683520 1228749056 13 3038 35052 30 _ _ (2092919 / 100000) (1046461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228749056 :
    ThetaLowerSegment 1228749056 1228814592 (61434587322257 / 50000) (30718935560791 / 25000) := by
  exact
    packedTile65536 1228749056 1228814592 13 3138 35053 30 _ _ (83717 / 4000) (65404 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228814592 :
    ThetaLowerSegment 1228814592 1228880128 (30718935560791 / 25000) (30720557581541 / 25000) := by
  exact
    packedTile65536 1228814592 1228880128 13 3100 35054 30 _ _ (209293 / 10000) (2092933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228880128 :
    ThetaLowerSegment 1228880128 1228945664 (30720557581541 / 25000) (61444386420487 / 50000) := by
  exact
    packedTile65536 1228880128 1228945664 13 3126 35055 30 _ _ (418587 / 20000) (1046469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1228945664 :
    ThetaLowerSegment 1228945664 1229011200 (61444386420487 / 50000)
      (122895359326301 / 100000) := by
  exact
    packedTile65536 1228945664 1229011200 13 3147 35056 30 _ _ (2092941 / 100000) (130809 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229011200 :
    ThetaLowerSegment 1229011200 1229076736 (122895359326301 / 100000)
      (122901893503713 / 100000) := by
  exact
    packedTile65536 1229011200 1229076736 13 3122 35057 30 _ _ (1046473 / 50000) (2092949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229076736 :
    ThetaLowerSegment 1229076736 1229142272 (122901893503713 / 100000) (122908459091 / 100) := by
  exact
    packedTile65536 1229076736 1229142272 13 3137 35058 30 _ _ (2092951 / 100000) (1046477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229142272 :
    ThetaLowerSegment 1229142272 1229207808 (122908459091 / 100) (122914974466141 / 100000) := by
  exact
    packedTile65536 1229142272 1229207808 13 3113 35059 30 _ _ (2092957 / 100000) (13081 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229207808 :
    ThetaLowerSegment 1229207808 1229273344 (122914974466141 / 100000)
      (122921579854213 / 100000) := by
  exact
    packedTile65536 1229207808 1229273344 13 3156 35060 30 _ _ (1046481 / 50000) (418593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229273344 :
    ThetaLowerSegment 1229273344 1229338880 (122921579854213 / 100000)
      (61464079024747 / 50000) := by
  exact
    packedTile65536 1229273344 1229338880 13 3143 35060 30 _ _ (2092967 / 100000) (209297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229338880 :
    ThetaLowerSegment 1229338880 1229404416 (61464079024747 / 50000) (30733675170773 / 25000) := by
  exact
    packedTile65536 1229338880 1229404416 13 3126 35061 30 _ _ (2092973 / 100000) (130811 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229404416 :
    ThetaLowerSegment 1229404416 1229469952 (30733675170773 / 25000) (15367679485787 / 12500) := by
  exact
    packedTile65536 1229404416 1229469952 13 3218 35062 30 _ _ (1046489 / 50000) (2092981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229469952 :
    ThetaLowerSegment 1229469952 1229535488 (15367679485787 / 12500)
      (122948064363457 / 100000) := by
  exact
    packedTile65536 1229469952 1229535488 13 3167 35063 30 _ _ (2092983 / 100000) (1046493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229535488 :
    ThetaLowerSegment 1229535488 1229601024 (122948064363457 / 100000)
      (61477306663019 / 50000) := by
  exact
    packedTile65536 1229535488 1229601024 13 3129 35064 30 _ _ (2092989 / 100000) (65406 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229601024 :
    ThetaLowerSegment 1229601024 1229666560 (61477306663019 / 50000) (61480584291623 / 50000) := by
  exact
    packedTile65536 1229601024 1229666560 13 3132 35065 30 _ _ (1046497 / 50000) (2092997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229666560 :
    ThetaLowerSegment 1229666560 1229732096 (61480584291623 / 50000) (1229677531581 / 1000) := by
  exact
    packedTile65536 1229666560 1229732096 13 3146 35066 30 _ _ (2092999 / 100000) (1046501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229732096 :
    ThetaLowerSegment 1229732096 1229797632 (1229677531581 / 1000) (6148719189897 / 5000) := by
  exact
    packedTile65536 1229732096 1229797632 13 3168 35067 30 _ _ (418601 / 20000) (130813 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229797632 :
    ThetaLowerSegment 1229797632 1229863168 (6148719189897 / 5000) (12298074026931 / 10000) := by
  exact
    packedTile65536 1229797632 1229863168 13 3037 35068 30 _ _ (209301 / 10000) (2093013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229863168 :
    ThetaLowerSegment 1229863168 1229928704 (12298074026931 / 10000) (4919493414383 / 4000) := by
  exact
    packedTile65536 1229863168 1229928704 13 3151 35069 30 _ _ (418603 / 20000) (1046509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229928704 :
    ThetaLowerSegment 1229928704 1229994240 (4919493414383 / 4000) (61496910815827 / 50000) := by
  exact
    packedTile65536 1229928704 1229994240 13 3099 35070 30 _ _ (2093021 / 100000) (65407 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229994240 :
    ThetaLowerSegment 1229994240 1230059776 (61496910815827 / 50000) (3075013035197 / 2500) := by
  exact
    packedTile65536 1229994240 1230059776 13 3201 35071 30 _ _ (1046513 / 50000) (2093029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230059776 :
    ThetaLowerSegment 1230059776 1230125312 (3075013035197 / 2500) (123007070501879 / 100000) := by
  exact
    packedTile65536 1230059776 1230125312 13 3129 35072 30 _ _ (2093031 / 100000) (1046517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230125312 :
    ThetaLowerSegment 1230125312 1230190848 (123007070501879 / 100000)
      (61506862133251 / 50000) := by
  exact
    packedTile65536 1230125312 1230190848 13 3179 35073 30 _ _ (2093037 / 100000) (26163 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230190848 :
    ThetaLowerSegment 1230190848 1230256384 (61506862133251 / 50000) (30755061023083 / 25000) := by
  exact
    packedTile65536 1230190848 1230256384 13 3115 35074 30 _ _ (1046521 / 50000) (418609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230256384 :
    ThetaLowerSegment 1230256384 1230321920 (30755061023083 / 25000) (24605379577749 / 20000) := by
  exact
    packedTile65536 1230256384 1230321920 13 3179 35075 30 _ _ (2093047 / 100000) (41861 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230321920 :
    ThetaLowerSegment 1230321920 1230387456 (24605379577749 / 20000) (24606706573351 / 20000) := by
  exact
    packedTile65536 1230321920 1230387456 13 3170 35075 30 _ _ (2093053 / 100000) (65408 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230387456 :
    ThetaLowerSegment 1230387456 1230452992 (24606706573351 / 20000)
      (123040163674499 / 100000) := by
  exact
    packedTile65536 1230387456 1230452992 13 3168 35076 30 _ _ (1046529 / 50000) (2093061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230452992 :
    ThetaLowerSegment 1230452992 1230518528 (123040163674499 / 100000)
      (123046798684209 / 100000) := by
  exact
    packedTile65536 1230452992 1230518528 13 3170 35077 30 _ _ (2093063 / 100000) (1046533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230518528 :
    ThetaLowerSegment 1230518528 1230584064 (123046798684209 / 100000)
      (61526711623797 / 50000) := by
  exact
    packedTile65536 1230518528 1230584064 13 3165 35078 30 _ _ (2093069 / 100000) (130817 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230584064 :
    ThetaLowerSegment 1230584064 1230649600 (61526711623797 / 50000) (15382477198583 / 12500) := by
  exact
    packedTile65536 1230584064 1230649600 13 3055 35079 30 _ _ (1046537 / 50000) (2093077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230649600 :
    ThetaLowerSegment 1230649600 1230715136 (15382477198583 / 12500)
      (123066375205171 / 100000) := by
  exact
    packedTile65536 1230649600 1230715136 13 3133 35080 30 _ _ (2093079 / 100000) (1046541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230715136 :
    ThetaLowerSegment 1230715136 1230780672 (123066375205171 / 100000)
      (61536472699493 / 50000) := by
  exact
    packedTile65536 1230715136 1230780672 13 3139 35081 30 _ _ (418617 / 20000) (65409 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230780672 :
    ThetaLowerSegment 1230780672 1230846208 (61536472699493 / 50000) (30769875762489 / 25000) := by
  exact
    packedTile65536 1230780672 1230846208 13 3133 35082 30 _ _ (209309 / 10000) (2093093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230846208 :
    ThetaLowerSegment 1230846208 1230911744 (30769875762489 / 25000) (61543014660083 / 50000) := by
  exact
    packedTile65536 1230846208 1230911744 13 3118 35083 30 _ _ (418619 / 20000) (1046549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230911744 :
    ThetaLowerSegment 1230911744 1230977280 (61543014660083 / 50000)
      (123092553515983 / 100000) := by
  exact
    packedTile65536 1230911744 1230977280 13 3117 35084 30 _ _ (2093101 / 100000) (130819 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1230977280 :
    ThetaLowerSegment 1230977280 1231042816 (123092553515983 / 100000)
      (123099217965487 / 100000) := by
  exact
    packedTile65536 1230977280 1231042816 13 3184 35085 30 _ _ (1046553 / 50000) (2093109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231042816 :
    ThetaLowerSegment 1231042816 1231108352 (123099217965487 / 100000)
      (123105735913141 / 100000) := by
  exact
    packedTile65536 1231042816 1231108352 13 3114 35086 30 _ _ (2093111 / 100000) (1046557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231108352 :
    ThetaLowerSegment 1231108352 1231173888 (123105735913141 / 100000)
      (123112366907797 / 100000) := by
  exact
    packedTile65536 1231108352 1231173888 13 3168 35087 30 _ _ (2093117 / 100000) (13082 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231173888 :
    ThetaLowerSegment 1231173888 1231239424 (123112366907797 / 100000)
      (123118956055853 / 100000) := by
  exact
    packedTile65536 1231173888 1231239424 13 3148 35088 30 _ _ (1046561 / 50000) (3349 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231239424 :
    ThetaLowerSegment 1231239424 1231304960 (123118956055853 / 100000)
      (123125599640951 / 100000) := by
  exact
    packedTile65536 1231239424 1231304960 13 3174 35089 30 _ _ (2093127 / 100000) (209313 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231304960 :
    ThetaLowerSegment 1231304960 1231370496 (123125599640951 / 100000)
      (61566118482847 / 50000) := by
  exact
    packedTile65536 1231304960 1231370496 13 3171 35089 30 _ _ (2093133 / 100000) (130821 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231370496 :
    ThetaLowerSegment 1231370496 1231436032 (61566118482847 / 50000) (61569381684989 / 50000) := by
  exact
    packedTile65536 1231370496 1231436032 13 3118 35090 30 _ _ (1046569 / 50000) (2093141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231436032 :
    ThetaLowerSegment 1231436032 1231501568 (61569381684989 / 50000) (30786343378893 / 25000) := by
  exact
    packedTile65536 1231436032 1231501568 13 3158 35091 30 _ _ (2093143 / 100000) (1046573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231501568 :
    ThetaLowerSegment 1231501568 1231567104 (30786343378893 / 25000)
      (123151868556919 / 100000) := by
  exact
    packedTile65536 1231501568 1231567104 13 3103 35092 30 _ _ (2093149 / 100000) (65411 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231567104 :
    ThetaLowerSegment 1231567104 1231632640 (123151868556919 / 100000)
      (24631664768771 / 20000) := by
  exact
    packedTile65536 1231567104 1231632640 13 3084 35093 30 _ _ (1046577 / 50000) (2093157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231632640 :
    ThetaLowerSegment 1231632640 1231698176 (24631664768771 / 20000) (30791206822217 / 25000) := by
  exact
    packedTile65536 1231632640 1231698176 13 3107 35094 30 _ _ (2093159 / 100000) (1046581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231698176 :
    ThetaLowerSegment 1231698176 1231763712 (30791206822217 / 25000) (3849107356488 / 3125) := by
  exact
    packedTile65536 1231698176 1231763712 13 3157 35095 30 _ _ (523291 / 25000) (2093167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231763712 :
    ThetaLowerSegment 1231763712 1231829248 (3849107356488 / 3125) (61588973629743 / 50000) := by
  exact
    packedTile65536 1231763712 1231829248 13 3111 35096 30 _ _ (209317 / 10000) (2093173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231829248 :
    ThetaLowerSegment 1231829248 1231894784 (61588973629743 / 50000) (15398057129217 / 12500) := by
  exact
    packedTile65536 1231829248 1231894784 13 3110 35097 30 _ _ (83727 / 4000) (1046589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231894784 :
    ThetaLowerSegment 1231894784 1231960320 (15398057129217 / 12500) (15398886028497 / 12500) := by
  exact
    packedTile65536 1231894784 1231960320 13 3168 35098 30 _ _ (104659 / 5000) (2093183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1231960320 :
    ThetaLowerSegment 1231960320 1232025856 (15398886028497 / 12500) (61598841928531 / 50000) := by
  exact
    packedTile65536 1231960320 1232025856 13 3151 35099 30 _ _ (1046593 / 50000) (2093189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232025856 :
    ThetaLowerSegment 1232025856 1232091392 (61598841928531 / 50000) (4928166323873 / 4000) := by
  exact
    packedTile65536 1232025856 1232091392 13 3093 35100 30 _ _ (2093191 / 100000) (1046597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232091392 :
    ThetaLowerSegment 1232091392 1232156928 (4928166323873 / 4000) (123210577928957 / 100000) := by
  exact
    packedTile65536 1232091392 1232156928 13 3067 35101 30 _ _ (523299 / 25000) (2093199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232156928 :
    ThetaLowerSegment 1232156928 1232222464 (123210577928957 / 100000)
      (123217119185207 / 100000) := by
  exact
    packedTile65536 1232156928 1232222464 13 3125 35102 30 _ _ (1046601 / 50000) (418641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232222464 :
    ThetaLowerSegment 1232222464 1232288000 (123217119185207 / 100000)
      (61611838601369 / 50000) := by
  exact
    packedTile65536 1232222464 1232288000 13 3133 35103 30 _ _ (2093207 / 100000) (209321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232288000 :
    ThetaLowerSegment 1232288000 1232353536 (61611838601369 / 50000) (12323028337981 / 10000) := by
  exact
    packedTile65536 1232288000 1232353536 13 3156 35103 30 _ _ (523303 / 25000) (418643 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232353536 :
    ThetaLowerSegment 1232353536 1232419072 (12323028337981 / 10000) (61618369432061 / 50000) := by
  exact
    packedTile65536 1232353536 1232419072 13 3084 35104 30 _ _ (1046609 / 50000) (2093221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232419072 :
    ThetaLowerSegment 1232419072 1232484608 (61618369432061 / 50000) (61621680910847 / 50000) := by
  exact
    packedTile65536 1232419072 1232484608 13 3164 35105 30 _ _ (2093223 / 100000) (1046613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232484608 :
    ThetaLowerSegment 1232484608 1232550144 (61621680910847 / 50000) (61624887736143 / 50000) := by
  exact
    packedTile65536 1232484608 1232550144 13 3064 35106 30 _ _ (523307 / 25000) (2093231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232550144 :
    ThetaLowerSegment 1232550144 1232615680 (61624887736143 / 50000) (30814065601113 / 25000) := by
  exact
    packedTile65536 1232550144 1232615680 13 3099 35107 30 _ _ (1046617 / 50000) (2093237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232615680 :
    ThetaLowerSegment 1232615680 1232681216 (30814065601113 / 25000) (4930514830399 / 4000) := by
  exact
    packedTile65536 1232615680 1232681216 13 3157 35108 30 _ _ (2093239 / 100000) (1046621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232681216 :
    ThetaLowerSegment 1232681216 1232746752 (4930514830399 / 4000) (123269368189351 / 100000) := by
  exact
    packedTile65536 1232681216 1232746752 13 3104 35109 30 _ _ (523311 / 25000) (2093247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232746752 :
    ThetaLowerSegment 1232746752 1232812288 (123269368189351 / 100000)
      (123275897036101 / 100000) := by
  exact
    packedTile65536 1232746752 1232812288 13 3119 35110 30 _ _ (8373 / 400) (2093253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232812288 :
    ThetaLowerSegment 1232812288 1232877824 (123275897036101 / 100000)
      (123282365194051 / 100000) := by
  exact
    packedTile65536 1232812288 1232877824 13 3090 35111 30 _ _ (418651 / 20000) (1046629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232877824 :
    ThetaLowerSegment 1232877824 1232943360 (123282365194051 / 100000)
      (123289002921511 / 100000) := by
  exact
    packedTile65536 1232877824 1232943360 13 3171 35112 30 _ _ (104663 / 5000) (2093263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1232943360 :
    ThetaLowerSegment 1232943360 1233008896 (123289002921511 / 100000)
      (123295508792239 / 100000) := by
  exact
    packedTile65536 1232943360 1233008896 13 3108 35113 30 _ _ (1046633 / 50000) (2093269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233008896 :
    ThetaLowerSegment 1233008896 1233074432 (123295508792239 / 100000)
      (123301935134209 / 100000) := by
  exact
    packedTile65536 1233008896 1233074432 13 3070 35114 30 _ _ (2093271 / 100000) (1046637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233074432 :
    ThetaLowerSegment 1233074432 1233139968 (123301935134209 / 100000)
      (123308591751889 / 100000) := by
  exact
    packedTile65536 1233074432 1233139968 13 3180 35115 30 _ _ (523319 / 25000) (2093279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233139968 :
    ThetaLowerSegment 1233139968 1233205504 (123308591751889 / 100000)
      (123315126975171 / 100000) := by
  exact
    packedTile65536 1233139968 1233205504 13 3122 35116 30 _ _ (2093281 / 100000) (523321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233205504 :
    ThetaLowerSegment 1233205504 1233271040 (123315126975171 / 100000)
      (123321666403759 / 100000) := by
  exact
    packedTile65536 1233205504 1233271040 13 3124 35117 30 _ _ (2093287 / 100000) (209329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233271040 :
    ThetaLowerSegment 1233271040 1233336576 (123321666403759 / 100000)
      (123328207941259 / 100000) := by
  exact
    packedTile65536 1233271040 1233336576 13 3125 35117 30 _ _ (523323 / 25000) (418659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233336576 :
    ThetaLowerSegment 1233336576 1233402112 (123328207941259 / 100000)
      (61667448012587 / 50000) := by
  exact
    packedTile65536 1233336576 1233402112 13 3195 35118 30 _ _ (2093297 / 100000) (20933 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233402112 :
    ThetaLowerSegment 1233402112 1233467648 (61667448012587 / 50000) (2466827370361 / 2000) := by
  exact
    packedTile65536 1233402112 1233467648 13 3092 35119 30 _ _ (2093303 / 100000) (1046653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233467648 :
    ThetaLowerSegment 1233467648 1233533184 (2466827370361 / 2000) (61673971799239 / 50000) := by
  exact
    packedTile65536 1233467648 1233533184 13 3141 35120 30 _ _ (523327 / 25000) (2093311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233533184 :
    ThetaLowerSegment 1233533184 1233598720 (61673971799239 / 50000) (2467090499491 / 2000) := by
  exact
    packedTile65536 1233533184 1233598720 13 3144 35121 30 _ _ (2093313 / 100000) (523329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233598720 :
    ThetaLowerSegment 1233598720 1233664256 (2467090499491 / 2000) (24672221692561 / 20000) := by
  exact
    packedTile65536 1233598720 1233664256 13 3145 35122 30 _ _ (2093319 / 100000) (1046661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233664256 :
    ThetaLowerSegment 1233664256 1233729792 (24672221692561 / 20000)
      (123367585207261 / 100000) := by
  exact
    packedTile65536 1233664256 1233729792 13 3094 35123 30 _ _ (523331 / 25000) (2093327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233729792 :
    ThetaLowerSegment 1233729792 1233795328 (123367585207261 / 100000)
      (123374116393741 / 100000) := by
  exact
    packedTile65536 1233729792 1233795328 13 3120 35124 30 _ _ (2093329 / 100000) (523333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233795328 :
    ThetaLowerSegment 1233795328 1233860864 (123374116393741 / 100000)
      (123380618292251 / 100000) := by
  exact
    packedTile65536 1233795328 1233860864 13 3106 35125 30 _ _ (418667 / 20000) (1046669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233860864 :
    ThetaLowerSegment 1233860864 1233926400 (123380618292251 / 100000)
      (123387193473191 / 100000) := by
  exact
    packedTile65536 1233860864 1233926400 13 3141 35126 30 _ _ (104667 / 5000) (2093343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233926400 :
    ThetaLowerSegment 1233926400 1233991936 (123387193473191 / 100000)
      (123393699589451 / 100000) := by
  exact
    packedTile65536 1233926400 1233991936 13 3108 35127 30 _ _ (418669 / 20000) (523337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233991936 :
    ThetaLowerSegment 1233991936 1234057472 (123393699589451 / 100000)
      (123400235031273 / 100000) := by
  exact
    packedTile65536 1233991936 1234057472 13 3122 35128 30 _ _ (2093351 / 100000) (1046677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234057472 :
    ThetaLowerSegment 1234057472 1234123008 (123400235031273 / 100000)
      (123406839569453 / 100000) := by
  exact
    packedTile65536 1234057472 1234123008 13 3155 35129 30 _ _ (523339 / 25000) (2093359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234123008 :
    ThetaLowerSegment 1234123008 1234188544 (123406839569453 / 100000)
      (24682675008499 / 20000) := by
  exact
    packedTile65536 1234123008 1234188544 13 3122 35130 30 _ _ (2093361 / 100000) (523341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234188544 :
    ThetaLowerSegment 1234188544 1234254080 (24682675008499 / 20000)
      (123419967052029 / 100000) := by
  exact
    packedTile65536 1234188544 1234254080 13 3149 35131 30 _ _ (1046683 / 50000) (2093369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234254080 :
    ThetaLowerSegment 1234254080 1234319616 (123419967052029 / 100000)
      (123426489999181 / 100000) := by
  exact
    packedTile65536 1234254080 1234319616 13 3116 35131 30 _ _ (523343 / 25000) (16747 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234319616 :
    ThetaLowerSegment 1234319616 1234385152 (123426489999181 / 100000)
      (12343301505529 / 10000) := by
  exact
    packedTile65536 1234319616 1234385152 13 3117 35132 30 _ _ (2093377 / 100000) (104669 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234385152 :
    ThetaLowerSegment 1234385152 1234450688 (12343301505529 / 10000) (61719748082981 / 50000) := by
  exact
    packedTile65536 1234385152 1234450688 13 3096 35133 30 _ _ (1046691 / 50000) (418677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234450688 :
    ThetaLowerSegment 1234450688 1234516224 (61719748082981 / 50000) (61723017955037 / 50000) := by
  exact
    packedTile65536 1234450688 1234516224 13 3124 35134 30 _ _ (523347 / 25000) (2093391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234516224 :
    ThetaLowerSegment 1234516224 1234581760 (61723017955037 / 50000)
      (123452632191417 / 100000) := by
  exact
    packedTile65536 1234516224 1234581760 13 3151 35135 30 _ _ (2093393 / 100000) (523349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234581760 :
    ThetaLowerSegment 1234581760 1234647296 (123452632191417 / 100000)
      (123459178246963 / 100000) := by
  exact
    packedTile65536 1234581760 1234647296 13 3127 35136 30 _ _ (1046699 / 50000) (2093401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234647296 :
    ThetaLowerSegment 1234647296 1234712832 (123459178246963 / 100000)
      (123465814337643 / 100000) := by
  exact
    packedTile65536 1234647296 1234712832 13 3170 35137 30 _ _ (523351 / 25000) (2093407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234712832 :
    ThetaLowerSegment 1234712832 1234778368 (123465814337643 / 100000)
      (61736192774247 / 50000) := by
  exact
    packedTile65536 1234712832 1234778368 13 3139 35138 30 _ _ (2093409 / 100000) (523353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234778368 :
    ThetaLowerSegment 1234778368 1234843904 (61736192774247 / 50000) (61739445939603 / 50000) := by
  exact
    packedTile65536 1234778368 1234843904 13 3108 35139 30 _ _ (1046707 / 50000) (2093417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234843904 :
    ThetaLowerSegment 1234843904 1234909440 (61739445939603 / 50000) (61742766103723 / 50000) := by
  exact
    packedTile65536 1234843904 1234909440 13 3172 35140 30 _ _ (104671 / 5000) (2093423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234909440 :
    ThetaLowerSegment 1234909440 1234974976 (61742766103723 / 50000)
      (123492019731521 / 100000) := by
  exact
    packedTile65536 1234909440 1234974976 13 3099 35141 30 _ _ (83737 / 4000) (523357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1234974976 :
    ThetaLowerSegment 1234974976 1235040512 (123492019731521 / 100000)
      (123498559606841 / 100000) := by
  exact
    packedTile65536 1234974976 1235040512 13 3124 35142 30 _ _ (209343 / 10000) (2093433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235040512 :
    ThetaLowerSegment 1235040512 1235106048 (123498559606841 / 100000)
      (123505204169531 / 100000) := by
  exact
    packedTile65536 1235040512 1235106048 13 3174 35143 30 _ _ (418687 / 20000) (1046719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235106048 :
    ThetaLowerSegment 1235106048 1235171584 (123505204169531 / 100000)
      (123511840377501 / 100000) := by
  exact
    packedTile65536 1235106048 1235171584 13 3170 35144 30 _ _ (2093441 / 100000) (523361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235171584 :
    ThetaLowerSegment 1235171584 1235237120 (123511840377501 / 100000)
      (123518355181453 / 100000) := by
  exact
    packedTile65536 1235171584 1235237120 13 3112 35145 30 _ _ (1046723 / 50000) (2093449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235237120 :
    ThetaLowerSegment 1235237120 1235302656 (123518355181453 / 100000)
      (123524899309279 / 100000) := by
  exact
    packedTile65536 1235237120 1235302656 13 3126 35145 30 _ _ (2093451 / 100000) (1046727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235302656 :
    ThetaLowerSegment 1235302656 1235368192 (123524899309279 / 100000)
      (123531430895119 / 100000) := by
  exact
    packedTile65536 1235302656 1235368192 13 3120 35146 30 _ _ (2093457 / 100000) (104673 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235368192 :
    ThetaLowerSegment 1235368192 1235433728 (123531430895119 / 100000)
      (123537987618103 / 100000) := by
  exact
    packedTile65536 1235368192 1235433728 13 3132 35147 30 _ _ (1046731 / 50000) (418693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235433728 :
    ThetaLowerSegment 1235433728 1235499264 (123537987618103 / 100000)
      (30886087416079 / 25000) := by
  exact
    packedTile65536 1235433728 1235499264 13 3039 35148 30 _ _ (2093467 / 100000) (209347 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235499264 :
    ThetaLowerSegment 1235499264 1235564800 (30886087416079 / 25000)
      (123550983880253 / 100000) := by
  exact
    packedTile65536 1235499264 1235564800 13 3169 35149 30 _ _ (2093473 / 100000) (523369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235564800 :
    ThetaLowerSegment 1235564800 1235630336 (123550983880253 / 100000)
      (123557676729419 / 100000) := by
  exact
    packedTile65536 1235564800 1235630336 13 3197 35150 30 _ _ (1046739 / 50000) (2093481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235630336 :
    ThetaLowerSegment 1235630336 1235695872 (123557676729419 / 100000)
      (123564204209413 / 100000) := by
  exact
    packedTile65536 1235630336 1235695872 13 3118 35151 30 _ _ (2093483 / 100000) (1046743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235695872 :
    ThetaLowerSegment 1235695872 1235761408 (123564204209413 / 100000)
      (123570744269049 / 100000) := by
  exact
    packedTile65536 1235695872 1235761408 13 3124 35152 30 _ _ (2093489 / 100000) (523373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235761408 :
    ThetaLowerSegment 1235761408 1235826944 (123570744269049 / 100000)
      (24715450588379 / 20000) := by
  exact
    packedTile65536 1235761408 1235826944 13 3109 35153 30 _ _ (1046747 / 50000) (2093497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235826944 :
    ThetaLowerSegment 1235826944 1235892480 (24715450588379 / 20000) (61791885002141 / 50000) := by
  exact
    packedTile65536 1235826944 1235892480 13 3113 35154 30 _ _ (2093499 / 100000) (1046751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235892480 :
    ThetaLowerSegment 1235892480 1235958016 (61791885002141 / 50000) (61795185411197 / 50000) := by
  exact
    packedTile65536 1235892480 1235958016 13 3153 35155 30 _ _ (65422 / 3125) (2093507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235958016 :
    ThetaLowerSegment 1235958016 1236023552 (61795185411197 / 50000) (61798528746667 / 50000) := by
  exact
    packedTile65536 1235958016 1236023552 13 3194 35156 30 _ _ (209351 / 10000) (2093513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236023552 :
    ThetaLowerSegment 1236023552 1236089088 (61798528746667 / 50000) (30900881613671 / 25000) := by
  exact
    packedTile65536 1236023552 1236089088 13 3090 35157 30 _ _ (418703 / 20000) (1046759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236089088 :
    ThetaLowerSegment 1236089088 1236154624 (30900881613671 / 25000) (30902543345171 / 25000) := by
  exact
    packedTile65536 1236089088 1236154624 13 3175 35158 30 _ _ (26169 / 1250) (2093523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236154624 :
    ThetaLowerSegment 1236154624 1236220160 (30902543345171 / 25000) (6180836933911 / 5000) := by
  exact
    packedTile65536 1236154624 1236220160 13 3136 35158 30 _ _ (1046763 / 50000) (2093529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236220160 :
    ThetaLowerSegment 1236220160 1236285696 (6180836933911 / 5000) (6181167711809 / 5000) := by
  exact
    packedTile65536 1236220160 1236285696 13 3160 35159 30 _ _ (2093531 / 100000) (1046767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236285696 :
    ThetaLowerSegment 1236285696 1236351232 (6181167711809 / 5000) (30907456862373 / 25000) := by
  exact
    packedTile65536 1236285696 1236351232 13 3092 35160 30 _ _ (65423 / 3125) (2093539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236351232 :
    ThetaLowerSegment 1236351232 1236416768 (30907456862373 / 25000) (15454550669807 / 12500) := by
  exact
    packedTile65536 1236351232 1236416768 13 3142 35161 30 _ _ (1046771 / 50000) (418709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236416768 :
    ThetaLowerSegment 1236416768 1236482304 (15454550669807 / 12500) (61821433022249 / 50000) := by
  exact
    packedTile65536 1236416768 1236482304 13 3086 35162 30 _ _ (2093547 / 100000) (41871 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236482304 :
    ThetaLowerSegment 1236482304 1236547840 (61821433022249 / 50000) (61824738740857 / 50000) := by
  exact
    packedTile65536 1236482304 1236547840 13 3158 35163 30 _ _ (130847 / 6250) (418711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236547840 :
    ThetaLowerSegment 1236547840 1236613376 (61824738740857 / 50000)
      (123656145460759 / 100000) := by
  exact
    packedTile65536 1236547840 1236613376 13 3185 35164 30 _ _ (2093557 / 100000) (52339 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236613376 :
    ThetaLowerSegment 1236613376 1236678912 (123656145460759 / 100000)
      (30915719066451 / 25000) := by
  exact
    packedTile65536 1236613376 1236678912 13 3215 35165 30 _ _ (2093563 / 100000) (1046783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236678912 :
    ThetaLowerSegment 1236678912 1236744448 (30915719066451 / 25000) (30917355189843 / 25000) := by
  exact
    packedTile65536 1236678912 1236744448 13 3126 35166 30 _ _ (65424 / 3125) (2093571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236744448 :
    ThetaLowerSegment 1236744448 1236809984 (30917355189843 / 25000) (6183790935923 / 5000) := by
  exact
    packedTile65536 1236744448 1236809984 13 3056 35167 30 _ _ (2093573 / 100000) (261697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236809984 :
    ThetaLowerSegment 1236809984 1236875520 (6183790935923 / 5000) (4947299470703 / 4000) := by
  exact
    packedTile65536 1236809984 1236875520 13 3185 35168 30 _ _ (2093579 / 100000) (1046791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236875520 :
    ThetaLowerSegment 1236875520 1236941056 (4947299470703 / 4000) (24737776533339 / 20000) := by
  exact
    packedTile65536 1236875520 1236941056 13 3055 35169 30 _ _ (130849 / 6250) (2093587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1236941056 :
    ThetaLowerSegment 1236941056 1237006592 (24737776533339 / 20000)
      (123695339295171 / 100000) := by
  exact
    packedTile65536 1236941056 1237006592 13 3084 35170 30 _ _ (2093589 / 100000) (261699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237006592 :
    ThetaLowerSegment 1237006592 1237072128 (123695339295171 / 100000)
      (123701946680991 / 100000) := by
  exact
    packedTile65536 1237006592 1237072128 13 3156 35171 30 _ _ (418719 / 20000) (1046799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237072128 :
    ThetaLowerSegment 1237072128 1237137664 (123701946680991 / 100000)
      (123708499648991 / 100000) := by
  exact
    packedTile65536 1237072128 1237137664 13 3130 35172 30 _ _ (2617 / 125) (2093603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237137664 :
    ThetaLowerSegment 1237137664 1237203200 (123708499648991 / 100000)
      (123715140564051 / 100000) := by
  exact
    packedTile65536 1237137664 1237203200 13 3172 35172 30 _ _ (418721 / 20000) (261701 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237203200 :
    ThetaLowerSegment 1237203200 1237268736 (123715140564051 / 100000)
      (123721695656961 / 100000) := by
  exact
    packedTile65536 1237203200 1237268736 13 3131 35173 30 _ _ (209361 / 10000) (2093613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237268736 :
    ThetaLowerSegment 1237268736 1237334272 (123721695656961 / 100000)
      (123728223551649 / 100000) := by
  exact
    packedTile65536 1237268736 1237334272 13 3118 35174 30 _ _ (130851 / 6250) (2093619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237334272 :
    ThetaLowerSegment 1237334272 1237399808 (123728223551649 / 100000)
      (15466843147633 / 12500) := by
  exact
    packedTile65536 1237334272 1237399808 13 3115 35175 30 _ _ (2093621 / 100000) (261703 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237399808 :
    ThetaLowerSegment 1237399808 1237465344 (15466843147633 / 12500) (30935347587497 / 25000) := by
  exact
    packedTile65536 1237399808 1237465344 13 3174 35176 30 _ _ (1046813 / 50000) (2093629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237465344 :
    ThetaLowerSegment 1237465344 1237530880 (30935347587497 / 25000) (30937005220633 / 25000) := by
  exact
    packedTile65536 1237465344 1237530880 13 3167 35177 30 _ _ (65426 / 3125) (418727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237530880 :
    ThetaLowerSegment 1237530880 1237596416 (30937005220633 / 25000)
      (123754580247253 / 100000) := by
  exact
    packedTile65536 1237530880 1237596416 13 3133 35178 30 _ _ (2093637 / 100000) (52341 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237596416 :
    ThetaLowerSegment 1237596416 1237661952 (123754580247253 / 100000)
      (24752243837207 / 20000) := by
  exact
    packedTile65536 1237596416 1237661952 13 3171 35179 30 _ _ (1046821 / 50000) (418729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237661952 :
    ThetaLowerSegment 1237661952 1237727488 (24752243837207 / 20000) (30941916381287 / 25000) := by
  exact
    packedTile65536 1237661952 1237727488 13 3079 35180 30 _ _ (2093647 / 100000) (41873 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237727488 :
    ThetaLowerSegment 1237727488 1237793024 (30941916381287 / 25000) (15471777855793 / 12500) := by
  exact
    packedTile65536 1237727488 1237793024 13 3132 35181 30 _ _ (2093653 / 100000) (261707 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237793024 :
    ThetaLowerSegment 1237793024 1237858560 (15471777855793 / 12500) (61890441386221 / 50000) := by
  exact
    packedTile65536 1237793024 1237858560 13 3181 35182 30 _ _ (1046829 / 50000) (2093661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237858560 :
    ThetaLowerSegment 1237858560 1237924096 (61890441386221 / 50000) (61893715875153 / 50000) := by
  exact
    packedTile65536 1237858560 1237924096 13 3128 35183 30 _ _ (2093663 / 100000) (1046833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237924096 :
    ThetaLowerSegment 1237924096 1237989632 (61893715875153 / 50000) (61896889877357 / 50000) := by
  exact
    packedTile65536 1237924096 1237989632 13 3032 35184 30 _ _ (2093669 / 100000) (261709 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237989632 :
    ThetaLowerSegment 1237989632 1238055168 (61896889877357 / 50000) (1238004564811 / 1000) := by
  exact
    packedTile65536 1237989632 1238055168 13 3189 35185 30 _ _ (1046837 / 50000) (2093677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238055168 :
    ThetaLowerSegment 1238055168 1238120704 (1238004564811 / 1000) (123806919668173 / 100000) := by
  exact
    packedTile65536 1238055168 1238120704 13 3087 35186 30 _ _ (2093679 / 100000) (1046841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238120704 :
    ThetaLowerSegment 1238120704 1238186240 (123806919668173 / 100000)
      (123813560836993 / 100000) := by
  exact
    packedTile65536 1238120704 1238186240 13 3172 35186 30 _ _ (418737 / 20000) (261711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238186240 :
    ThetaLowerSegment 1238186240 1238251776 (123813560836993 / 100000)
      (123820212490123 / 100000) := by
  exact
    packedTile65536 1238186240 1238251776 13 3177 35187 30 _ _ (209369 / 10000) (2093693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238251776 :
    ThetaLowerSegment 1238251776 1238317312 (123820212490123 / 100000)
      (61913394393059 / 50000) := by
  exact
    packedTile65536 1238251776 1238317312 13 3141 35188 30 _ _ (418739 / 20000) (1046849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238317312 :
    ThetaLowerSegment 1238317312 1238382848 (61913394393059 / 50000) (61916641721759 / 50000) := by
  exact
    packedTile65536 1238317312 1238382848 13 3102 35189 30 _ _ (20937 / 1000) (2093703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238382848 :
    ThetaLowerSegment 1238382848 1238448384 (61916641721759 / 50000) (15479966768963 / 12500) := by
  exact
    packedTile65536 1238382848 1238448384 13 3081 35190 30 _ _ (1046853 / 50000) (2093709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238448384 :
    ThetaLowerSegment 1238448384 1238513920 (15479966768963 / 12500) (3870198446202 / 3125) := by
  exact
    packedTile65536 1238448384 1238513920 13 3160 35191 30 _ _ (2093711 / 100000) (1046857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238513920 :
    ThetaLowerSegment 1238513920 1238579456 (3870198446202 / 3125) (6192640050873 / 5000) := by
  exact
    packedTile65536 1238513920 1238579456 13 3081 35192 30 _ _ (523429 / 25000) (2093719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238579456 :
    ThetaLowerSegment 1238579456 1238644992 (6192640050873 / 5000) (61929602856529 / 50000) := by
  exact
    packedTile65536 1238579456 1238644992 13 3059 35193 30 _ _ (1046861 / 50000) (83749 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238644992 :
    ThetaLowerSegment 1238644992 1238710528 (61929602856529 / 50000)
      (123865786297019 / 100000) := by
  exact
    packedTile65536 1238644992 1238710528 13 3143 35194 30 _ _ (2093727 / 100000) (209373 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238710528 :
    ThetaLowerSegment 1238710528 1238776064 (123865786297019 / 100000)
      (123872358521767 / 100000) := by
  exact
    packedTile65536 1238710528 1238776064 13 3139 35195 30 _ _ (523433 / 25000) (418747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238776064 :
    ThetaLowerSegment 1238776064 1238841600 (123872358521767 / 100000)
      (61939503068371 / 50000) := by
  exact
    packedTile65536 1238776064 1238841600 13 3175 35196 30 _ _ (2093737 / 100000) (104687 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238841600 :
    ThetaLowerSegment 1238841600 1238907136 (61939503068371 / 50000) (61942714870133 / 50000) := by
  exact
    packedTile65536 1238841600 1238907136 13 3068 35197 30 _ _ (2093743 / 100000) (1046873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238907136 :
    ThetaLowerSegment 1238907136 1238972672 (61942714870133 / 50000) (12389191617157 / 10000) := by
  exact
    packedTile65536 1238907136 1238972672 13 3098 35198 30 _ _ (523437 / 25000) (2093751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1238972672 :
    ThetaLowerSegment 1238972672 1239038208 (12389191617157 / 10000)
      (123898526149791 / 100000) := by
  exact
    packedTile65536 1238972672 1239038208 13 3157 35199 30 _ _ (2093753 / 100000) (523439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239038208 :
    ThetaLowerSegment 1239038208 1239103744 (123898526149791 / 100000)
      (123905046115317 / 100000) := by
  exact
    packedTile65536 1239038208 1239103744 13 3114 35199 30 _ _ (2093759 / 100000) (1046881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239103744 :
    ThetaLowerSegment 1239103744 1239169280 (123905046115317 / 100000)
      (123911664503321 / 100000) := by
  exact
    packedTile65536 1239103744 1239169280 13 3161 35200 30 _ _ (523441 / 25000) (2093767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239169280 :
    ThetaLowerSegment 1239169280 1239234816 (123911664503321 / 100000)
      (123918096561689 / 100000) := by
  exact
    packedTile65536 1239169280 1239234816 13 3072 35201 30 _ _ (2093769 / 100000) (523443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239234816 :
    ThetaLowerSegment 1239234816 1239300352 (123918096561689 / 100000)
      (24784925408559 / 20000) := by
  exact
    packedTile65536 1239234816 1239300352 13 3119 35202 30 _ _ (1046887 / 50000) (2093777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239300352 :
    ThetaLowerSegment 1239300352 1239365888 (24784925408559 / 20000) (24786223133403 / 20000) := by
  exact
    packedTile65536 1239300352 1239365888 13 3099 35203 30 _ _ (104689 / 5000) (2093783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239365888 :
    ThetaLowerSegment 1239365888 1239431424 (24786223133403 / 20000) (619687833093 / 500) := by
  exact
    packedTile65536 1239365888 1239431424 13 3081 35204 30 _ _ (418757 / 20000) (523447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239431424 :
    ThetaLowerSegment 1239431424 1239496960 (619687833093 / 500) (2478881356731 / 2000) := by
  exact
    packedTile65536 1239431424 1239496960 13 3105 35205 30 _ _ (209379 / 10000) (2093793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239496960 :
    ThetaLowerSegment 1239496960 1239562496 (2478881356731 / 2000) (2479012218981 / 2000) := by
  exact
    packedTile65536 1239496960 1239562496 13 3125 35206 30 _ _ (523449 / 25000) (2093799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239562496 :
    ThetaLowerSegment 1239562496 1239628032 (2479012218981 / 2000) (123957128951563 / 100000) := by
  exact
    packedTile65536 1239562496 1239628032 13 3113 35207 30 _ _ (2093801 / 100000) (523451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239628032 :
    ThetaLowerSegment 1239628032 1239693568 (123957128951563 / 100000)
      (123963596718297 / 100000) := by
  exact
    packedTile65536 1239628032 1239693568 13 3089 35208 30 _ _ (1046903 / 50000) (2093809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239693568 :
    ThetaLowerSegment 1239693568 1239759104 (123963596718297 / 100000)
      (123970317854817 / 100000) := by
  exact
    packedTile65536 1239693568 1239759104 13 3210 35209 30 _ _ (523453 / 25000) (418763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239759104 :
    ThetaLowerSegment 1239759104 1239824640 (123970317854817 / 100000)
      (123976766811177 / 100000) := by
  exact
    packedTile65536 1239759104 1239824640 13 3080 35210 30 _ _ (2093817 / 100000) (104691 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239824640 :
    ThetaLowerSegment 1239824640 1239890176 (123976766811177 / 100000)
      (123983410508383 / 100000) := by
  exact
    packedTile65536 1239824640 1239890176 13 3173 35211 30 _ _ (1046911 / 50000) (83753 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239890176 :
    ThetaLowerSegment 1239890176 1239955712 (123983410508383 / 100000)
      (123990119130091 / 100000) := by
  exact
    packedTile65536 1239890176 1239955712 13 3204 35212 30 _ _ (2093827 / 100000) (209383 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239955712 :
    ThetaLowerSegment 1239955712 1240021248 (123990119130091 / 100000)
      (123996547197401 / 100000) := by
  exact
    packedTile65536 1239955712 1240021248 13 3070 35213 30 _ _ (2093833 / 100000) (523459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240021248 :
    ThetaLowerSegment 1240021248 1240086784 (123996547197401 / 100000)
      (124003119754883 / 100000) := by
  exact
    packedTile65536 1240021248 1240086784 13 3139 35213 30 _ _ (1046919 / 50000) (2093841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240086784 :
    ThetaLowerSegment 1240086784 1240152320 (124003119754883 / 100000)
      (62004789630269 / 50000) := by
  exact
    packedTile65536 1240086784 1240152320 13 3085 35214 30 _ _ (2093843 / 100000) (1046923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240152320 :
    ThetaLowerSegment 1240152320 1240217856 (62004789630269 / 50000) (62008076973199 / 50000) := by
  exact
    packedTile65536 1240152320 1240217856 13 3140 35215 30 _ _ (2093849 / 100000) (523463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240217856 :
    ThetaLowerSegment 1240217856 1240283392 (62008076973199 / 50000) (15502828256139 / 12500) := by
  exact
    packedTile65536 1240217856 1240283392 13 3091 35216 30 _ _ (1046927 / 50000) (2093857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240283392 :
    ThetaLowerSegment 1240283392 1240348928 (15502828256139 / 12500)
      (124029190297077 / 100000) := by
  exact
    packedTile65536 1240283392 1240348928 13 3135 35217 30 _ _ (2093859 / 100000) (1046931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240348928 :
    ThetaLowerSegment 1240348928 1240414464 (124029190297077 / 100000)
      (124035714777301 / 100000) := by
  exact
    packedTile65536 1240348928 1240414464 13 3116 35218 30 _ _ (261733 / 12500) (2093867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240414464 :
    ThetaLowerSegment 1240414464 1240480000 (124035714777301 / 100000)
      (124042346063591 / 100000) := by
  exact
    packedTile65536 1240414464 1240480000 13 3167 35219 30 _ _ (209387 / 10000) (2093873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240480000 :
    ThetaLowerSegment 1240480000 1240545536 (124042346063591 / 100000)
      (62024453086983 / 50000) := by
  exact
    packedTile65536 1240480000 1240545536 13 3133 35220 30 _ _ (16751 / 800) (1046939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240545536 :
    ThetaLowerSegment 1240545536 1240611072 (62024453086983 / 50000) (62027711164263 / 50000) := by
  exact
    packedTile65536 1240545536 1240611072 13 3112 35221 30 _ _ (52347 / 2500) (2093883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240611072 :
    ThetaLowerSegment 1240611072 1240676608 (62027711164263 / 50000) (31015491953259 / 25000) := by
  exact
    packedTile65536 1240611072 1240676608 13 3126 35222 30 _ _ (418777 / 20000) (65434 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240676608 :
    ThetaLowerSegment 1240676608 1240742144 (31015491953259 / 25000) (31017121000457 / 25000) := by
  exact
    packedTile65536 1240676608 1240742144 13 3112 35223 30 _ _ (2093891 / 100000) (1046947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240742144 :
    ThetaLowerSegment 1240742144 1240807680 (31017121000457 / 25000) (1240751467789 / 1000) := by
  exact
    packedTile65536 1240742144 1240807680 13 3182 35224 30 _ _ (261737 / 12500) (2093899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240807680 :
    ThetaLowerSegment 1240807680 1240873216 (1240751467789 / 1000) (6204083987501 / 5000) := by
  exact
    packedTile65536 1240807680 1240873216 13 3120 35225 30 _ _ (2093901 / 100000) (130869 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240873216 :
    ThetaLowerSegment 1240873216 1240938752 (6204083987501 / 5000) (24817632078437 / 20000) := by
  exact
    packedTile65536 1240873216 1240938752 13 3095 35226 30 _ _ (2093907 / 100000) (209391 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1240938752 :
    ThetaLowerSegment 1240938752 1241004288 (24817632078437 / 20000)
      (124094779248017 / 100000) := by
  exact
    packedTile65536 1240938752 1241004288 13 3161 35226 30 _ _ (261739 / 12500) (418783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241004288 :
    ThetaLowerSegment 1241004288 1241069824 (124094779248017 / 100000)
      (124101358335231 / 100000) := by
  exact
    packedTile65536 1241004288 1241069824 13 3142 35227 30 _ _ (2093917 / 100000) (13087 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241069824 :
    ThetaLowerSegment 1241069824 1241135360 (124101358335231 / 100000)
      (124107694543203 / 100000) := by
  exact
    packedTile65536 1241069824 1241135360 13 3026 35228 30 _ _ (1046961 / 50000) (83757 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241135360 :
    ThetaLowerSegment 1241135360 1241200896 (124107694543203 / 100000)
      (24822853476639 / 20000) := by
  exact
    packedTile65536 1241135360 1241200896 13 3139 35229 30 _ _ (261741 / 12500) (2093931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241200896 :
    ThetaLowerSegment 1241200896 1241266432 (24822853476639 / 20000)
      (124120808829887 / 100000) := by
  exact
    packedTile65536 1241200896 1241266432 13 3124 35230 30 _ _ (2093933 / 100000) (130871 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241266432 :
    ThetaLowerSegment 1241266432 1241331968 (124120808829887 / 100000)
      (124127390077021 / 100000) := by
  exact
    packedTile65536 1241266432 1241331968 13 3143 35231 30 _ _ (1046969 / 50000) (2093941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241331968 :
    ThetaLowerSegment 1241331968 1241397504 (124127390077021 / 100000)
      (124133979718789 / 100000) := by
  exact
    packedTile65536 1241331968 1241397504 13 3147 35232 30 _ _ (261743 / 12500) (2093947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241397504 :
    ThetaLowerSegment 1241397504 1241463040 (124133979718789 / 100000)
      (15517559655317 / 12500) := by
  exact
    packedTile65536 1241397504 1241463040 13 3103 35233 30 _ _ (2093949 / 100000) (65436 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241463040 :
    ThetaLowerSegment 1241463040 1241528576 (15517559655317 / 12500) (31036780863133 / 25000) := by
  exact
    packedTile65536 1241463040 1241528576 13 3174 35234 30 _ _ (1046977 / 50000) (2093957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241528576 :
    ThetaLowerSegment 1241528576 1241594112 (31036780863133 / 25000) (31038414151153 / 25000) := by
  exact
    packedTile65536 1241528576 1241594112 13 3120 35235 30 _ _ (2093959 / 100000) (1046981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241594112 :
    ThetaLowerSegment 1241594112 1241659648 (31038414151153 / 25000)
      (124160170929727 / 100000) := by
  exact
    packedTile65536 1241594112 1241659648 13 3111 35236 30 _ _ (418793 / 20000) (130873 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241659648 :
    ThetaLowerSegment 1241659648 1241725184 (124160170929727 / 100000)
      (124166733431707 / 100000) := by
  exact
    packedTile65536 1241659648 1241725184 13 3134 35237 30 _ _ (209397 / 10000) (2093973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241725184 :
    ThetaLowerSegment 1241725184 1241790720 (124166733431707 / 100000)
      (124173308513207 / 100000) := by
  exact
    packedTile65536 1241725184 1241790720 13 3140 35238 30 _ _ (83759 / 4000) (1046989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241790720 :
    ThetaLowerSegment 1241790720 1241856256 (124173308513207 / 100000) (99343844909 / 80) := by
  exact
    packedTile65536 1241790720 1241856256 13 3103 35239 30 _ _ (2093981 / 100000) (65437 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241856256 :
    ThetaLowerSegment 1241856256 1241921792 (99343844909 / 80) (6209319586111 / 5000) := by
  exact
    packedTile65536 1241856256 1241921792 13 3145 35239 30 _ _ (1046993 / 50000) (2093989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241921792 :
    ThetaLowerSegment 1241921792 1241987328 (6209319586111 / 5000) (62096481332989 / 50000) := by
  exact
    packedTile65536 1241921792 1241987328 13 3138 35240 30 _ _ (2093991 / 100000) (1046997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241987328 :
    ThetaLowerSegment 1241987328 1242052864 (62096481332989 / 50000) (62099779376689 / 50000) := by
  exact
    packedTile65536 1241987328 1242052864 13 3150 35241 30 _ _ (523499 / 25000) (2093999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242052864 :
    ThetaLowerSegment 1242052864 1242118400 (62099779376689 / 50000) (15525766478207 / 12500) := by
  exact
    packedTile65536 1242052864 1242118400 13 3139 35242 30 _ _ (1047001 / 50000) (418801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242118400 :
    ThetaLowerSegment 1242118400 1242183936 (15525766478207 / 12500) (62106430982077 / 50000) := by
  exact
    packedTile65536 1242118400 1242183936 13 3214 35243 30 _ _ (2094007 / 100000) (209401 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242183936 :
    ThetaLowerSegment 1242183936 1242249472 (62106430982077 / 50000) (62109681935707 / 50000) := by
  exact
    packedTile65536 1242183936 1242249472 13 3105 35244 30 _ _ (523503 / 25000) (418803 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242249472 :
    ThetaLowerSegment 1242249472 1242315008 (62109681935707 / 50000) (6211294650821 / 5000) := by
  exact
    packedTile65536 1242249472 1242315008 13 3118 35245 30 _ _ (2094017 / 100000) (104701 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242315008 :
    ThetaLowerSegment 1242315008 1242380544 (6211294650821 / 5000) (124232210683811 / 100000) := by
  exact
    packedTile65536 1242315008 1242380544 13 3017 35246 30 _ _ (2094023 / 100000) (1047013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242380544 :
    ThetaLowerSegment 1242380544 1242446080 (124232210683811 / 100000)
      (124238584905043 / 100000) := by
  exact
    packedTile65536 1242380544 1242446080 13 3044 35247 30 _ _ (523507 / 25000) (2094031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242446080 :
    ThetaLowerSegment 1242446080 1242511616 (124238584905043 / 100000)
      (124245130852201 / 100000) := by
  exact
    packedTile65536 1242446080 1242511616 13 3126 35248 30 _ _ (2094033 / 100000) (523509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242511616 :
    ThetaLowerSegment 1242511616 1242577152 (124245130852201 / 100000)
      (124251647501569 / 100000) := by
  exact
    packedTile65536 1242511616 1242577152 13 3112 35249 30 _ _ (2094039 / 100000) (1047021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242577152 :
    ThetaLowerSegment 1242577152 1242642688 (124251647501569 / 100000)
      (124258153696277 / 100000) := by
  exact
    packedTile65536 1242577152 1242642688 13 3107 35250 30 _ _ (523511 / 25000) (2094047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242642688 :
    ThetaLowerSegment 1242642688 1242708224 (124258153696277 / 100000)
      (124264708069647 / 100000) := by
  exact
    packedTile65536 1242642688 1242708224 13 3130 35251 30 _ _ (2094049 / 100000) (523513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242708224 :
    ThetaLowerSegment 1242708224 1242773760 (124264708069647 / 100000)
      (124271312715963 / 100000) := by
  exact
    packedTile65536 1242708224 1242773760 13 3154 35252 30 _ _ (1047027 / 50000) (2094057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242773760 :
    ThetaLowerSegment 1242773760 1242839296 (124271312715963 / 100000)
      (124277932039623 / 100000) := by
  exact
    packedTile65536 1242773760 1242839296 13 3161 35252 30 _ _ (104703 / 5000) (2094063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242839296 :
    ThetaLowerSegment 1242839296 1242904832 (124277932039623 / 100000) (3883891183564 / 3125) := by
  exact
    packedTile65536 1242839296 1242904832 13 3145 35253 30 _ _ (418813 / 20000) (523517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242904832 :
    ThetaLowerSegment 1242904832 1242970368 (3883891183564 / 3125) (62145545579889 / 50000) := by
  exact
    packedTile65536 1242904832 1242970368 13 3139 35254 30 _ _ (209407 / 10000) (2094073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1242970368 :
    ThetaLowerSegment 1242970368 1243035904 (62145545579889 / 50000)
      (124297559757453 / 100000) := by
  exact
    packedTile65536 1242970368 1243035904 13 3089 35255 30 _ _ (83763 / 4000) (1047039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243035904 :
    ThetaLowerSegment 1243035904 1243101440 (124297559757453 / 100000)
      (31076031175347 / 25000) := by
  exact
    packedTile65536 1243035904 1243101440 13 3135 35256 30 _ _ (2094081 / 100000) (523521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243101440 :
    ThetaLowerSegment 1243101440 1243166976 (31076031175347 / 25000) (6215532074851 / 5000) := by
  exact
    packedTile65536 1243101440 1243166976 13 3112 35257 30 _ _ (1047043 / 50000) (2094089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243166976 :
    ThetaLowerSegment 1243166976 1243232512 (6215532074851 / 5000) (62158623130017 / 50000) := by
  exact
    packedTile65536 1243166976 1243232512 13 3154 35258 30 _ _ (2094091 / 100000) (1047047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243232512 :
    ThetaLowerSegment 1243232512 1243298048 (62158623130017 / 50000)
      (124323752619413 / 100000) := by
  exact
    packedTile65536 1243232512 1243298048 13 3107 35259 30 _ _ (2094097 / 100000) (20941 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243298048 :
    ThetaLowerSegment 1243298048 1243363584 (124323752619413 / 100000)
      (124330227582797 / 100000) := by
  exact
    packedTile65536 1243298048 1243363584 13 3092 35260 30 _ _ (1047051 / 50000) (418821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243363584 :
    ThetaLowerSegment 1243363584 1243429120 (124330227582797 / 100000)
      (124336798890563 / 100000) := by
  exact
    packedTile65536 1243363584 1243429120 13 3138 35261 30 _ _ (2094107 / 100000) (209411 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243429120 :
    ThetaLowerSegment 1243429120 1243494656 (124336798890563 / 100000)
      (24868666922823 / 20000) := by
  exact
    packedTile65536 1243429120 1243494656 13 3121 35262 30 _ _ (65441 / 3125) (418823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243494656 :
    ThetaLowerSegment 1243494656 1243560192 (24868666922823 / 20000)
      (124349790779909 / 100000) := by
  exact
    packedTile65536 1243494656 1243560192 13 3083 35263 30 _ _ (1047059 / 50000) (2094121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243560192 :
    ThetaLowerSegment 1243560192 1243625728 (124349790779909 / 100000)
      (124356399832097 / 100000) := by
  exact
    packedTile65536 1243560192 1243625728 13 3156 35264 30 _ _ (2094123 / 100000) (1047063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243625728 :
    ThetaLowerSegment 1243625728 1243691264 (124356399832097 / 100000)
      (124362979582273 / 100000) := by
  exact
    packedTile65536 1243625728 1243691264 13 3142 35265 30 _ _ (130883 / 6250) (2094131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243691264 :
    ThetaLowerSegment 1243691264 1243756800 (124362979582273 / 100000)
      (124369550971627 / 100000) := by
  exact
    packedTile65536 1243691264 1243756800 13 3138 35266 30 _ _ (2094133 / 100000) (261767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243756800 :
    ThetaLowerSegment 1243756800 1243822336 (124369550971627 / 100000) (7773507256087 / 6250) := by
  exact
    packedTile65536 1243756800 1243822336 13 3135 35266 30 _ _ (2094139 / 100000) (1047071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243822336 :
    ThetaLowerSegment 1243822336 1243887872 (7773507256087 / 6250) (7773919409803 / 6250) := by
  exact
    packedTile65536 1243822336 1243887872 13 3149 35267 30 _ _ (65442 / 3125) (2094147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243887872 :
    ThetaLowerSegment 1243887872 1243953408 (7773919409803 / 6250) (4975570023367 / 4000) := by
  exact
    packedTile65536 1243887872 1243953408 13 3123 35268 30 _ _ (2094149 / 100000) (261769 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243953408 :
    ThetaLowerSegment 1243953408 1244018944 (4975570023367 / 4000) (12439589533799 / 10000) := by
  exact
    packedTile65536 1243953408 1244018944 13 3173 35269 30 _ _ (418831 / 20000) (1047079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244018944 :
    ThetaLowerSegment 1244018944 1244084480 (12439589533799 / 10000) (12440239561063 / 10000) := by
  exact
    packedTile65536 1244018944 1244084480 13 3104 35270 30 _ _ (26177 / 1250) (2094163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244084480 :
    ThetaLowerSegment 1244084480 1244150016 (12440239561063 / 10000) (24881789650583 / 20000) := by
  exact
    packedTile65536 1244084480 1244150016 13 3129 35271 30 _ _ (418833 / 20000) (261771 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244150016 :
    ThetaLowerSegment 1244150016 1244215552 (24881789650583 / 20000) (24883086360647 / 20000) := by
  exact
    packedTile65536 1244150016 1244215552 13 3096 35272 30 _ _ (209417 / 10000) (2094173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244215552 :
    ThetaLowerSegment 1244215552 1244281088 (24883086360647 / 20000)
      (124421971914883 / 100000) := by
  exact
    packedTile65536 1244215552 1244281088 13 3123 35273 30 _ _ (65443 / 3125) (2094179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244281088 :
    ThetaLowerSegment 1244281088 1244346624 (124421971914883 / 100000)
      (24885697801231 / 20000) := by
  exact
    packedTile65536 1244281088 1244346624 13 3112 35274 30 _ _ (2094181 / 100000) (261773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244346624 :
    ThetaLowerSegment 1244346624 1244412160 (24885697801231 / 20000)
      (124435010301359 / 100000) := by
  exact
    packedTile65536 1244346624 1244412160 13 3114 35275 30 _ _ (1047093 / 50000) (2094189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244412160 :
    ThetaLowerSegment 1244412160 1244477696 (124435010301359 / 100000)
      (124441519046987 / 100000) := by
  exact
    packedTile65536 1244412160 1244477696 13 3108 35276 30 _ _ (2094191 / 100000) (1047097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244477696 :
    ThetaLowerSegment 1244477696 1244543232 (124441519046987 / 100000)
      (12444809273137 / 10000) := by
  exact
    packedTile65536 1244477696 1244543232 13 3139 35277 30 _ _ (2094197 / 100000) (10471 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244543232 :
    ThetaLowerSegment 1244543232 1244608768 (12444809273137 / 10000) (3111367498467 / 2500) := by
  exact
    packedTile65536 1244543232 1244608768 13 3155 35278 30 _ _ (1047101 / 50000) (418841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244608768 :
    ThetaLowerSegment 1244608768 1244674304 (3111367498467 / 2500) (62230631591709 / 50000) := by
  exact
    packedTile65536 1244608768 1244674304 13 3134 35279 30 _ _ (2094207 / 100000) (209421 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244674304 :
    ThetaLowerSegment 1244674304 1244739840 (62230631591709 / 50000) (12446785157437 / 10000) := by
  exact
    packedTile65536 1244674304 1244739840 13 3146 35279 30 _ _ (523553 / 25000) (418843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244739840 :
    ThetaLowerSegment 1244739840 1244805376 (12446785157437 / 10000) (6223721894499 / 5000) := by
  exact
    packedTile65536 1244739840 1244805376 13 3145 35280 30 _ _ (1047109 / 50000) (2094221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244805376 :
    ThetaLowerSegment 1244805376 1244870912 (6223721894499 / 5000) (62240525723107 / 50000) := by
  exact
    packedTile65536 1244805376 1244870912 13 3158 35281 30 _ _ (2094223 / 100000) (1047113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244870912 :
    ThetaLowerSegment 1244870912 1244936448 (62240525723107 / 50000) (99590054947 / 80) := by
  exact
    packedTile65536 1244870912 1244936448 13 3112 35282 30 _ _ (523557 / 25000) (2094231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1244936448 :
    ThetaLowerSegment 1244936448 1245001984 (99590054947 / 80) (62247080666191 / 50000) := by
  exact
    packedTile65536 1244936448 1245001984 13 3148 35283 30 _ _ (1047117 / 50000) (2094237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245001984 :
    ThetaLowerSegment 1245001984 1245067520 (62247080666191 / 50000)
      (124500701640779 / 100000) := by
  exact
    packedTile65536 1245001984 1245067520 13 3123 35284 30 _ _ (2094239 / 100000) (1047121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245067520 :
    ThetaLowerSegment 1245067520 1245133056 (124500701640779 / 100000) (4980290600059 / 4000) := by
  exact
    packedTile65536 1245067520 1245133056 13 3134 35285 30 _ _ (523561 / 25000) (2094247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245133056 :
    ThetaLowerSegment 1245133056 1245198592 (4980290600059 / 4000) (124513748796379 / 100000) := by
  exact
    packedTile65536 1245133056 1245198592 13 3096 35286 30 _ _ (2094249 / 100000) (523563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245198592 :
    ThetaLowerSegment 1245198592 1245264128 (124513748796379 / 100000)
      (62260209499277 / 50000) := by
  exact
    packedTile65536 1245198592 1245264128 13 3185 35287 30 _ _ (418851 / 20000) (1047129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245264128 :
    ThetaLowerSegment 1245264128 1245329664 (62260209499277 / 50000) (62263462932187 / 50000) := by
  exact
    packedTile65536 1245264128 1245329664 13 3107 35288 30 _ _ (104713 / 5000) (2094263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245329664 :
    ThetaLowerSegment 1245329664 1245395200 (62263462932187 / 50000) (62266742551177 / 50000) := by
  exact
    packedTile65536 1245329664 1245395200 13 3132 35289 30 _ _ (418853 / 20000) (523567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245395200 :
    ThetaLowerSegment 1245395200 1245460736 (62266742551177 / 50000) (62270047309237 / 50000) := by
  exact
    packedTile65536 1245395200 1245460736 13 3156 35290 30 _ _ (209427 / 10000) (2094273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245460736 :
    ThetaLowerSegment 1245460736 1245526272 (62270047309237 / 50000) (62273349982489 / 50000) := by
  exact
    packedTile65536 1245460736 1245526272 13 3154 35291 30 _ _ (523569 / 25000) (2094279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245526272 :
    ThetaLowerSegment 1245526272 1245591808 (62273349982489 / 50000) (31138297011879 / 25000) := by
  exact
    packedTile65536 1245526272 1245591808 13 3098 35292 30 _ _ (2094281 / 100000) (523571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245591808 :
    ThetaLowerSegment 1245591808 1245657344 (31138297011879 / 25000) (31139930554959 / 25000) := by
  exact
    packedTile65536 1245591808 1245657344 13 3120 35292 30 _ _ (1047143 / 50000) (2094289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245657344 :
    ThetaLowerSegment 1245657344 1245722880 (31139930554959 / 25000) (31141568290521 / 25000) := by
  exact
    packedTile65536 1245657344 1245722880 13 3128 35293 30 _ _ (2094291 / 100000) (1047147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245722880 :
    ThetaLowerSegment 1245722880 1245788416 (31141568290521 / 25000) (3892903109931 / 3125) := by
  exact
    packedTile65536 1245722880 1245788416 13 3164 35294 30 _ _ (2094297 / 100000) (20943 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245788416 :
    ThetaLowerSegment 1245788416 1245853952 (3892903109931 / 3125) (62289776557623 / 50000) := by
  exact
    packedTile65536 1245788416 1245853952 13 3177 35295 30 _ _ (1047151 / 50000) (418861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245853952 :
    ThetaLowerSegment 1245853952 1245919488 (62289776557623 / 50000)
      (124586106201849 / 100000) := by
  exact
    packedTile65536 1245853952 1245919488 13 3129 35296 30 _ _ (2094307 / 100000) (209431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245919488 :
    ThetaLowerSegment 1245919488 1245985024 (124586106201849 / 100000)
      (124592697001713 / 100000) := by
  exact
    packedTile65536 1245919488 1245985024 13 3147 35297 30 _ _ (261789 / 12500) (418863 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245985024 :
    ThetaLowerSegment 1245985024 1246050560 (124592697001713 / 100000)
      (124599193576149 / 100000) := by
  exact
    packedTile65536 1245985024 1246050560 13 3102 35298 30 _ _ (1047159 / 50000) (2094321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246050560 :
    ThetaLowerSegment 1246050560 1246116096 (124599193576149 / 100000)
      (12460574252417 / 10000) := by
  exact
    packedTile65536 1246050560 1246116096 13 3127 35299 30 _ _ (2094323 / 100000) (1047163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246116096 :
    ThetaLowerSegment 1246116096 1246181632 (12460574252417 / 10000) (62306192866293 / 50000) := by
  exact
    packedTile65536 1246116096 1246181632 13 3172 35300 30 _ _ (261791 / 12500) (2094331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246181632 :
    ThetaLowerSegment 1246181632 1246247168 (62306192866293 / 50000) (62309501914013 / 50000) := by
  exact
    packedTile65536 1246181632 1246247168 13 3160 35301 30 _ _ (1047167 / 50000) (2094337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246247168 :
    ThetaLowerSegment 1246247168 1246312704 (62309501914013 / 50000) (7789100585827 / 6250) := by
  exact
    packedTile65536 1246247168 1246312704 13 3154 35302 30 _ _ (2094339 / 100000) (1047171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246312704 :
    ThetaLowerSegment 1246312704 1246378240 (7789100585827 / 6250) (1557902634319 / 1250) := by
  exact
    packedTile65536 1246312704 1246378240 13 3152 35303 30 _ _ (261793 / 12500) (2094347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246378240 :
    ThetaLowerSegment 1246378240 1246443776 (1557902634319 / 1250) (124638772340937 / 100000) := by
  exact
    packedTile65536 1246378240 1246443776 13 3133 35304 30 _ _ (2094349 / 100000) (130897 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246443776 :
    ThetaLowerSegment 1246443776 1246509312 (124638772340937 / 100000)
      (62322706770321 / 50000) := by
  exact
    packedTile65536 1246443776 1246509312 13 3171 35305 30 _ _ (418871 / 20000) (1047179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246509312 :
    ThetaLowerSegment 1246509312 1246574848 (62322706770321 / 50000) (62325961405761 / 50000) := by
  exact
    packedTile65536 1246509312 1246574848 13 3108 35305 30 _ _ (52359 / 2500) (2094363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246574848 :
    ThetaLowerSegment 1246574848 1246640384 (62325961405761 / 50000) (62329203482781 / 50000) := by
  exact
    packedTile65536 1246574848 1246640384 13 3096 35306 30 _ _ (418873 / 20000) (65449 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246640384 :
    ThetaLowerSegment 1246640384 1246705920 (62329203482781 / 50000) (62332481171831 / 50000) := by
  exact
    packedTile65536 1246640384 1246705920 13 3130 35307 30 _ _ (209437 / 10000) (2094373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246705920 :
    ThetaLowerSegment 1246705920 1246771456 (62332481171831 / 50000) (62335780861219 / 50000) := by
  exact
    packedTile65536 1246705920 1246771456 13 3151 35308 30 _ _ (261797 / 12500) (2094379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246771456 :
    ThetaLowerSegment 1246771456 1246836992 (62335780861219 / 50000) (62339048095579 / 50000) := by
  exact
    packedTile65536 1246771456 1246836992 13 3120 35309 30 _ _ (2094381 / 100000) (130899 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246836992 :
    ThetaLowerSegment 1246836992 1246902528 (62339048095579 / 50000) (62342342564757 / 50000) := by
  exact
    packedTile65536 1246836992 1246902528 13 3146 35310 30 _ _ (1047193 / 50000) (2094389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246902528 :
    ThetaLowerSegment 1246902528 1246968064 (62342342564757 / 50000) (31172795482599 / 25000) := by
  exact
    packedTile65536 1246902528 1246968064 13 3102 35311 30 _ _ (2094391 / 100000) (1047197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1246968064 :
    ThetaLowerSegment 1246968064 1247033600 (31172795482599 / 25000) (1558722816971 / 1250) := by
  exact
    packedTile65536 1246968064 1247033600 13 3172 35312 30 _ _ (2094397 / 100000) (2618 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247033600 :
    ThetaLowerSegment 1247033600 1247099136 (1558722816971 / 1250) (62352220786799 / 50000) := by
  exact
    packedTile65536 1247033600 1247099136 13 3159 35313 30 _ _ (1047201 / 50000) (418881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247099136 :
    ThetaLowerSegment 1247099136 1247164672 (62352220786799 / 50000)
      (124711057805311 / 100000) := by
  exact
    packedTile65536 1247099136 1247164672 13 3159 35314 30 _ _ (2094407 / 100000) (209441 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247164672 :
    ThetaLowerSegment 1247164672 1247230208 (124711057805311 / 100000)
      (124717556765747 / 100000) := by
  exact
    packedTile65536 1247164672 1247230208 13 3103 35315 30 _ _ (523603 / 25000) (418883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247230208 :
    ThetaLowerSegment 1247230208 1247295744 (124717556765747 / 100000)
      (124724204448479 / 100000) := by
  exact
    packedTile65536 1247230208 1247295744 13 3174 35316 30 _ _ (1047209 / 50000) (2094421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247295744 :
    ThetaLowerSegment 1247295744 1247361280 (124724204448479 / 100000)
      (62365358004793 / 50000) := by
  exact
    packedTile65536 1247295744 1247361280 13 3109 35317 30 _ _ (2094423 / 100000) (1047213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247361280 :
    ThetaLowerSegment 1247361280 1247426816 (62365358004793 / 50000) (62368580282271 / 50000) := by
  exact
    packedTile65536 1247361280 1247426816 13 3077 35318 30 _ _ (523607 / 25000) (2094431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247426816 :
    ThetaLowerSegment 1247426816 1247492352 (62368580282271 / 50000) (3898243747411 / 3125) := by
  exact
    packedTile65536 1247426816 1247492352 13 3170 35318 30 _ _ (2094433 / 100000) (523609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247492352 :
    ThetaLowerSegment 1247492352 1247557888 (3898243747411 / 3125) (24950057278947 / 20000) := by
  exact
    packedTile65536 1247492352 1247557888 13 3097 35319 30 _ _ (2094439 / 100000) (1047221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247557888 :
    ThetaLowerSegment 1247557888 1247623424 (24950057278947 / 20000)
      (124756712148927 / 100000) := by
  exact
    packedTile65536 1247557888 1247623424 13 3068 35320 30 _ _ (523611 / 25000) (2094447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247623424 :
    ThetaLowerSegment 1247623424 1247688960 (124756712148927 / 100000)
      (124763255207603 / 100000) := by
  exact
    packedTile65536 1247623424 1247688960 13 3124 35321 30 _ _ (2094449 / 100000) (523613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247688960 :
    ThetaLowerSegment 1247688960 1247754496 (124763255207603 / 100000)
      (124769706125923 / 100000) := by
  exact
    packedTile65536 1247688960 1247754496 13 3080 35322 30 _ _ (1047227 / 50000) (2094457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247754496 :
    ThetaLowerSegment 1247754496 1247820032 (124769706125923 / 100000)
      (124776299486003 / 100000) := by
  exact
    packedTile65536 1247754496 1247820032 13 3148 35323 30 _ _ (104723 / 5000) (2094463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247820032 :
    ThetaLowerSegment 1247820032 1247885568 (124776299486003 / 100000)
      (124782884483963 / 100000) := by
  exact
    packedTile65536 1247820032 1247885568 13 3144 35324 30 _ _ (418893 / 20000) (523617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247885568 :
    ThetaLowerSegment 1247885568 1247951104 (124782884483963 / 100000)
      (124789538615153 / 100000) := by
  exact
    packedTile65536 1247885568 1247951104 13 3177 35325 30 _ _ (209447 / 10000) (2094473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247951104 :
    ThetaLowerSegment 1247951104 1248016640 (124789538615153 / 100000)
      (124796261879903 / 100000) := by
  exact
    packedTile65536 1247951104 1248016640 13 3210 35326 30 _ _ (83779 / 4000) (1047239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248016640 :
    ThetaLowerSegment 1248016640 1248082176 (124796261879903 / 100000)
      (124802813416471 / 100000) := by
  exact
    packedTile65536 1248016640 1248082176 13 3128 35327 30 _ _ (2094481 / 100000) (523621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248082176 :
    ThetaLowerSegment 1248082176 1248147712 (124802813416471 / 100000)
      (124809310512043 / 100000) := by
  exact
    packedTile65536 1248082176 1248147712 13 3102 35328 30 _ _ (1047243 / 50000) (2094489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248147712 :
    ThetaLowerSegment 1248147712 1248213248 (124809310512043 / 100000)
      (62407957221083 / 50000) := by
  exact
    packedTile65536 1248147712 1248213248 13 3153 35329 30 _ _ (2094491 / 100000) (1047247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248213248 :
    ThetaLowerSegment 1248213248 1248278784 (62407957221083 / 50000) (62411199500891 / 50000) := by
  exact
    packedTile65536 1248213248 1248278784 13 3096 35330 30 _ _ (65453 / 3125) (2094499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248278784 :
    ThetaLowerSegment 1248278784 1248344320 (62411199500891 / 50000) (31207225607623 / 25000) := by
  exact
    packedTile65536 1248278784 1248344320 13 3105 35330 30 _ _ (1047251 / 50000) (418901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248344320 :
    ThetaLowerSegment 1248344320 1248409856 (31207225607623 / 25000) (62417771008841 / 50000) := by
  exact
    packedTile65536 1248344320 1248409856 13 3170 35331 30 _ _ (2094507 / 100000) (209451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248409856 :
    ThetaLowerSegment 1248409856 1248475392 (62417771008841 / 50000) (2496841286561 / 2000) := by
  exact
    packedTile65536 1248409856 1248475392 13 3114 35332 30 _ _ (130907 / 6250) (418903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248475392 :
    ThetaLowerSegment 1248475392 1248540928 (2496841286561 / 2000) (31212150852531 / 25000) := by
  exact
    packedTile65536 1248475392 1248540928 13 3122 35333 30 _ _ (2094517 / 100000) (52363 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248540928 :
    ThetaLowerSegment 1248540928 1248606464 (31212150852531 / 25000) (15606897526543 / 12500) := by
  exact
    packedTile65536 1248540928 1248606464 13 3140 35334 30 _ _ (2094523 / 100000) (1047263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248606464 :
    ThetaLowerSegment 1248606464 1248672000 (15606897526543 / 12500) (15607723817839 / 12500) := by
  exact
    packedTile65536 1248606464 1248672000 13 3156 35335 30 _ _ (65454 / 3125) (2094531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248672000 :
    ThetaLowerSegment 1248672000 1248737536 (15607723817839 / 12500) (15608536496643 / 12500) := by
  exact
    packedTile65536 1248672000 1248737536 13 3104 35336 30 _ _ (2094533 / 100000) (261817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248737536 :
    ThetaLowerSegment 1248737536 1248803072 (15608536496643 / 12500) (31218709874733 / 25000) := by
  exact
    packedTile65536 1248737536 1248803072 13 3126 35337 30 _ _ (1047269 / 50000) (2094541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248803072 :
    ThetaLowerSegment 1248803072 1248868608 (31218709874733 / 25000) (31220350949957 / 25000) := by
  exact
    packedTile65536 1248803072 1248868608 13 3134 35338 30 _ _ (130909 / 6250) (2094547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248868608 :
    ThetaLowerSegment 1248868608 1248934144 (31220350949957 / 25000)
      (124887878050787 / 100000) := by
  exact
    packedTile65536 1248868608 1248934144 13 3091 35339 30 _ _ (2094549 / 100000) (261819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248934144 :
    ThetaLowerSegment 1248934144 1248999680 (124887878050787 / 100000)
      (124894400491943 / 100000) := by
  exact
    packedTile65536 1248934144 1248999680 13 3114 35340 30 _ _ (1047277 / 50000) (2094557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1248999680 :
    ThetaLowerSegment 1248999680 1249065216 (124894400491943 / 100000)
      (31225243828161 / 25000) := by
  exact
    packedTile65536 1248999680 1249065216 13 3139 35341 30 _ _ (2094559 / 100000) (1047281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249065216 :
    ThetaLowerSegment 1249065216 1249130752 (31225243828161 / 25000)
      (124907654880429 / 100000) := by
  exact
    packedTile65536 1249065216 1249130752 13 3189 35342 30 _ _ (418913 / 20000) (261821 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249130752 :
    ThetaLowerSegment 1249130752 1249196288 (124907654880429 / 100000)
      (124914210884529 / 100000) := by
  exact
    packedTile65536 1249130752 1249196288 13 3130 35343 30 _ _ (209457 / 10000) (2094573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249196288 :
    ThetaLowerSegment 1249196288 1249261824 (124914210884529 / 100000)
      (62460422201777 / 50000) := by
  exact
    packedTile65536 1249196288 1249261824 13 3167 35343 30 _ _ (83783 / 4000) (1047289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249261824 :
    ThetaLowerSegment 1249261824 1249327360 (62460422201777 / 50000) (62463728496307 / 50000) := by
  exact
    packedTile65536 1249261824 1249327360 13 3157 35344 30 _ _ (104729 / 5000) (2094583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249327360 :
    ThetaLowerSegment 1249327360 1249392896 (62463728496307 / 50000) (12493415128947 / 10000) := by
  exact
    packedTile65536 1249327360 1249392896 13 3196 35345 30 _ _ (1047293 / 50000) (2094589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249392896 :
    ThetaLowerSegment 1249392896 1249458432 (12493415128947 / 10000) (62470334828331 / 50000) := by
  exact
    packedTile65536 1249392896 1249458432 13 3112 35346 30 _ _ (2094591 / 100000) (1047297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249458432 :
    ThetaLowerSegment 1249458432 1249523968 (62470334828331 / 50000) (62473567837257 / 50000) := by
  exact
    packedTile65536 1249458432 1249523968 13 3087 35347 30 _ _ (523649 / 25000) (2094599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249523968 :
    ThetaLowerSegment 1249523968 1249589504 (62473567837257 / 50000) (15619227181463 / 12500) := by
  exact
    packedTile65536 1249523968 1249589504 13 3190 35348 30 _ _ (2094601 / 100000) (523651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249589504 :
    ThetaLowerSegment 1249589504 1249655040 (15619227181463 / 12500) (62480199353449 / 50000) := by
  exact
    packedTile65536 1249589504 1249655040 13 3142 35349 30 _ _ (2094607 / 100000) (209461 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249655040 :
    ThetaLowerSegment 1249655040 1249720576 (62480199353449 / 50000) (62483472184699 / 50000) := by
  exact
    packedTile65536 1249655040 1249720576 13 3125 35350 30 _ _ (523653 / 25000) (418923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249720576 :
    ThetaLowerSegment 1249720576 1249786112 (62483472184699 / 50000)
      (124973452344417 / 100000) := by
  exact
    packedTile65536 1249720576 1249786112 13 3107 35351 30 _ _ (2094617 / 100000) (104731 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249786112 :
    ThetaLowerSegment 1249786112 1249851648 (124973452344417 / 100000)
      (124979962429593 / 100000) := by
  exact
    packedTile65536 1249786112 1249851648 13 3108 35352 30 _ _ (1047311 / 50000) (16757 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249851648 :
    ThetaLowerSegment 1249851648 1249917184 (124979962429593 / 100000)
      (124986476722673 / 100000) := by
  exact
    packedTile65536 1249851648 1249917184 13 3110 35353 30 _ _ (523657 / 25000) (2094631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249917184 :
    ThetaLowerSegment 1249917184 1249982720 (124986476722673 / 100000)
      (31248258754649 / 25000) := by
  exact
    packedTile65536 1249917184 1249982720 13 3131 35354 30 _ _ (2094633 / 100000) (523659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249982720 :
    ThetaLowerSegment 1249982720 1250048256 (31248258754649 / 25000) (31249913518669 / 25000) := by
  exact
    packedTile65536 1249982720 1250048256 13 3160 35355 30 _ _ (1047319 / 50000) (2094641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250048256 :
    ThetaLowerSegment 1250048256 1250113792 (31249913518669 / 25000) (62503084207203 / 50000) := by
  exact
    packedTile65536 1250048256 1250113792 13 3110 35356 30 _ _ (2094643 / 100000) (1047323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250113792 :
    ThetaLowerSegment 1250113792 1250179328 (62503084207203 / 50000) (7813303670207 / 6250) := by
  exact
    packedTile65536 1250113792 1250179328 13 3194 35356 30 _ _ (2094649 / 100000) (523663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250179328 :
    ThetaLowerSegment 1250179328 1250244864 (7813303670207 / 6250) (31254847463621 / 25000) := by
  exact
    packedTile65536 1250179328 1250244864 13 3118 35357 30 _ _ (1047327 / 50000) (2094657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250244864 :
    ThetaLowerSegment 1250244864 1250310400 (31254847463621 / 25000)
      (125026065532717 / 100000) := by
  exact
    packedTile65536 1250244864 1250310400 13 3187 35358 30 _ _ (2094659 / 100000) (1047331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250310400 :
    ThetaLowerSegment 1250310400 1250375936 (125026065532717 / 100000)
      (125032609263053 / 100000) := by
  exact
    packedTile65536 1250310400 1250375936 13 3124 35359 30 _ _ (261833 / 12500) (2094667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250375936 :
    ThetaLowerSegment 1250375936 1250441472 (125032609263053 / 100000)
      (125039041994623 / 100000) := by
  exact
    packedTile65536 1250375936 1250441472 13 3071 35360 30 _ _ (209467 / 10000) (2094673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250441472 :
    ThetaLowerSegment 1250441472 1250507008 (125039041994623 / 100000)
      (125045598327373 / 100000) := by
  exact
    packedTile65536 1250441472 1250507008 13 3130 35361 30 _ _ (83787 / 4000) (1047339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250507008 :
    ThetaLowerSegment 1250507008 1250572544 (125045598327373 / 100000)
      (125052148391733 / 100000) := by
  exact
    packedTile65536 1250507008 1250572544 13 3127 35362 30 _ _ (52367 / 2500) (2094683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250572544 :
    ThetaLowerSegment 1250572544 1250638080 (125052148391733 / 100000)
      (125058696377043 / 100000) := by
  exact
    packedTile65536 1250572544 1250638080 13 3126 35363 30 _ _ (418937 / 20000) (65459 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250638080 :
    ThetaLowerSegment 1250638080 1250703616 (125058696377043 / 100000)
      (125065265324883 / 100000) := by
  exact
    packedTile65536 1250638080 1250703616 13 3136 35364 30 _ _ (209469 / 10000) (2094693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250703616 :
    ThetaLowerSegment 1250703616 1250769152 (125065265324883 / 100000)
      (25014365182551 / 20000) := by
  exact
    packedTile65536 1250703616 1250769152 13 3132 35365 30 _ _ (261837 / 12500) (2094699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250769152 :
    ThetaLowerSegment 1250769152 1250834688 (25014365182551 / 20000)
      (125078428410307 / 100000) := by
  exact
    packedTile65536 1250769152 1250834688 13 3152 35366 30 _ _ (2094701 / 100000) (130919 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250834688 :
    ThetaLowerSegment 1250834688 1250900224 (125078428410307 / 100000)
      (125084878010081 / 100000) := by
  exact
    packedTile65536 1250834688 1250900224 13 3079 35367 30 _ _ (1047353 / 50000) (2094709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250900224 :
    ThetaLowerSegment 1250900224 1250965760 (125084878010081 / 100000) (3127287903731 / 2500) := by
  exact
    packedTile65536 1250900224 1250965760 13 3169 35368 30 _ _ (2094711 / 100000) (1047357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1250965760 :
    ThetaLowerSegment 1250965760 1251031296 (3127287903731 / 2500) (62549040496159 / 50000) := by
  exact
    packedTile65536 1250965760 1251031296 13 3134 35368 30 _ _ (2094717 / 100000) (13092 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251031296 :
    ThetaLowerSegment 1251031296 1251096832 (62549040496159 / 50000) (62552373198861 / 50000) := by
  exact
    packedTile65536 1251031296 1251096832 13 3182 35369 30 _ _ (1047361 / 50000) (83789 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251096832 :
    ThetaLowerSegment 1251096832 1251162368 (62552373198861 / 50000) (7819452241373 / 6250) := by
  exact
    packedTile65536 1251096832 1251162368 13 3098 35370 30 _ _ (2094727 / 100000) (209473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251162368 :
    ThetaLowerSegment 1251162368 1251227904 (7819452241373 / 6250) (15639725094007 / 12500) := by
  exact
    packedTile65536 1251162368 1251227904 13 3134 35371 30 _ _ (523683 / 25000) (418947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251227904 :
    ThetaLowerSegment 1251227904 1251293440 (15639725094007 / 12500) (62562198541009 / 50000) := by
  exact
    packedTile65536 1251227904 1251293440 13 3149 35372 30 _ _ (1047369 / 50000) (2094741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251293440 :
    ThetaLowerSegment 1251293440 1251358976 (62562198541009 / 50000) (5005239737109 / 4000) := by
  exact
    packedTile65536 1251293440 1251358976 13 3149 35373 30 _ _ (2094743 / 100000) (1047373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251358976 :
    ThetaLowerSegment 1251358976 1251424512 (5005239737109 / 4000) (25027530945273 / 20000) := by
  exact
    packedTile65536 1251358976 1251424512 13 3180 35374 30 _ _ (523687 / 25000) (2094751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251424512 :
    ThetaLowerSegment 1251424512 1251490048 (25027530945273 / 20000) (6257211088851 / 5000) := by
  exact
    packedTile65536 1251424512 1251490048 13 3135 35375 30 _ _ (2094753 / 100000) (523689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251490048 :
    ThetaLowerSegment 1251490048 1251555584 (6257211088851 / 5000) (125150738572269 / 100000) := by
  exact
    packedTile65536 1251490048 1251555584 13 3111 35376 30 _ _ (2094759 / 100000) (1047381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251555584 :
    ThetaLowerSegment 1251555584 1251621120 (125150738572269 / 100000)
      (125157211393029 / 100000) := by
  exact
    packedTile65536 1251555584 1251621120 13 3090 35377 30 _ _ (523691 / 25000) (2094767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251621120 :
    ThetaLowerSegment 1251621120 1251686656 (125157211393029 / 100000)
      (125163809915379 / 100000) := by
  exact
    packedTile65536 1251621120 1251686656 13 3150 35378 30 _ _ (2094769 / 100000) (523693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251686656 :
    ThetaLowerSegment 1251686656 1251752192 (125163809915379 / 100000)
      (125170326757293 / 100000) := by
  exact
    packedTile65536 1251686656 1251752192 13 3111 35379 30 _ _ (1047387 / 50000) (2094777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251752192 :
    ThetaLowerSegment 1251752192 1251817728 (125170326757293 / 100000)
      (125176893892593 / 100000) := by
  exact
    packedTile65536 1251752192 1251817728 13 3135 35380 30 _ _ (104739 / 5000) (2094783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251817728 :
    ThetaLowerSegment 1251817728 1251883264 (125176893892593 / 100000)
      (62591686531299 / 50000) := by
  exact
    packedTile65536 1251817728 1251883264 13 3093 35381 30 _ _ (418957 / 20000) (523697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251883264 :
    ThetaLowerSegment 1251883264 1251948800 (62591686531299 / 50000) (3912186679559 / 3125) := by
  exact
    packedTile65536 1251883264 1251948800 13 3151 35381 30 _ _ (209479 / 10000) (2094793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251948800 :
    ThetaLowerSegment 1251948800 1252014336 (3912186679559 / 3125) (62598194004089 / 50000) := by
  exact
    packedTile65536 1251948800 1252014336 13 3062 35382 30 _ _ (418959 / 20000) (1047399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252014336 :
    ThetaLowerSegment 1252014336 1252079872 (62598194004089 / 50000) (62601391716289 / 50000) := by
  exact
    packedTile65536 1252014336 1252079872 13 3053 35383 30 _ _ (5237 / 250) (2094803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252079872 :
    ThetaLowerSegment 1252079872 1252145408 (62601391716289 / 50000) (15651175639293 / 12500) := by
  exact
    packedTile65536 1252079872 1252145408 13 3161 35384 30 _ _ (1047403 / 50000) (2094809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252145408 :
    ThetaLowerSegment 1252145408 1252210944 (15651175639293 / 12500) (62607959988277 / 50000) := by
  exact
    packedTile65536 1252145408 1252210944 13 3110 35385 30 _ _ (2094811 / 100000) (1047407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252210944 :
    ThetaLowerSegment 1252210944 1252276480 (62607959988277 / 50000) (12522238457873 / 10000) := by
  exact
    packedTile65536 1252210944 1252276480 13 3086 35386 30 _ _ (65463 / 3125) (2094819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252276480 :
    ThetaLowerSegment 1252276480 1252342016 (12522238457873 / 10000) (62614456020483 / 50000) := by
  exact
    packedTile65536 1252276480 1252342016 13 3116 35387 30 _ _ (2094821 / 100000) (261853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252342016 :
    ThetaLowerSegment 1252342016 1252407552 (62614456020483 / 50000) (12523534734951 / 10000) := by
  exact
    packedTile65536 1252342016 1252407552 13 3072 35388 30 _ _ (2094827 / 100000) (209483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252407552 :
    ThetaLowerSegment 1252407552 1252473088 (12523534734951 / 10000) (62620922759187 / 50000) := by
  exact
    packedTile65536 1252407552 1252473088 13 3102 35389 30 _ _ (130927 / 6250) (418967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252473088 :
    ThetaLowerSegment 1252473088 1252538624 (62620922759187 / 50000) (12524848196199 / 10000) := by
  exact
    packedTile65536 1252473088 1252538624 13 3168 35390 30 _ _ (2094837 / 100000) (52371 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252538624 :
    ThetaLowerSegment 1252538624 1252604160 (12524848196199 / 10000) (31313781176493 / 25000) := by
  exact
    packedTile65536 1252538624 1252604160 13 3171 35391 30 _ _ (1047421 / 50000) (418969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252604160 :
    ThetaLowerSegment 1252604160 1252669696 (31313781176493 / 25000) (31315417776493 / 25000) := by
  exact
    packedTile65536 1252604160 1252669696 13 3125 35392 30 _ _ (65464 / 3125) (2094851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252669696 :
    ThetaLowerSegment 1252669696 1252735232 (31315417776493 / 25000) (62634160084697 / 50000) := by
  exact
    packedTile65536 1252669696 1252735232 13 3174 35393 30 _ _ (2094853 / 100000) (261857 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252735232 :
    ThetaLowerSegment 1252735232 1252800768 (62634160084697 / 50000) (62637390355733 / 50000) := by
  exact
    packedTile65536 1252735232 1252800768 13 3084 35393 30 _ _ (1047429 / 50000) (2094861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252800768 :
    ThetaLowerSegment 1252800768 1252866304 (62637390355733 / 50000) (626407609903 / 500) := by
  exact
    packedTile65536 1252800768 1252866304 13 3218 35394 30 _ _ (2094863 / 100000) (1047433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252866304 :
    ThetaLowerSegment 1252866304 1252931840 (626407609903 / 500) (6264409706759 / 5000) := by
  exact
    packedTile65536 1252866304 1252931840 13 3185 35395 30 _ _ (523717 / 25000) (2094871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252931840 :
    ThetaLowerSegment 1252931840 1252997376 (6264409706759 / 5000) (62647384972333 / 50000) := by
  exact
    packedTile65536 1252931840 1252997376 13 3139 35396 30 _ _ (1047437 / 50000) (2094877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1252997376 :
    ThetaLowerSegment 1252997376 1253062912 (62647384972333 / 50000) (62650720019701 / 50000) := by
  exact
    packedTile65536 1252997376 1253062912 13 3184 35397 30 _ _ (2094879 / 100000) (1047441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253062912 :
    ThetaLowerSegment 1253062912 1253128448 (62650720019701 / 50000) (62654013177349 / 50000) := by
  exact
    packedTile65536 1253062912 1253128448 13 3144 35398 30 _ _ (523721 / 25000) (2094887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253128448 :
    ThetaLowerSegment 1253128448 1253193984 (62654013177349 / 50000)
      (125314635729493 / 100000) := by
  exact
    packedTile65536 1253128448 1253193984 13 3155 35399 30 _ _ (2094889 / 100000) (523723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253193984 :
    ThetaLowerSegment 1253193984 1253259520 (125314635729493 / 100000)
      (125321088006093 / 100000) := by
  exact
    packedTile65536 1253193984 1253259520 13 3080 35400 30 _ _ (418979 / 20000) (1047449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253259520 :
    ThetaLowerSegment 1253259520 1253325056 (125321088006093 / 100000)
      (125327816824893 / 100000) := by
  exact
    packedTile65536 1253259520 1253325056 13 3212 35401 30 _ _ (20949 / 1000) (2094903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253325056 :
    ThetaLowerSegment 1253325056 1253390592 (125327816824893 / 100000)
      (125334440914503 / 100000) := by
  exact
    packedTile65536 1253325056 1253390592 13 3162 35402 30 _ _ (418981 / 20000) (523727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253390592 :
    ThetaLowerSegment 1253390592 1253456128 (125334440914503 / 100000)
      (125340893237303 / 100000) := by
  exact
    packedTile65536 1253390592 1253456128 13 3080 35403 30 _ _ (209491 / 10000) (2094913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253456128 :
    ThetaLowerSegment 1253456128 1253521664 (125340893237303 / 100000)
      (125347425185391 / 100000) := by
  exact
    packedTile65536 1253456128 1253521664 13 3118 35404 30 _ _ (523729 / 25000) (2094919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253521664 :
    ThetaLowerSegment 1253521664 1253587200 (125347425185391 / 100000)
      (62676971242311 / 50000) := by
  exact
    packedTile65536 1253521664 1253587200 13 3111 35405 30 _ _ (2094921 / 100000) (523731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253587200 :
    ThetaLowerSegment 1253587200 1253652736 (62676971242311 / 50000) (31340109712537 / 25000) := by
  exact
    packedTile65536 1253587200 1253652736 13 3101 35406 30 _ _ (1047463 / 50000) (2094929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253652736 :
    ThetaLowerSegment 1253652736 1253718272 (31340109712537 / 25000)
      (125367019028419 / 100000) := by
  exact
    packedTile65536 1253652736 1253718272 13 3141 35406 30 _ _ (2094931 / 100000) (1047467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253718272 :
    ThetaLowerSegment 1253718272 1253783808 (125367019028419 / 100000)
      (125373618076819 / 100000) := by
  exact
    packedTile65536 1253718272 1253783808 13 3150 35407 30 _ _ (261867 / 12500) (2094939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253783808 :
    ThetaLowerSegment 1253783808 1253849344 (125373618076819 / 100000)
      (125380091447599 / 100000) := by
  exact
    packedTile65536 1253783808 1253849344 13 3090 35408 30 _ _ (1047471 / 50000) (418989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253849344 :
    ThetaLowerSegment 1253849344 1253914880 (125380091447599 / 100000)
      (62693344217851 / 50000) := by
  exact
    packedTile65536 1253849344 1253914880 13 3149 35409 30 _ _ (2094947 / 100000) (41899 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253914880 :
    ThetaLowerSegment 1253914880 1253980416 (62693344217851 / 50000) (62696609200543 / 50000) := by
  exact
    packedTile65536 1253914880 1253980416 13 3117 35410 30 _ _ (261869 / 12500) (418991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253980416 :
    ThetaLowerSegment 1253980416 1254045952 (62696609200543 / 50000) (7837477596203 / 6250) := by
  exact
    packedTile65536 1253980416 1254045952 13 3066 35411 30 _ _ (2094957 / 100000) (26187 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254045952 :
    ThetaLowerSegment 1254045952 1254111488 (7837477596203 / 6250) (6270313500109 / 5000) := by
  exact
    packedTile65536 1254045952 1254111488 13 3164 35412 30 _ _ (2094963 / 100000) (1047483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254111488 :
    ThetaLowerSegment 1254111488 1254177024 (6270313500109 / 5000) (31353208384231 / 25000) := by
  exact
    packedTile65536 1254111488 1254177024 13 3133 35413 30 _ _ (261871 / 12500) (2094971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254177024 :
    ThetaLowerSegment 1254177024 1254242560 (31353208384231 / 25000)
      (125419371947657 / 100000) := by
  exact
    packedTile65536 1254177024 1254242560 13 3121 35414 30 _ _ (2094973 / 100000) (65468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254242560 :
    ThetaLowerSegment 1254242560 1254308096 (125419371947657 / 100000)
      (125425979508269 / 100000) := by
  exact
    packedTile65536 1254242560 1254308096 13 3154 35415 30 _ _ (1047489 / 50000) (2094981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254308096 :
    ThetaLowerSegment 1254308096 1254373632 (125425979508269 / 100000) (5017301639801 / 4000) := by
  exact
    packedTile65536 1254308096 1254373632 13 3132 35416 30 _ _ (2094983 / 100000) (1047493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254373632 :
    ThetaLowerSegment 1254373632 1254439168 (5017301639801 / 4000) (2508781756713 / 2000) := by
  exact
    packedTile65536 1254373632 1254439168 13 3125 35417 30 _ _ (2094989 / 100000) (130937 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254439168 :
    ThetaLowerSegment 1254439168 1254504704 (2508781756713 / 2000) (15680718477697 / 12500) := by
  exact
    packedTile65536 1254439168 1254504704 13 3179 35418 30 _ _ (1047497 / 50000) (2094997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254504704 :
    ThetaLowerSegment 1254504704 1254570240 (15680718477697 / 12500)
      (125452324023437 / 100000) := by
  exact
    packedTile65536 1254504704 1254570240 13 3139 35418 30 _ _ (2094999 / 100000) (1047501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254570240 :
    ThetaLowerSegment 1254570240 1254635776 (125452324023437 / 100000)
      (125458818535837 / 100000) := by
  exact
    packedTile65536 1254570240 1254635776 13 3100 35419 30 _ _ (523751 / 25000) (2095007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254635776 :
    ThetaLowerSegment 1254635776 1254701312 (125458818535837 / 100000)
      (125465363347077 / 100000) := by
  exact
    packedTile65536 1254635776 1254701312 13 3124 35420 30 _ _ (209501 / 10000) (2095013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254701312 :
    ThetaLowerSegment 1254701312 1254766848 (125465363347077 / 100000) (3920994577136 / 3125) := by
  exact
    packedTile65536 1254701312 1254766848 13 3085 35421 30 _ _ (419003 / 20000) (1047509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254766848 :
    ThetaLowerSegment 1254766848 1254832384 (3920994577136 / 3125) (15684803222669 / 12500) := by
  exact
    packedTile65536 1254766848 1254832384 13 3150 35422 30 _ _ (104751 / 5000) (2095023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254832384 :
    ThetaLowerSegment 1254832384 1254897920 (15684803222669 / 12500)
      (125485023015077 / 100000) := by
  exact
    packedTile65536 1254832384 1254897920 13 3149 35423 30 _ _ (83801 / 4000) (523757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254897920 :
    ThetaLowerSegment 1254897920 1254963456 (125485023015077 / 100000) (6274577242329 / 5000) := by
  exact
    packedTile65536 1254897920 1254963456 13 3113 35424 30 _ _ (2095031 / 100000) (1047517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1254963456 :
    ThetaLowerSegment 1254963456 1255028992 (6274577242329 / 5000) (7843637548497 / 6250) := by
  exact
    packedTile65536 1254963456 1255028992 13 3177 35425 30 _ _ (523759 / 25000) (2095039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255028992 :
    ThetaLowerSegment 1255028992 1255094528 (7843637548497 / 6250) (125504781299733 / 100000) := by
  exact
    packedTile65536 1255028992 1255094528 13 3141 35426 30 _ _ (2095041 / 100000) (523761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255094528 :
    ThetaLowerSegment 1255094528 1255160064 (125504781299733 / 100000)
      (125511246611689 / 100000) := by
  exact
    packedTile65536 1255094528 1255160064 13 3086 35427 30 _ _ (1047523 / 50000) (2095049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255160064 :
    ThetaLowerSegment 1255160064 1255225600 (125511246611689 / 100000)
      (125517699368769 / 100000) := by
  exact
    packedTile65536 1255160064 1255225600 13 3080 35428 30 _ _ (2095051 / 100000) (1047527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255225600 :
    ThetaLowerSegment 1255225600 1255291136 (125517699368769 / 100000)
      (125524202425697 / 100000) := by
  exact
    packedTile65536 1255225600 1255291136 13 3104 35429 30 _ _ (2095057 / 100000) (104753 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255291136 :
    ThetaLowerSegment 1255291136 1255356672 (125524202425697 / 100000)
      (125530745304323 / 100000) := by
  exact
    packedTile65536 1255291136 1255356672 13 3123 35430 30 _ _ (1047531 / 50000) (419013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255356672 :
    ThetaLowerSegment 1255356672 1255422208 (125530745304323 / 100000)
      (15692143216751 / 12500) := by
  exact
    packedTile65536 1255356672 1255422208 13 3055 35431 30 _ _ (2095067 / 100000) (209507 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255422208 :
    ThetaLowerSegment 1255422208 1255487744 (15692143216751 / 12500) (15692975222219 / 12500) := by
  exact
    packedTile65536 1255422208 1255487744 13 3177 35431 30 _ _ (65471 / 3125) (83803 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255487744 :
    ThetaLowerSegment 1255487744 1255553280 (15692975222219 / 12500) (62775095881301 / 50000) := by
  exact
    packedTile65536 1255487744 1255553280 13 3050 35432 30 _ _ (2095077 / 100000) (52377 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255553280 :
    ThetaLowerSegment 1255553280 1255618816 (62775095881301 / 50000) (62778368400947 / 50000) := by
  exact
    packedTile65536 1255553280 1255618816 13 3124 35433 30 _ _ (2095083 / 100000) (1047543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255618816 :
    ThetaLowerSegment 1255618816 1255684352 (62778368400947 / 50000) (62781667117003 / 50000) := by
  exact
    packedTile65536 1255618816 1255684352 13 3149 35434 30 _ _ (130943 / 6250) (2095091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255684352 :
    ThetaLowerSegment 1255684352 1255749888 (62781667117003 / 50000) (15696244864759 / 12500) := by
  exact
    packedTile65536 1255684352 1255749888 13 3162 35435 30 _ _ (2095093 / 100000) (261887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255749888 :
    ThetaLowerSegment 1255749888 1255815424 (15696244864759 / 12500) (31394120763311 / 25000) := by
  exact
    packedTile65536 1255749888 1255815424 13 3114 35436 30 _ _ (1047549 / 50000) (2095101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255815424 :
    ThetaLowerSegment 1255815424 1255880960 (31394120763311 / 25000) (31395729279407 / 25000) := by
  exact
    packedTile65536 1255815424 1255880960 13 3071 35437 30 _ _ (65472 / 3125) (2095107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255880960 :
    ThetaLowerSegment 1255880960 1255946496 (31395729279407 / 25000) (3924672790051 / 3125) := by
  exact
    packedTile65536 1255880960 1255946496 13 3156 35438 30 _ _ (2095109 / 100000) (261889 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255946496 :
    ThetaLowerSegment 1255946496 1256012032 (3924672790051 / 3125) (12559605975197 / 10000) := by
  exact
    packedTile65536 1255946496 1256012032 13 3117 35439 30 _ _ (1047557 / 50000) (2095117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256012032 :
    ThetaLowerSegment 1256012032 1256077568 (12559605975197 / 10000) (25120500448579 / 20000) := by
  exact
    packedTile65536 1256012032 1256077568 13 3075 35440 30 _ _ (2095119 / 100000) (1047561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256077568 :
    ThetaLowerSegment 1256077568 1256143104 (25120500448579 / 20000)
      (125609036934651 / 100000) := by
  exact
    packedTile65536 1256077568 1256143104 13 3119 35441 30 _ _ (523781 / 25000) (2095127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256143104 :
    ThetaLowerSegment 1256143104 1256208640 (125609036934651 / 100000)
      (125615580025641 / 100000) := by
  exact
    packedTile65536 1256143104 1256208640 13 3123 35442 30 _ _ (209513 / 10000) (2095133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256208640 :
    ThetaLowerSegment 1256208640 1256274176 (125615580025641 / 100000)
      (125622074944141 / 100000) := by
  exact
    packedTile65536 1256208640 1256274176 13 3100 35443 30 _ _ (419027 / 20000) (1047569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256274176 :
    ThetaLowerSegment 1256274176 1256339712 (125622074944141 / 100000)
      (125628764726161 / 100000) := by
  exact
    packedTile65536 1256274176 1256339712 13 3193 35443 30 _ _ (104757 / 5000) (2095143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256339712 :
    ThetaLowerSegment 1256339712 1256405248 (125628764726161 / 100000)
      (62817668598013 / 50000) := by
  exact
    packedTile65536 1256339712 1256405248 13 3137 35444 30 _ _ (419029 / 20000) (523787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256405248 :
    ThetaLowerSegment 1256405248 1256470784 (62817668598013 / 50000) (62820916082063 / 50000) := by
  exact
    packedTile65536 1256405248 1256470784 13 3100 35445 30 _ _ (2095151 / 100000) (1047577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256470784 :
    ThetaLowerSegment 1256470784 1256536320 (62820916082063 / 50000) (12564851361661 / 10000) := by
  exact
    packedTile65536 1256470784 1256536320 13 3189 35446 30 _ _ (523789 / 25000) (2095159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256536320 :
    ThetaLowerSegment 1256536320 1256601856 (12564851361661 / 10000)
      (125655052614091 / 100000) := by
  exact
    packedTile65536 1256536320 1256601856 13 3121 35447 30 _ _ (2095161 / 100000) (523791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256601856 :
    ThetaLowerSegment 1256601856 1256667392 (125655052614091 / 100000)
      (125661562294853 / 100000) := by
  exact
    packedTile65536 1256601856 1256667392 13 3107 35448 30 _ _ (1047583 / 50000) (2095169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256667392 :
    ThetaLowerSegment 1256667392 1256732928 (125661562294853 / 100000) (6283404647143 / 5000) := by
  exact
    packedTile65536 1256667392 1256732928 13 3117 35449 30 _ _ (2095171 / 100000) (1047587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256732928 :
    ThetaLowerSegment 1256732928 1256798464 (6283404647143 / 5000) (125674686464879 / 100000) := by
  exact
    packedTile65536 1256732928 1256798464 13 3147 35450 30 _ _ (2095177 / 100000) (104759 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256798464 :
    ThetaLowerSegment 1256798464 1256864000 (125674686464879 / 100000)
      (125681231813447 / 100000) := by
  exact
    packedTile65536 1256798464 1256864000 13 3124 35451 30 _ _ (1047591 / 50000) (419037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256864000 :
    ThetaLowerSegment 1256864000 1256929536 (125681231813447 / 100000) (7855481752279 / 6250) := by
  exact
    packedTile65536 1256864000 1256929536 13 3091 35452 30 _ _ (2095187 / 100000) (209519 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256929536 :
    ThetaLowerSegment 1256929536 1256995072 (7855481752279 / 6250) (15711768843983 / 12500) := by
  exact
    packedTile65536 1256929536 1256995072 13 3075 35453 30 _ _ (261899 / 12500) (419039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1256995072 :
    ThetaLowerSegment 1256995072 1257060608 (15711768843983 / 12500)
      (125700765288793 / 100000) := by
  exact
    packedTile65536 1256995072 1257060608 13 3157 35454 30 _ _ (2095197 / 100000) (2619 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257060608 :
    ThetaLowerSegment 1257060608 1257126144 (125700765288793 / 100000)
      (125707235275657 / 100000) := by
  exact
    packedTile65536 1257060608 1257126144 13 3088 35455 30 _ _ (2095203 / 100000) (1047603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257126144 :
    ThetaLowerSegment 1257126144 1257191680 (125707235275657 / 100000)
      (125713835180857 / 100000) := by
  exact
    packedTile65536 1257126144 1257191680 13 3150 35455 30 _ _ (261901 / 12500) (2095211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257191680 :
    ThetaLowerSegment 1257191680 1257257216 (125713835180857 / 100000)
      (25144089534617 / 20000) := by
  exact
    packedTile65536 1257191680 1257257216 13 3156 35456 30 _ _ (2095213 / 100000) (130951 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257257216 :
    ThetaLowerSegment 1257257216 1257322752 (25144089534617 / 20000)
      (125726930277577 / 100000) := by
  exact
    packedTile65536 1257257216 1257322752 13 3094 35457 30 _ _ (1047609 / 50000) (2095221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257322752 :
    ThetaLowerSegment 1257322752 1257339136 (125726930277577 / 100000)
      (125728572933193 / 100000) := by
  exact
    packedTile65536 1257322752 1257339136 11 784 35458 30 _ _ (261903 / 12500) (2095227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257339136 :
    ThetaLowerSegment 1257339136 1257341184 (125728572933193 / 100000)
      (15716094402221 / 12500) := by
  exact
    packedTile65536 1257339136 1257341184 8 87 35458 30 _ _ (83809 / 4000) (523807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1225341184_1257341184 :
    ThetaLowerSegment 1225341184 1257341184 (122529402903409 / 100000)
      (15716094402221 / 12500) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1225341184 cell1225406720)
                    (ThetaLowerSegment.join cell1225472256 cell1225537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1225603328 cell1225668864)
                    (ThetaLowerSegment.join cell1225734400 cell1225799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1225865472 cell1225931008)
                    (ThetaLowerSegment.join cell1225996544 cell1226062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1226127616 cell1226193152)
                    (ThetaLowerSegment.join cell1226258688 cell1226324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1226389760 cell1226455296)
                    (ThetaLowerSegment.join cell1226520832 cell1226586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1226651904 cell1226717440)
                    (ThetaLowerSegment.join cell1226782976 cell1226848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1226914048 cell1226979584)
                    (ThetaLowerSegment.join cell1227045120 cell1227110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1227176192 cell1227241728)
                    (ThetaLowerSegment.join cell1227307264 cell1227372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1227438336 cell1227503872)
                    (ThetaLowerSegment.join cell1227569408 cell1227634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1227700480 cell1227766016)
                    (ThetaLowerSegment.join cell1227831552 cell1227897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1227962624 cell1228028160)
                    (ThetaLowerSegment.join cell1228093696 cell1228159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1228224768 cell1228290304)
                    (ThetaLowerSegment.join cell1228355840 cell1228421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1228486912 cell1228552448)
                    (ThetaLowerSegment.join cell1228617984 cell1228683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1228749056 cell1228814592)
                    (ThetaLowerSegment.join cell1228880128 cell1228945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1229011200 cell1229076736)
                    (ThetaLowerSegment.join cell1229142272 cell1229207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1229273344 cell1229338880)
                    (ThetaLowerSegment.join cell1229404416 cell1229469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1229535488 cell1229601024)
                    (ThetaLowerSegment.join cell1229666560 cell1229732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1229797632 cell1229863168)
                    (ThetaLowerSegment.join cell1229928704 cell1229994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1230059776 cell1230125312)
                    (ThetaLowerSegment.join cell1230190848 cell1230256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1230321920 cell1230387456)
                    (ThetaLowerSegment.join cell1230452992 cell1230518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1230584064 cell1230649600)
                    (ThetaLowerSegment.join cell1230715136 cell1230780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1230846208 cell1230911744)
                    (ThetaLowerSegment.join cell1230977280 cell1231042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1231108352 cell1231173888)
                    (ThetaLowerSegment.join cell1231239424 cell1231304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1231370496 cell1231436032)
                    (ThetaLowerSegment.join cell1231501568 cell1231567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1231632640 cell1231698176)
                    (ThetaLowerSegment.join cell1231763712 cell1231829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1231894784 cell1231960320)
                    (ThetaLowerSegment.join cell1232025856 cell1232091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1232156928 cell1232222464)
                    (ThetaLowerSegment.join cell1232288000 cell1232353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1232419072 cell1232484608)
                    (ThetaLowerSegment.join cell1232550144 cell1232615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1232681216 cell1232746752)
                    (ThetaLowerSegment.join cell1232812288 cell1232877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1232943360 cell1233008896)
                    (ThetaLowerSegment.join cell1233074432 cell1233139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1233205504 cell1233271040)
                    (ThetaLowerSegment.join cell1233336576 cell1233402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1233467648 cell1233533184)
                    (ThetaLowerSegment.join cell1233598720 cell1233664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1233729792 cell1233795328)
                    (ThetaLowerSegment.join cell1233860864 cell1233926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1233991936 cell1234057472)
                    (ThetaLowerSegment.join cell1234123008 cell1234188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1234254080 cell1234319616)
                    (ThetaLowerSegment.join cell1234385152 cell1234450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1234516224 cell1234581760)
                    (ThetaLowerSegment.join cell1234647296 cell1234712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1234778368 cell1234843904)
                    (ThetaLowerSegment.join cell1234909440 cell1234974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1235040512 cell1235106048)
                    (ThetaLowerSegment.join cell1235171584 cell1235237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1235302656 cell1235368192)
                    (ThetaLowerSegment.join cell1235433728 cell1235499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1235564800 cell1235630336)
                    (ThetaLowerSegment.join cell1235695872 cell1235761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1235826944 cell1235892480)
                    (ThetaLowerSegment.join cell1235958016 cell1236023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1236089088 cell1236154624)
                    (ThetaLowerSegment.join cell1236220160 cell1236285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1236351232 cell1236416768)
                    (ThetaLowerSegment.join cell1236482304 cell1236547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1236613376 cell1236678912)
                    (ThetaLowerSegment.join cell1236744448 cell1236809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1236875520 cell1236941056)
                    (ThetaLowerSegment.join cell1237006592 cell1237072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1237137664 cell1237203200)
                    (ThetaLowerSegment.join cell1237268736 cell1237334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1237399808 cell1237465344)
                    (ThetaLowerSegment.join cell1237530880 cell1237596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1237661952 cell1237727488)
                    (ThetaLowerSegment.join cell1237793024 cell1237858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1237924096 cell1237989632)
                    (ThetaLowerSegment.join cell1238055168 cell1238120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1238186240 cell1238251776)
                    (ThetaLowerSegment.join cell1238317312 cell1238382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1238448384 cell1238513920)
                    (ThetaLowerSegment.join cell1238579456 cell1238644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1238710528 cell1238776064)
                    (ThetaLowerSegment.join cell1238841600 cell1238907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1238972672 cell1239038208)
                    (ThetaLowerSegment.join cell1239103744 cell1239169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1239234816 cell1239300352)
                    (ThetaLowerSegment.join cell1239365888 cell1239431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1239496960 cell1239562496)
                    (ThetaLowerSegment.join cell1239628032 cell1239693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1239759104 cell1239824640)
                    (ThetaLowerSegment.join cell1239890176 cell1239955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1240021248 cell1240086784)
                    (ThetaLowerSegment.join cell1240152320 cell1240217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1240283392 cell1240348928)
                    (ThetaLowerSegment.join cell1240414464 cell1240480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1240545536 cell1240611072)
                    (ThetaLowerSegment.join cell1240676608 cell1240742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1240807680 cell1240873216)
                    (ThetaLowerSegment.join cell1240938752 cell1241004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1241069824 cell1241135360)
                    (ThetaLowerSegment.join cell1241200896 cell1241266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1241331968 cell1241397504)
                    (ThetaLowerSegment.join cell1241463040 cell1241528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1241594112 cell1241659648)
                    (ThetaLowerSegment.join cell1241725184 cell1241790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1241856256 cell1241921792)
                    (ThetaLowerSegment.join cell1241987328 cell1242052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1242118400 cell1242183936)
                    (ThetaLowerSegment.join cell1242249472 cell1242315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1242380544 cell1242446080)
                    (ThetaLowerSegment.join cell1242511616 cell1242577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1242642688 cell1242708224)
                    (ThetaLowerSegment.join cell1242773760 cell1242839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1242904832 cell1242970368)
                    (ThetaLowerSegment.join cell1243035904 cell1243101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1243166976 cell1243232512)
                    (ThetaLowerSegment.join cell1243298048 cell1243363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1243429120 cell1243494656)
                    (ThetaLowerSegment.join cell1243560192 cell1243625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1243691264 cell1243756800)
                    (ThetaLowerSegment.join cell1243822336 cell1243887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1243953408 cell1244018944)
                    (ThetaLowerSegment.join cell1244084480 cell1244150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1244215552 cell1244281088)
                    (ThetaLowerSegment.join cell1244346624 cell1244412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1244477696 cell1244543232)
                    (ThetaLowerSegment.join cell1244608768 cell1244674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1244739840 cell1244805376)
                    (ThetaLowerSegment.join cell1244870912 cell1244936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1245001984 cell1245067520)
                    (ThetaLowerSegment.join cell1245133056 cell1245198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1245264128 cell1245329664)
                    (ThetaLowerSegment.join cell1245395200 cell1245460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1245526272 cell1245591808)
                    (ThetaLowerSegment.join cell1245657344 cell1245722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1245788416 cell1245853952)
                    (ThetaLowerSegment.join cell1245919488 cell1245985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1246050560 cell1246116096)
                    (ThetaLowerSegment.join cell1246181632 cell1246247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1246312704 cell1246378240)
                    (ThetaLowerSegment.join cell1246443776 cell1246509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1246574848 cell1246640384)
                    (ThetaLowerSegment.join cell1246705920 cell1246771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1246836992 cell1246902528)
                    (ThetaLowerSegment.join cell1246968064 cell1247033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1247099136 cell1247164672)
                    (ThetaLowerSegment.join cell1247230208 cell1247295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1247361280 cell1247426816)
                    (ThetaLowerSegment.join cell1247492352 cell1247557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1247623424 cell1247688960)
                    (ThetaLowerSegment.join cell1247754496 cell1247820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1247885568 cell1247951104)
                    (ThetaLowerSegment.join cell1248016640 cell1248082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1248147712 cell1248213248)
                    (ThetaLowerSegment.join cell1248278784 cell1248344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1248409856 cell1248475392)
                    (ThetaLowerSegment.join cell1248540928 cell1248606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1248672000 cell1248737536)
                    (ThetaLowerSegment.join cell1248803072 cell1248868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1248934144 cell1248999680)
                    (ThetaLowerSegment.join cell1249065216 cell1249130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1249196288 cell1249261824)
                    (ThetaLowerSegment.join cell1249327360 cell1249392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1249458432 cell1249523968)
                    (ThetaLowerSegment.join cell1249589504 cell1249655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1249720576 cell1249786112)
                    (ThetaLowerSegment.join cell1249851648 cell1249917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1249982720 cell1250048256)
                    (ThetaLowerSegment.join cell1250113792 cell1250179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1250244864 cell1250310400)
                    (ThetaLowerSegment.join cell1250375936 cell1250441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1250507008 cell1250572544)
                    (ThetaLowerSegment.join cell1250638080 cell1250703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1250769152 cell1250834688)
                    (ThetaLowerSegment.join cell1250900224 cell1250965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1251031296 cell1251096832)
                    (ThetaLowerSegment.join cell1251162368 cell1251227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1251293440 cell1251358976)
                    (ThetaLowerSegment.join cell1251424512 cell1251490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1251555584 cell1251621120)
                    (ThetaLowerSegment.join cell1251686656 cell1251752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1251817728 cell1251883264)
                    (ThetaLowerSegment.join cell1251948800 cell1252014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1252079872 cell1252145408)
                    (ThetaLowerSegment.join cell1252210944 cell1252276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1252342016 cell1252407552)
                    (ThetaLowerSegment.join cell1252473088 cell1252538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1252604160 cell1252669696)
                    (ThetaLowerSegment.join cell1252735232 cell1252800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1252866304 cell1252931840)
                    (ThetaLowerSegment.join cell1252997376 cell1253062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1253128448 cell1253193984)
                    (ThetaLowerSegment.join cell1253259520 cell1253325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1253390592 cell1253456128)
                    (ThetaLowerSegment.join cell1253521664 cell1253587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1253652736 cell1253718272)
                    (ThetaLowerSegment.join cell1253783808 cell1253849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1253914880 cell1253980416)
                    (ThetaLowerSegment.join cell1254045952 cell1254111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1254177024 cell1254242560)
                    (ThetaLowerSegment.join cell1254308096 cell1254373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1254439168 cell1254504704)
                    (ThetaLowerSegment.join cell1254570240 cell1254635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1254701312 cell1254766848)
                    (ThetaLowerSegment.join cell1254832384 cell1254897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1254963456 cell1255028992)
                    (ThetaLowerSegment.join cell1255094528 cell1255160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1255225600 cell1255291136)
                    (ThetaLowerSegment.join cell1255356672 cell1255422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1255487744 cell1255553280)
                    (ThetaLowerSegment.join cell1255618816 cell1255684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1255749888 cell1255815424)
                    (ThetaLowerSegment.join cell1255880960 cell1255946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1256012032 cell1256077568)
                    (ThetaLowerSegment.join cell1256143104 cell1256208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1256274176 cell1256339712)
                    (ThetaLowerSegment.join cell1256405248 cell1256470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1256536320 cell1256601856)
                    (ThetaLowerSegment.join cell1256667392 cell1256732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1256798464 cell1256864000)
                  (ThetaLowerSegment.join cell1256929536 cell1256995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1257060608 cell1257126144)
                  (ThetaLowerSegment.join cell1257191680 cell1257257216)))
              (ThetaLowerSegment.join cell1257322752 cell1257339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
