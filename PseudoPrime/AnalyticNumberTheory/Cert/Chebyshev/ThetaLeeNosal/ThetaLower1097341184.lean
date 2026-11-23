/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1097341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1065341184 :
    ThetaLowerSegment 1065341184 1065406720 (13316273891833 / 12500)
      (106536728504639 / 100000) := by
  exact
    packedTile32768 1065341184 1065406720 13 3145 32639 30 _ _ (415731 / 20000) (1039329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065406720 :
    ThetaLowerSegment 1065406720 1065472256 (106536728504639 / 100000)
      (21308670223717 / 20000) := by
  exact
    packedTile32768 1065406720 1065472256 13 3186 32640 30 _ _ (2078661 / 100000) (259833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065472256 :
    ThetaLowerSegment 1065472256 1065537792 (21308670223717 / 20000)
      (106549782514283 / 100000) := by
  exact
    packedTile32768 1065472256 1065537792 13 3094 32641 30 _ _ (2078667 / 100000) (207867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065537792 :
    ThetaLowerSegment 1065537792 1065603328 (106549782514283 / 100000)
      (53278178678491 / 50000) := by
  exact
    packedTile32768 1065537792 1065603328 13 3163 32642 30 _ _ (2078673 / 100000) (519669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065603328 :
    ThetaLowerSegment 1065603328 1065668864 (53278178678491 / 50000) (21312579791959 / 20000) := by
  exact
    packedTile32768 1065603328 1065668864 13 3147 32643 30 _ _ (2078679 / 100000) (1039341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065668864 :
    ThetaLowerSegment 1065668864 1065734400 (21312579791959 / 20000) (10656949878467 / 10000) := by
  exact
    packedTile32768 1065668864 1065734400 13 3175 32644 30 _ _ (415737 / 20000) (64959 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065734400 :
    ThetaLowerSegment 1065734400 1065799936 (10656949878467 / 10000) (21315219725719 / 20000) := by
  exact
    packedTile32768 1065734400 1065799936 13 3175 32645 30 _ _ (2078691 / 100000) (1039347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065799936 :
    ThetaLowerSegment 1065799936 1065865472 (21315219725719 / 20000) (4263306692571 / 4000) := by
  exact
    packedTile32768 1065799936 1065865472 13 3160 32646 30 _ _ (1039349 / 50000) (2078701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065865472 :
    ThetaLowerSegment 1065865472 1065931008 (4263306692571 / 4000) (106589283829107 / 100000) := by
  exact
    packedTile32768 1065865472 1065931008 13 3183 32647 30 _ _ (129919 / 6250) (2078707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065931008 :
    ThetaLowerSegment 1065931008 1065996544 (106589283829107 / 100000)
      (106595686255907 / 100000) := by
  exact
    packedTile32768 1065931008 1065996544 13 3080 32648 30 _ _ (207871 / 10000) (2078713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065996544 :
    ThetaLowerSegment 1065996544 1066062080 (106595686255907 / 100000)
      (106602246683603 / 100000) := by
  exact
    packedTile32768 1065996544 1066062080 13 3156 32649 30 _ _ (519679 / 25000) (2078719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066062080 :
    ThetaLowerSegment 1066062080 1066127616 (106602246683603 / 100000)
      (106608950562053 / 100000) := by
  exact
    packedTile32768 1066062080 1066127616 13 3225 32650 30 _ _ (1039361 / 50000) (83149 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066127616 :
    ThetaLowerSegment 1066127616 1066193152 (106608950562053 / 100000)
      (106615594176741 / 100000) := by
  exact
    packedTile32768 1066127616 1066193152 13 3196 32651 30 _ _ (259841 / 12500) (2078731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066193152 :
    ThetaLowerSegment 1066193152 1066258688 (106615594176741 / 100000)
      (53311101237653 / 50000) := by
  exact
    packedTile32768 1066193152 1066258688 13 3179 32652 30 _ _ (415747 / 20000) (1039369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066258688 :
    ThetaLowerSegment 1066258688 1066324224 (53311101237653 / 50000) (53314373175987 / 50000) := by
  exact
    packedTile32768 1066258688 1066324224 13 3148 32653 30 _ _ (2078741 / 100000) (259843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066324224 :
    ThetaLowerSegment 1066324224 1066389760 (53314373175987 / 50000) (26658850624967 / 25000) := by
  exact
    packedTile32768 1066324224 1066389760 13 3202 32654 30 _ _ (2078747 / 100000) (1663 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066389760 :
    ThetaLowerSegment 1066389760 1066455296 (26658850624967 / 25000) (53320950340873 / 50000) := by
  exact
    packedTile32768 1066389760 1066455296 13 3126 32655 30 _ _ (2078753 / 100000) (519689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066455296 :
    ThetaLowerSegment 1066455296 1066520832 (53320950340873 / 50000)
      (106648529844197 / 100000) := by
  exact
    packedTile32768 1066455296 1066520832 13 3189 32656 30 _ _ (2078759 / 100000) (1039381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066520832 :
    ThetaLowerSegment 1066520832 1066586368 (106648529844197 / 100000)
      (106654990645817 / 100000) := by
  exact
    packedTile32768 1066520832 1066586368 13 3108 32657 30 _ _ (415753 / 20000) (129923 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066586368 :
    ThetaLowerSegment 1066586368 1066651904 (106654990645817 / 100000)
      (21332311080927 / 20000) := by
  exact
    packedTile32768 1066586368 1066651904 13 3158 32658 30 _ _ (2078771 / 100000) (1039387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066651904 :
    ThetaLowerSegment 1066651904 1066717440 (21332311080927 / 20000) (21333616553511 / 20000) := by
  exact
    packedTile32768 1066651904 1066717440 13 3140 32659 30 _ _ (1039389 / 50000) (2078781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066717440 :
    ThetaLowerSegment 1066717440 1066782976 (21333616553511 / 20000)
      (106674647567427 / 100000) := by
  exact
    packedTile32768 1066717440 1066782976 13 3158 32660 30 _ _ (64962 / 3125) (2078787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066782976 :
    ThetaLowerSegment 1066782976 1066848512 (106674647567427 / 100000)
      (106681305931797 / 100000) := by
  exact
    packedTile32768 1066782976 1066848512 13 3203 32661 30 _ _ (207879 / 10000) (2078793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066848512 :
    ThetaLowerSegment 1066848512 1066914048 (106681305931797 / 100000) (4267515662301 / 4000) := by
  exact
    packedTile32768 1066848512 1066914048 13 3168 32662 30 _ _ (519699 / 25000) (2078799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066914048 :
    ThetaLowerSegment 1066914048 1066979584 (4267515662301 / 4000) (106694416917003 / 100000) := by
  exact
    packedTile32768 1066914048 1066979584 13 3139 32663 30 _ _ (1039401 / 50000) (415761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1066979584 :
    ThetaLowerSegment 1066979584 1067045120 (106694416917003 / 100000)
      (106700854985379 / 100000) := by
  exact
    packedTile32768 1066979584 1067045120 13 3097 32664 30 _ _ (259851 / 12500) (2078811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067045120 :
    ThetaLowerSegment 1067045120 1067110656 (106700854985379 / 100000)
      (106707436510503 / 100000) := by
  exact
    packedTile32768 1067045120 1067110656 13 3166 32665 30 _ _ (1039407 / 50000) (2078817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067110656 :
    ThetaLowerSegment 1067110656 1067176192 (106707436510503 / 100000)
      (106714047161283 / 100000) := by
  exact
    packedTile32768 1067110656 1067176192 13 3180 32666 30 _ _ (2078821 / 100000) (259853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067176192 :
    ThetaLowerSegment 1067176192 1067241728 (106714047161283 / 100000)
      (10672057675689 / 10000) := by
  exact
    packedTile32768 1067176192 1067241728 13 3141 32667 30 _ _ (2078827 / 100000) (207883 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067241728 :
    ThetaLowerSegment 1067241728 1067307264 (10672057675689 / 10000) (10672710429251 / 10000) := by
  exact
    packedTile32768 1067241728 1067307264 13 3140 32668 30 _ _ (2078833 / 100000) (519709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067307264 :
    ThetaLowerSegment 1067307264 1067372800 (10672710429251 / 10000) (21346736763589 / 20000) := by
  exact
    packedTile32768 1067307264 1067372800 13 3165 32669 30 _ _ (2078839 / 100000) (1039421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067372800 :
    ThetaLowerSegment 1067372800 1067438336 (21346736763589 / 20000) (21348078865921 / 20000) := by
  exact
    packedTile32768 1067372800 1067438336 13 3228 32670 30 _ _ (415769 / 20000) (64964 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067438336 :
    ThetaLowerSegment 1067438336 1067503872 (21348078865921 / 20000) (6671685348601 / 6250) := by
  exact
    packedTile32768 1067438336 1067503872 13 3161 32671 30 _ _ (2078851 / 100000) (1039427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067503872 :
    ThetaLowerSegment 1067503872 1067569408 (6671685348601 / 6250) (106753561790877 / 100000) := by
  exact
    packedTile32768 1067503872 1067569408 13 3173 32672 30 _ _ (2078857 / 100000) (103943 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067569408 :
    ThetaLowerSegment 1067569408 1067634944 (106753561790877 / 100000)
      (106760112291341 / 100000) := by
  exact
    packedTile32768 1067569408 1067634944 13 3151 32673 30 _ _ (129929 / 6250) (2078867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067634944 :
    ThetaLowerSegment 1067634944 1067700480 (106760112291341 / 100000)
      (106766685678281 / 100000) := by
  exact
    packedTile32768 1067634944 1067700480 13 3162 32674 30 _ _ (207887 / 10000) (2078873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067700480 :
    ThetaLowerSegment 1067700480 1067766016 (106766685678281 / 100000)
      (106773271557449 / 100000) := by
  exact
    packedTile32768 1067700480 1067766016 13 3168 32675 30 _ _ (519719 / 25000) (2078879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067766016 :
    ThetaLowerSegment 1067766016 1067831552 (106773271557449 / 100000)
      (106779780536991 / 100000) := by
  exact
    packedTile32768 1067766016 1067831552 13 3131 32676 30 _ _ (1039441 / 50000) (415777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067831552 :
    ThetaLowerSegment 1067831552 1067897088 (106779780536991 / 100000)
      (21357256659731 / 20000) := by
  exact
    packedTile32768 1067831552 1067897088 13 3128 32677 30 _ _ (259861 / 12500) (2078891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067897088 :
    ThetaLowerSegment 1067897088 1067962624 (21357256659731 / 20000) (21358580915209 / 20000) := by
  exact
    packedTile32768 1067897088 1067962624 13 3185 32678 30 _ _ (1039447 / 50000) (2078897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067962624 :
    ThetaLowerSegment 1067962624 1068028160 (21358580915209 / 20000) (21359898937809 / 20000) := by
  exact
    packedTile32768 1067962624 1068028160 13 3170 32679 30 _ _ (20789 / 1000) (2078903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068028160 :
    ThetaLowerSegment 1068028160 1068093696 (21359898937809 / 20000) (21361198254059 / 20000) := by
  exact
    packedTile32768 1068028160 1068093696 13 3125 32680 30 _ _ (1039453 / 50000) (2078909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068093696 :
    ThetaLowerSegment 1068093696 1068159232 (21361198254059 / 20000)
      (106812564793201 / 100000) := by
  exact
    packedTile32768 1068093696 1068159232 13 3162 32681 30 _ _ (2078913 / 100000) (519729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068159232 :
    ThetaLowerSegment 1068159232 1068224768 (106812564793201 / 100000)
      (106819196544811 / 100000) := by
  exact
    packedTile32768 1068159232 1068224768 13 3190 32682 30 _ _ (2078919 / 100000) (1039461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068224768 :
    ThetaLowerSegment 1068224768 1068290304 (106819196544811 / 100000)
      (53412894407993 / 50000) := by
  exact
    packedTile32768 1068224768 1068290304 13 3171 32683 30 _ _ (83157 / 4000) (129933 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068290304 :
    ThetaLowerSegment 1068290304 1068355840 (53412894407993 / 50000)
      (106832256370327 / 100000) := by
  exact
    packedTile32768 1068290304 1068355840 13 3111 32684 30 _ _ (2078931 / 100000) (1039467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068355840 :
    ThetaLowerSegment 1068355840 1068421376 (106832256370327 / 100000)
      (26709692419987 / 25000) := by
  exact
    packedTile32768 1068355840 1068421376 13 3133 32685 30 _ _ (2078937 / 100000) (103947 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068421376 :
    ThetaLowerSegment 1068421376 1068486912 (26709692419987 / 25000)
      (106845283008367 / 100000) := by
  exact
    packedTile32768 1068421376 1068486912 13 3133 32686 30 _ _ (2078943 / 100000) (1039473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068486912 :
    ThetaLowerSegment 1068486912 1068552448 (106845283008367 / 100000)
      (106851848329309 / 100000) := by
  exact
    packedTile32768 1068486912 1068552448 13 3158 32687 30 _ _ (2078949 / 100000) (259869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068552448 :
    ThetaLowerSegment 1068552448 1068617984 (106851848329309 / 100000)
      (106858519699113 / 100000) := by
  exact
    packedTile32768 1068552448 1068617984 13 3209 32688 30 _ _ (519739 / 25000) (2078959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068617984 :
    ThetaLowerSegment 1068617984 1068683520 (106858519699113 / 100000)
      (106865105850729 / 100000) := by
  exact
    packedTile32768 1068617984 1068683520 13 3168 32689 30 _ _ (1039481 / 50000) (415793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068683520 :
    ThetaLowerSegment 1068683520 1068749056 (106865105850729 / 100000)
      (106871748153489 / 100000) := by
  exact
    packedTile32768 1068683520 1068749056 13 3195 32690 30 _ _ (259871 / 12500) (2078971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068749056 :
    ThetaLowerSegment 1068749056 1068880128 (106871748153489 / 100000)
      (21376945853429 / 20000) := by
  exact
    packedTile32768 1068749056 1068880128 14 6244 32691 30 _ _ (1039487 / 50000) (2078977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068880128 :
    ThetaLowerSegment 1068880128 1068945664 (21376945853429 / 20000)
      (106891352916541 / 100000) := by
  exact
    packedTile32768 1068880128 1068945664 13 3186 32693 30 _ _ (1039493 / 50000) (2078989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1068945664 :
    ThetaLowerSegment 1068945664 1069076736 (106891352916541 / 100000)
      (106904448487149 / 100000) := by
  exact
    packedTile32768 1068945664 1069076736 14 6299 32694 30 _ _ (129937 / 6250) (415799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069076736 :
    ThetaLowerSegment 1069076736 1069207808 (106904448487149 / 100000)
      (106917500480539 / 100000) := by
  exact
    packedTile32768 1069076736 1069207808 14 6278 32696 30 _ _ (415801 / 20000) (64969 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069207808 :
    ThetaLowerSegment 1069207808 1069273344 (106917500480539 / 100000)
      (53462029889587 / 50000) := by
  exact
    packedTile32768 1069207808 1069273344 13 3155 32698 30 _ _ (2079017 / 100000) (103951 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069273344 :
    ThetaLowerSegment 1069273344 1069338880 (53462029889587 / 50000) (1336634479891 / 1250) := by
  exact
    packedTile32768 1069273344 1069338880 13 3222 32699 30 _ _ (2079023 / 100000) (1039513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069338880 :
    ThetaLowerSegment 1069338880 1069469952 (1336634479891 / 1250) (53471909425729 / 50000) := by
  exact
    packedTile32768 1069338880 1069469952 14 6282 32700 30 _ _ (2079029 / 100000) (259879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069469952 :
    ThetaLowerSegment 1069469952 1069601024 (53471909425729 / 50000) (4278275591289 / 4000) := by
  exact
    packedTile32768 1069469952 1069601024 14 6287 32702 30 _ _ (2079041 / 100000) (519761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069601024 :
    ThetaLowerSegment 1069601024 1069732096 (4278275591289 / 4000) (106969827735267 / 100000) := by
  exact
    packedTile32768 1069601024 1069732096 14 6223 32704 30 _ _ (1039527 / 50000) (2079057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069732096 :
    ThetaLowerSegment 1069732096 1069797632 (106969827735267 / 100000)
      (106976503616193 / 100000) := by
  exact
    packedTile32768 1069732096 1069797632 13 3211 32706 30 _ _ (1039533 / 50000) (2079069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069797632 :
    ThetaLowerSegment 1069797632 1069863168 (106976503616193 / 100000)
      (106982959134753 / 100000) := by
  exact
    packedTile32768 1069797632 1069863168 13 3105 32707 30 _ _ (64971 / 3125) (83163 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069863168 :
    ThetaLowerSegment 1069863168 1069928704 (106982959134753 / 100000)
      (106989612184353 / 100000) := by
  exact
    packedTile32768 1069863168 1069928704 13 3200 32708 30 _ _ (1039539 / 50000) (2079081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069928704 :
    ThetaLowerSegment 1069928704 1069994240 (106989612184353 / 100000)
      (21399223111821 / 20000) := by
  exact
    packedTile32768 1069928704 1069994240 13 3128 32709 30 _ _ (519771 / 25000) (2079087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069994240 :
    ThetaLowerSegment 1069994240 1070059776 (21399223111821 / 20000) (21400520879799 / 20000) := by
  exact
    packedTile32768 1069994240 1070059776 13 3121 32710 30 _ _ (207909 / 10000) (2079093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070059776 :
    ThetaLowerSegment 1070059776 1070125312 (21400520879799 / 20000) (5350457157953 / 5000) := by
  exact
    packedTile32768 1070059776 1070125312 13 3145 32711 30 _ _ (2079097 / 100000) (20791 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070125312 :
    ThetaLowerSegment 1070125312 1070190848 (5350457157953 / 5000) (4280628109161 / 4000) := by
  exact
    packedTile32768 1070125312 1070190848 13 3155 32712 30 _ _ (2079103 / 100000) (1039553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070190848 :
    ThetaLowerSegment 1070190848 1070256384 (4280628109161 / 4000) (26755551025717 / 25000) := by
  exact
    packedTile32768 1070190848 1070256384 13 3127 32713 30 _ _ (2079109 / 100000) (259889 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070256384 :
    ThetaLowerSegment 1070256384 1070321920 (26755551025717 / 25000)
      (107028838558833 / 100000) := by
  exact
    packedTile32768 1070256384 1070321920 13 3191 32714 30 _ _ (415823 / 20000) (1039559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070321920 :
    ThetaLowerSegment 1070321920 1070387456 (107028838558833 / 100000)
      (53517771862029 / 50000) := by
  exact
    packedTile32768 1070321920 1070387456 13 3225 32715 30 _ _ (2079121 / 100000) (519781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070387456 :
    ThetaLowerSegment 1070387456 1070518528 (53517771862029 / 50000)
      (107048606878999 / 100000) := by
  exact
    packedTile32768 1070387456 1070518528 14 6283 32716 30 _ _ (2079127 / 100000) (207913 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070518528 :
    ThetaLowerSegment 1070518528 1070649600 (107048606878999 / 100000)
      (53530812184139 / 50000) := by
  exact
    packedTile32768 1070518528 1070649600 14 6261 32718 30 _ _ (2079139 / 100000) (1039571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070649600 :
    ThetaLowerSegment 1070649600 1070715136 (53530812184139 / 50000) (10706837329567 / 10000) := by
  exact
    packedTile32768 1070649600 1070715136 13 3246 32720 30 _ _ (129947 / 6250) (415831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070715136 :
    ThetaLowerSegment 1070715136 1070846208 (10706837329567 / 10000) (53540706887323 / 50000) := by
  exact
    packedTile32768 1070715136 1070846208 14 6272 32721 30 _ _ (1039579 / 50000) (2079161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070846208 :
    ThetaLowerSegment 1070846208 1070977280 (53540706887323 / 50000) (26773683754209 / 25000) := by
  exact
    packedTile32768 1070846208 1070977280 14 6407 32723 30 _ _ (207917 / 10000) (2079173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1070977280 :
    ThetaLowerSegment 1070977280 1071108352 (26773683754209 / 25000) (53553936683947 / 50000) := by
  exact
    packedTile32768 1070977280 1071108352 14 6319 32725 30 _ _ (1039591 / 50000) (415837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071108352 :
    ThetaLowerSegment 1071108352 1071239424 (53553936683947 / 50000) (53560525649733 / 50000) := by
  exact
    packedTile32768 1071108352 1071239424 14 6338 32727 30 _ _ (1039597 / 50000) (2079197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071239424 :
    ThetaLowerSegment 1071239424 1071370496 (53560525649733 / 50000)
      (107134035947181 / 100000) := by
  exact
    packedTile32768 1071239424 1071370496 14 6245 32729 30 _ _ (2079207 / 100000) (207921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071370496 :
    ThetaLowerSegment 1071370496 1071501568 (107134035947181 / 100000)
      (107147247304707 / 100000) := by
  exact
    packedTile32768 1071370496 1071501568 14 6354 32731 30 _ _ (2079219 / 100000) (1039611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071501568 :
    ThetaLowerSegment 1071501568 1071632640 (107147247304707 / 100000) (3348759202476 / 3125) := by
  exact
    packedTile32768 1071501568 1071632640 14 6275 32733 30 _ _ (2079231 / 100000) (1039617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071632640 :
    ThetaLowerSegment 1071632640 1071763712 (3348759202476 / 3125) (13396689808089 / 12500) := by
  exact
    packedTile32768 1071632640 1071763712 14 6360 32735 30 _ _ (2079243 / 100000) (1039623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071763712 :
    ThetaLowerSegment 1071763712 1071894784 (13396689808089 / 12500) (13398333459957 / 12500) := by
  exact
    packedTile32768 1071763712 1071894784 14 6324 32737 30 _ _ (259907 / 12500) (2079259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071894784 :
    ThetaLowerSegment 1071894784 1072025856 (13398333459957 / 12500) (26799905899641 / 25000) := by
  exact
    packedTile32768 1071894784 1072025856 14 6231 32739 30 _ _ (519817 / 25000) (2079271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072025856 :
    ThetaLowerSegment 1072025856 1072156928 (26799905899641 / 25000) (26803217672861 / 25000) := by
  exact
    packedTile32768 1072025856 1072156928 14 6371 32741 30 _ _ (25991 / 1250) (2079283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072156928 :
    ThetaLowerSegment 1072156928 1072288000 (26803217672861 / 25000) (26806471764841 / 25000) := by
  exact
    packedTile32768 1072156928 1072288000 14 6260 32743 30 _ _ (519823 / 25000) (415859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072288000 :
    ThetaLowerSegment 1072288000 1072419072 (26806471764841 / 25000) (13404871255803 / 12500) := by
  exact
    packedTile32768 1072288000 1072419072 14 6292 32745 30 _ _ (415861 / 20000) (519827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072419072 :
    ThetaLowerSegment 1072419072 1072550144 (13404871255803 / 12500)
      (107252067664207 / 100000) := by
  exact
    packedTile32768 1072419072 1072550144 14 6299 32747 30 _ _ (2079317 / 100000) (51983 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072550144 :
    ThetaLowerSegment 1072550144 1072681216 (107252067664207 / 100000) (5363255980617 / 5000) := by
  exact
    packedTile32768 1072550144 1072681216 14 6277 32749 30 _ _ (2079329 / 100000) (519833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072681216 :
    ThetaLowerSegment 1072681216 1072812288 (5363255980617 / 5000) (3352448516827 / 3125) := by
  exact
    packedTile32768 1072681216 1072812288 14 6364 32751 30 _ _ (2079341 / 100000) (129959 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072812288 :
    ThetaLowerSegment 1072812288 1072943360 (3352448516827 / 3125) (53645682564769 / 50000) := by
  exact
    packedTile32768 1072812288 1072943360 14 6258 32753 30 _ _ (2079353 / 100000) (519839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1072943360 :
    ThetaLowerSegment 1072943360 1073074432 (53645682564769 / 50000) (536521878613 / 500) := by
  exact
    packedTile32768 1072943360 1073074432 14 6257 32755 30 _ _ (1039683 / 50000) (2079369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073074432 :
    ThetaLowerSegment 1073074432 1073205504 (536521878613 / 500) (26829403260737 / 25000) := by
  exact
    packedTile32768 1073074432 1073205504 14 6366 32757 30 _ _ (1039689 / 50000) (2079381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073205504 :
    ThetaLowerSegment 1073205504 1073336576 (26829403260737 / 25000) (26832672061817 / 25000) := by
  exact
    packedTile32768 1073205504 1073336576 14 6288 32759 30 _ _ (207939 / 10000) (2079393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073336576 :
    ThetaLowerSegment 1073336576 1073467648 (26832672061817 / 25000) (53671876565017 / 50000) := by
  exact
    packedTile32768 1073336576 1073467648 14 6283 32761 30 _ _ (1039701 / 50000) (415881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073467648 :
    ThetaLowerSegment 1073467648 1073598720 (53671876565017 / 50000) (3354897901202 / 3125) := by
  exact
    packedTile32768 1073467648 1073598720 14 6242 32763 30 _ _ (415883 / 20000) (1039709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073598720 :
    ThetaLowerSegment 1073598720 1073729792 (3354897901202 / 3125) (53684910376001 / 50000) := by
  exact
    packedTile32768 1073598720 1073729792 14 6294 32765 30 _ _ (2079427 / 100000) (207943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073729792 :
    ThetaLowerSegment 1073729792 1073860864 (53684910376001 / 50000) (53691460608851 / 50000) := by
  exact
    packedTile65536 1073729792 1073860864 14 6300 32767 30 _ _ (2079439 / 100000) (1039721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073860864 :
    ThetaLowerSegment 1073860864 1073991936 (53691460608851 / 50000)
      (107395815893353 / 100000) := by
  exact
    packedTile65536 1073860864 1073991936 14 6201 32769 30 _ _ (2079451 / 100000) (1039727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073991936 :
    ThetaLowerSegment 1073991936 1074057472 (107395815893353 / 100000)
      (26850624301993 / 25000) := by
  exact
    packedTile65536 1073991936 1074057472 13 3213 32771 30 _ _ (2079463 / 100000) (1039733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074057472 :
    ThetaLowerSegment 1074057472 1074188544 (26850624301993 / 25000)
      (107415678961963 / 100000) := by
  exact
    packedTile65536 1074057472 1074188544 14 6339 32772 30 _ _ (2079469 / 100000) (129967 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074188544 :
    ThetaLowerSegment 1074188544 1074319616 (107415678961963 / 100000)
      (107428966851943 / 100000) := by
  exact
    packedTile65536 1074188544 1074319616 14 6390 32774 30 _ _ (1039741 / 50000) (415897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074319616 :
    ThetaLowerSegment 1074319616 1074450688 (107428966851943 / 100000)
      (107442069743637 / 100000) := by
  exact
    packedTile65536 1074319616 1074450688 14 6301 32776 30 _ _ (1039747 / 50000) (2079497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074450688 :
    ThetaLowerSegment 1074450688 1074581760 (107442069743637 / 100000) (4298204579391 / 4000) := by
  exact
    packedTile65536 1074450688 1074581760 14 6273 32778 30 _ _ (1039753 / 50000) (2079509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074581760 :
    ThetaLowerSegment 1074581760 1074712832 (4298204579391 / 4000) (21493638930599 / 20000) := by
  exact
    packedTile65536 1074581760 1074712832 14 6290 32780 30 _ _ (1039759 / 50000) (2079521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074712832 :
    ThetaLowerSegment 1074712832 1074843904 (21493638930599 / 20000) (21496254147527 / 20000) := by
  exact
    packedTile65536 1074712832 1074843904 14 6288 32782 30 _ _ (207953 / 10000) (2079533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074843904 :
    ThetaLowerSegment 1074843904 1074974976 (21496254147527 / 20000)
      (107494317790417 / 100000) := by
  exact
    packedTile65536 1074843904 1074974976 14 6274 32784 30 _ _ (2079543 / 100000) (1039773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1074974976 :
    ThetaLowerSegment 1074974976 1075106048 (107494317790417 / 100000)
      (53753687658131 / 50000) := by
  exact
    packedTile65536 1074974976 1075106048 14 6279 32786 30 _ _ (415911 / 20000) (1039779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075106048 :
    ThetaLowerSegment 1075106048 1075237120 (53753687658131 / 50000)
      (107520416280919 / 100000) := by
  exact
    packedTile65536 1075106048 1075237120 14 6271 32788 30 _ _ (2079567 / 100000) (207957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075237120 :
    ThetaLowerSegment 1075237120 1075302656 (107520416280919 / 100000)
      (107526867134977 / 100000) := by
  exact
    packedTile65536 1075237120 1075302656 13 3102 32790 30 _ _ (2079579 / 100000) (1039791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075302656 :
    ThetaLowerSegment 1075302656 1075368192 (107526867134977 / 100000)
      (53766749465771 / 50000) := by
  exact
    packedTile65536 1075302656 1075368192 13 3189 32791 30 _ _ (415917 / 20000) (519897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075368192 :
    ThetaLowerSegment 1075368192 1075433728 (53766749465771 / 50000)
      (107539960220779 / 100000) := by
  exact
    packedTile65536 1075368192 1075433728 13 3107 32792 30 _ _ (2079591 / 100000) (1039797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075433728 :
    ThetaLowerSegment 1075433728 1075499264 (107539960220779 / 100000)
      (53773281470627 / 50000) := by
  exact
    packedTile65536 1075433728 1075499264 13 3175 32793 30 _ _ (2079597 / 100000) (5199 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075499264 :
    ThetaLowerSegment 1075499264 1075564800 (53773281470627 / 50000) (53776543329501 / 50000) := by
  exact
    packedTile65536 1075499264 1075564800 13 3137 32794 30 _ _ (519901 / 25000) (2079607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075564800 :
    ThetaLowerSegment 1075564800 1075630336 (53776543329501 / 50000) (26889927554213 / 25000) := by
  exact
    packedTile65536 1075564800 1075630336 13 3185 32795 30 _ _ (207961 / 10000) (2079613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075630336 :
    ThetaLowerSegment 1075630336 1075695872 (26889927554213 / 25000) (5378304523937 / 5000) := by
  exact
    packedTile65536 1075630336 1075695872 13 3068 32796 30 _ _ (64988 / 3125) (2079619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075695872 :
    ThetaLowerSegment 1075695872 1075761408 (5378304523937 / 5000) (53786334161563 / 50000) := by
  exact
    packedTile65536 1075695872 1075761408 13 3163 32797 30 _ _ (1039811 / 50000) (16637 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075761408 :
    ThetaLowerSegment 1075761408 1075826944 (53786334161563 / 50000) (53789583580313 / 50000) := by
  exact
    packedTile65536 1075761408 1075826944 13 3125 32798 30 _ _ (519907 / 25000) (2079631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075826944 :
    ThetaLowerSegment 1075826944 1075892480 (53789583580313 / 50000) (53792846526059 / 50000) := by
  exact
    packedTile65536 1075826944 1075892480 13 3138 32799 30 _ _ (1039817 / 50000) (2079637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075892480 :
    ThetaLowerSegment 1075892480 1075958016 (53792846526059 / 50000) (53796125078519 / 50000) := by
  exact
    packedTile65536 1075892480 1075958016 13 3153 32800 30 _ _ (51991 / 2500) (2079643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075958016 :
    ThetaLowerSegment 1075958016 1076023552 (53796125078519 / 50000) (53799437954597 / 50000) := by
  exact
    packedTile65536 1075958016 1076023552 13 3186 32801 30 _ _ (1039823 / 50000) (2079649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076023552 :
    ThetaLowerSegment 1076023552 1076089088 (53799437954597 / 50000) (53802722764931 / 50000) := by
  exact
    packedTile65536 1076023552 1076089088 13 3159 32802 30 _ _ (519913 / 25000) (415931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076089088 :
    ThetaLowerSegment 1076089088 1076154624 (53802722764931 / 50000) (6725750168221 / 6250) := by
  exact
    packedTile65536 1076089088 1076154624 13 3153 32803 30 _ _ (1039829 / 50000) (2079661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076154624 :
    ThetaLowerSegment 1076154624 1076220160 (6725750168221 / 6250) (3363076876508 / 3125) := by
  exact
    packedTile65536 1076154624 1076220160 13 3105 32804 30 _ _ (129979 / 6250) (2079667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076220160 :
    ThetaLowerSegment 1076220160 1076285696 (3363076876508 / 3125) (53812526302663 / 50000) := by
  exact
    packedTile65536 1076220160 1076285696 13 3170 32805 30 _ _ (2079671 / 100000) (1039837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076285696 :
    ThetaLowerSegment 1076285696 1076351232 (53812526302663 / 50000) (53815787236199 / 50000) := by
  exact
    packedTile65536 1076285696 1076351232 13 3136 32806 30 _ _ (2079677 / 100000) (12998 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076351232 :
    ThetaLowerSegment 1076351232 1076416768 (53815787236199 / 50000) (6727383881957 / 6250) := by
  exact
    packedTile65536 1076351232 1076416768 13 3158 32807 30 _ _ (2079683 / 100000) (1039843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076416768 :
    ThetaLowerSegment 1076416768 1076482304 (6727383881957 / 6250) (107644682733217 / 100000) := by
  exact
    packedTile65536 1076416768 1076482304 13 3145 32808 30 _ _ (2079689 / 100000) (519923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076482304 :
    ThetaLowerSegment 1076482304 1076547840 (107644682733217 / 100000)
      (107651233772467 / 100000) := by
  exact
    packedTile65536 1076482304 1076547840 13 3150 32809 30 _ _ (415939 / 20000) (1039849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076547840 :
    ThetaLowerSegment 1076547840 1076613376 (107651233772467 / 100000)
      (107657917931481 / 100000) := by
  exact
    packedTile65536 1076547840 1076613376 13 3214 32810 30 _ _ (2079701 / 100000) (259963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076613376 :
    ThetaLowerSegment 1076613376 1076678912 (107657917931481 / 100000)
      (107664365023181 / 100000) := by
  exact
    packedTile65536 1076613376 1076678912 13 3100 32811 30 _ _ (2079707 / 100000) (207971 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076678912 :
    ThetaLowerSegment 1076678912 1076744448 (107664365023181 / 100000) (4306839805929 / 4000) := by
  exact
    packedTile65536 1076678912 1076744448 13 3188 32812 30 _ _ (2079713 / 100000) (519929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076744448 :
    ThetaLowerSegment 1076744448 1076809984 (4306839805929 / 4000) (107677450596001 / 100000) := by
  exact
    packedTile65536 1076744448 1076809984 13 3104 32813 30 _ _ (2079719 / 100000) (1039861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076809984 :
    ThetaLowerSegment 1076809984 1076875520 (107677450596001 / 100000)
      (107684035005351 / 100000) := by
  exact
    packedTile65536 1076809984 1076875520 13 3166 32814 30 _ _ (83189 / 4000) (129983 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076875520 :
    ThetaLowerSegment 1076875520 1076941056 (107684035005351 / 100000)
      (26922613783737 / 25000) := by
  exact
    packedTile65536 1076875520 1076941056 13 3087 32815 30 _ _ (2079731 / 100000) (1039867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1076941056 :
    ThetaLowerSegment 1076941056 1077006592 (26922613783737 / 25000) (13462128908313 / 12500) := by
  exact
    packedTile65536 1076941056 1077006592 13 3162 32816 30 _ _ (1039869 / 50000) (2079741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077006592 :
    ThetaLowerSegment 1077006592 1077072128 (13462128908313 / 12500) (13462942088217 / 12500) := by
  exact
    packedTile65536 1077006592 1077072128 13 3128 32817 30 _ _ (64992 / 3125) (2079747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077072128 :
    ThetaLowerSegment 1077072128 1077137664 (13462942088217 / 12500) (26927511580809 / 25000) := by
  exact
    packedTile65536 1077072128 1077137664 13 3130 32818 30 _ _ (8319 / 400) (2079753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077137664 :
    ThetaLowerSegment 1077137664 1077203200 (26927511580809 / 25000) (26929145229147 / 25000) := by
  exact
    packedTile65536 1077137664 1077203200 13 3142 32819 30 _ _ (519939 / 25000) (2079759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077203200 :
    ThetaLowerSegment 1077203200 1077268736 (26929145229147 / 25000) (26930792400651 / 25000) := by
  exact
    packedTile65536 1077203200 1077268736 13 3168 32820 30 _ _ (1039881 / 50000) (415953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077268736 :
    ThetaLowerSegment 1077268736 1077334272 (26930792400651 / 25000) (26932456734993 / 25000) := by
  exact
    packedTile65536 1077268736 1077334272 13 3201 32821 30 _ _ (259971 / 12500) (2079771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077334272 :
    ThetaLowerSegment 1077334272 1077399808 (26932456734993 / 25000) (53868150638217 / 50000) := by
  exact
    packedTile65536 1077334272 1077399808 13 3113 32822 30 _ _ (1039887 / 50000) (2079777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077399808 :
    ThetaLowerSegment 1077399808 1077465344 (53868150638217 / 50000) (53871449169297 / 50000) := by
  exact
    packedTile65536 1077399808 1077465344 13 3172 32823 30 _ _ (103989 / 5000) (2079783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077465344 :
    ThetaLowerSegment 1077465344 1077530880 (53871449169297 / 50000) (53874747709893 / 50000) := by
  exact
    packedTile65536 1077465344 1077530880 13 3172 32824 30 _ _ (1039893 / 50000) (2079789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077530880 :
    ThetaLowerSegment 1077530880 1077596416 (53874747709893 / 50000) (53877958908741 / 50000) := by
  exact
    packedTile65536 1077530880 1077596416 13 3088 32825 30 _ _ (129987 / 6250) (415959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077596416 :
    ThetaLowerSegment 1077596416 1077661952 (53877958908741 / 50000) (26940634453629 / 25000) := by
  exact
    packedTile65536 1077596416 1077661952 13 3183 32826 30 _ _ (1039899 / 50000) (2079801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077661952 :
    ThetaLowerSegment 1077661952 1077727488 (26940634453629 / 25000) (13471109372163 / 12500) := by
  exact
    packedTile65536 1077661952 1077727488 13 3047 32827 30 _ _ (519951 / 25000) (2079807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077727488 :
    ThetaLowerSegment 1077727488 1077793024 (13471109372163 / 12500) (13471937136941 / 12500) := by
  exact
    packedTile65536 1077727488 1077793024 13 3184 32828 30 _ _ (2079811 / 100000) (1039907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077793024 :
    ThetaLowerSegment 1077793024 1077858560 (13471937136941 / 12500) (53891049217343 / 50000) := by
  exact
    packedTile65536 1077793024 1077858560 13 3174 32829 30 _ _ (2079817 / 100000) (103991 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077858560 :
    ThetaLowerSegment 1077858560 1077924096 (53891049217343 / 50000) (13473579154819 / 12500) := by
  exact
    packedTile65536 1077858560 1077924096 13 3142 32830 30 _ _ (2079823 / 100000) (1039913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077924096 :
    ThetaLowerSegment 1077924096 1077989632 (13473579154819 / 12500) (26948790975403 / 25000) := by
  exact
    packedTile65536 1077924096 1077989632 13 3140 32831 30 _ _ (2079829 / 100000) (259979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1077989632 :
    ThetaLowerSegment 1077989632 1078055168 (26948790975403 / 25000) (3368804515611 / 3125) := by
  exact
    packedTile65536 1077989632 1078055168 13 3164 32832 30 _ _ (415967 / 20000) (1039919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078055168 :
    ThetaLowerSegment 1078055168 1078120704 (3368804515611 / 3125) (26952068800073 / 25000) := by
  exact
    packedTile65536 1078055168 1078120704 13 3140 32833 30 _ _ (2079841 / 100000) (519961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078120704 :
    ThetaLowerSegment 1078120704 1078186240 (26952068800073 / 25000) (53907484073969 / 50000) := by
  exact
    packedTile65536 1078120704 1078186240 13 3218 32834 30 _ _ (2079847 / 100000) (41597 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078186240 :
    ThetaLowerSegment 1078186240 1078251776 (53907484073969 / 50000) (53910720325237 / 50000) := by
  exact
    packedTile65536 1078186240 1078251776 13 3112 32835 30 _ _ (2079853 / 100000) (129991 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078251776 :
    ThetaLowerSegment 1078251776 1078317312 (53910720325237 / 50000) (5391397946429 / 5000) := by
  exact
    packedTile65536 1078251776 1078317312 13 3134 32836 30 _ _ (2079859 / 100000) (1039931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078317312 :
    ThetaLowerSegment 1078317312 1078382848 (5391397946429 / 5000) (21566922483343 / 20000) := by
  exact
    packedTile65536 1078317312 1078382848 13 3199 32837 30 _ _ (415973 / 20000) (519967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078382848 :
    ThetaLowerSegment 1078382848 1078448384 (21566922483343 / 20000)
      (107841230566237 / 100000) := by
  exact
    packedTile65536 1078382848 1078448384 13 3182 32838 30 _ _ (2079871 / 100000) (1039937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078448384 :
    ThetaLowerSegment 1078448384 1078513920 (107841230566237 / 100000)
      (10784769690383 / 10000) := by
  exact
    packedTile65536 1078448384 1078513920 13 3109 32839 30 _ _ (2079877 / 100000) (51997 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078513920 :
    ThetaLowerSegment 1078513920 1078579456 (10784769690383 / 10000)
      (107854246455397 / 100000) := by
  exact
    packedTile65536 1078513920 1078579456 13 3149 32840 30 _ _ (2079883 / 100000) (1039943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078579456 :
    ThetaLowerSegment 1078579456 1078644992 (107854246455397 / 100000)
      (107860675395387 / 100000) := by
  exact
    packedTile65536 1078579456 1078644992 13 3091 32841 30 _ _ (207989 / 10000) (2079893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078644992 :
    ThetaLowerSegment 1078644992 1078710528 (107860675395387 / 100000)
      (107867135552363 / 100000) := by
  exact
    packedTile65536 1078644992 1078710528 13 3106 32842 30 _ _ (259987 / 12500) (2079899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078710528 :
    ThetaLowerSegment 1078710528 1078776064 (107867135552363 / 100000)
      (21574744104419 / 20000) := by
  exact
    packedTile65536 1078710528 1078776064 13 3166 32843 30 _ _ (1039951 / 50000) (415981 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078776064 :
    ThetaLowerSegment 1078776064 1078841600 (21574744104419 / 20000)
      (107880280551927 / 100000) := by
  exact
    packedTile65536 1078776064 1078841600 13 3154 32844 30 _ _ (519977 / 25000) (2079911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078841600 :
    ThetaLowerSegment 1078841600 1078907136 (107880280551927 / 100000)
      (107886840600683 / 100000) := by
  exact
    packedTile65536 1078841600 1078907136 13 3154 32845 30 _ _ (1039957 / 50000) (2079917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078907136 :
    ThetaLowerSegment 1078907136 1078972672 (107886840600683 / 100000)
      (107893490104923 / 100000) := by
  exact
    packedTile65536 1078907136 1078972672 13 3197 32846 30 _ _ (25999 / 1250) (2079923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1078972672 :
    ThetaLowerSegment 1078972672 1079038208 (107893490104923 / 100000)
      (107900164587457 / 100000) := by
  exact
    packedTile65536 1078972672 1079038208 13 3209 32847 30 _ _ (1039963 / 50000) (2079929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079038208 :
    ThetaLowerSegment 1079038208 1079103744 (107900164587457 / 100000)
      (107906701813733 / 100000) := by
  exact
    packedTile65536 1079038208 1079103744 13 3143 32848 30 _ _ (519983 / 25000) (415987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079103744 :
    ThetaLowerSegment 1079103744 1079169280 (107906701813733 / 100000)
      (21582619108629 / 20000) := by
  exact
    packedTile65536 1079103744 1079169280 13 3074 32849 30 _ _ (1039969 / 50000) (2079941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079169280 :
    ThetaLowerSegment 1079169280 1079234816 (21582619108629 / 20000)
      (107919701445289 / 100000) := by
  exact
    packedTile65536 1079169280 1079234816 13 3176 32850 30 _ _ (259993 / 12500) (2079947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079234816 :
    ThetaLowerSegment 1079234816 1079300352 (107919701445289 / 100000)
      (107926209608839 / 100000) := by
  exact
    packedTile65536 1079234816 1079300352 13 3129 32851 30 _ _ (41599 / 2000) (2079953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079300352 :
    ThetaLowerSegment 1079300352 1079365888 (107926209608839 / 100000)
      (107932769790063 / 100000) := by
  exact
    packedTile65536 1079300352 1079365888 13 3154 32852 30 _ _ (519989 / 25000) (2079959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079365888 :
    ThetaLowerSegment 1079365888 1079431424 (107932769790063 / 100000)
      (107939263431427 / 100000) := by
  exact
    packedTile65536 1079365888 1079431424 13 3122 32853 30 _ _ (1039981 / 50000) (415993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079431424 :
    ThetaLowerSegment 1079431424 1079496960 (107939263431427 / 100000)
      (53972900386997 / 50000) := by
  exact
    packedTile65536 1079431424 1079496960 13 3143 32854 30 _ _ (2079969 / 100000) (519993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079496960 :
    ThetaLowerSegment 1079496960 1079562496 (53972900386997 / 50000) (53976174267647 / 50000) := by
  exact
    packedTile65536 1079496960 1079562496 13 3148 32855 30 _ _ (83199 / 4000) (1039989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079562496 :
    ThetaLowerSegment 1079562496 1079628032 (53976174267647 / 50000)
      (107958898395463 / 100000) := by
  exact
    packedTile65536 1079562496 1079628032 13 3149 32856 30 _ _ (2079981 / 100000) (129999 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079628032 :
    ThetaLowerSegment 1079628032 1079693568 (107958898395463 / 100000)
      (107965516914097 / 100000) := by
  exact
    packedTile65536 1079628032 1079693568 13 3182 32857 30 _ _ (2079987 / 100000) (207999 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079693568 :
    ThetaLowerSegment 1079693568 1079759104 (107965516914097 / 100000)
      (13496513031491 / 12500) := by
  exact
    packedTile65536 1079693568 1079759104 13 3167 32858 30 _ _ (2079993 / 100000) (519999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079759104 :
    ThetaLowerSegment 1079759104 1079824640 (13496513031491 / 12500) (53989361404373 / 50000) := by
  exact
    packedTile65536 1079759104 1079824640 13 3182 32859 30 _ _ (2079999 / 100000) (1040001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079824640 :
    ThetaLowerSegment 1079824640 1079890176 (53989361404373 / 50000) (53992597892153 / 50000) := by
  exact
    packedTile65536 1079824640 1079890176 13 3112 32860 30 _ _ (416001 / 20000) (260001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079890176 :
    ThetaLowerSegment 1079890176 1079955712 (53992597892153 / 50000) (53995938389819 / 50000) := by
  exact
    packedTile65536 1079890176 1079955712 13 3212 32861 30 _ _ (2080011 / 100000) (1040007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079955712 :
    ThetaLowerSegment 1079955712 1080021248 (53995938389819 / 50000)
      (107998397632933 / 100000) := by
  exact
    packedTile65536 1079955712 1080021248 13 3135 32862 30 _ _ (2080017 / 100000) (104001 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080021248 :
    ThetaLowerSegment 1080021248 1080086784 (107998397632933 / 100000)
      (108004903944877 / 100000) := by
  exact
    packedTile65536 1080021248 1080086784 13 3128 32863 30 _ _ (2080023 / 100000) (1040013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080086784 :
    ThetaLowerSegment 1080086784 1080152320 (108004903944877 / 100000)
      (54005731138157 / 50000) := by
  exact
    packedTile65536 1080086784 1080152320 13 3153 32864 30 _ _ (2080029 / 100000) (65001 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080152320 :
    ThetaLowerSegment 1080152320 1080217856 (54005731138157 / 50000) (54009034233737 / 50000) := by
  exact
    packedTile65536 1080152320 1080217856 13 3176 32865 30 _ _ (416007 / 20000) (1040019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080217856 :
    ThetaLowerSegment 1080217856 1080283392 (54009034233737 / 50000) (10802471627851 / 10000) := by
  exact
    packedTile65536 1080217856 1080283392 13 3196 32866 30 _ _ (2080041 / 100000) (520011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080283392 :
    ThetaLowerSegment 1080283392 1080348928 (10802471627851 / 10000) (13503910633367 / 12500) := by
  exact
    packedTile65536 1080283392 1080348928 13 3158 32867 30 _ _ (2080047 / 100000) (41601 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080348928 :
    ThetaLowerSegment 1080348928 1080414464 (13503910633367 / 12500) (21607585335233 / 20000) := by
  exact
    packedTile65536 1080348928 1080414464 13 3193 32868 30 _ _ (2080053 / 100000) (260007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080414464 :
    ThetaLowerSegment 1080414464 1080480000 (21607585335233 / 20000) (21608909085417 / 20000) := by
  exact
    packedTile65536 1080414464 1080480000 13 3182 32869 30 _ _ (104003 / 5000) (2080063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080480000 :
    ThetaLowerSegment 1080480000 1080545536 (21608909085417 / 20000)
      (108051135076173 / 100000) := by
  exact
    packedTile65536 1080480000 1080545536 13 3168 32870 30 _ _ (1040033 / 50000) (2080069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080545536 :
    ThetaLowerSegment 1080545536 1080611072 (108051135076173 / 100000)
      (108057539617861 / 100000) := by
  exact
    packedTile65536 1080545536 1080611072 13 3079 32871 30 _ _ (260009 / 12500) (83203 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080611072 :
    ThetaLowerSegment 1080611072 1080676608 (108057539617861 / 100000)
      (21612796739901 / 20000) := by
  exact
    packedTile65536 1080611072 1080676608 13 3098 32872 30 _ _ (1040039 / 50000) (2080081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080676608 :
    ThetaLowerSegment 1080676608 1080742144 (21612796739901 / 20000)
      (108070280113773 / 100000) := by
  exact
    packedTile65536 1080676608 1080742144 13 3027 32873 30 _ _ (520021 / 25000) (2080087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080742144 :
    ThetaLowerSegment 1080742144 1080807680 (108070280113773 / 100000)
      (108076938481863 / 100000) := by
  exact
    packedTile65536 1080742144 1080807680 13 3201 32874 30 _ _ (208009 / 10000) (2080093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080807680 :
    ThetaLowerSegment 1080807680 1080873216 (108076938481863 / 100000)
      (108083467903207 / 100000) := by
  exact
    packedTile65536 1080807680 1080873216 13 3139 32875 30 _ _ (65003 / 3125) (2080099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080873216 :
    ThetaLowerSegment 1080873216 1080938752 (108083467903207 / 100000)
      (108089993183181 / 100000) := by
  exact
    packedTile65536 1080873216 1080938752 13 3137 32876 30 _ _ (1040051 / 50000) (416021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1080938752 :
    ThetaLowerSegment 1080938752 1081004288 (108089993183181 / 100000)
      (108096576725001 / 100000) := by
  exact
    packedTile65536 1080938752 1081004288 13 3165 32877 30 _ _ (520027 / 25000) (2080111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081004288 :
    ThetaLowerSegment 1081004288 1081069824 (108096576725001 / 100000)
      (108103149885241 / 100000) := by
  exact
    packedTile65536 1081004288 1081069824 13 3160 32878 30 _ _ (1040057 / 50000) (2080117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081069824 :
    ThetaLowerSegment 1081069824 1081135360 (108103149885241 / 100000)
      (108109604497601 / 100000) := by
  exact
    packedTile65536 1081069824 1081135360 13 3103 32879 30 _ _ (52003 / 2500) (2080123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081135360 :
    ThetaLowerSegment 1081135360 1081200896 (108109604497601 / 100000) (4324650352827 / 4000) := by
  exact
    packedTile65536 1081135360 1081200896 13 3199 32880 30 _ _ (1040063 / 50000) (2080129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081200896 :
    ThetaLowerSegment 1081200896 1081266432 (4324650352827 / 4000) (108122923563603 / 100000) := by
  exact
    packedTile65536 1081200896 1081266432 13 3204 32881 30 _ _ (520033 / 25000) (416027 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081266432 :
    ThetaLowerSegment 1081266432 1081331968 (108122923563603 / 100000)
      (108129394872921 / 100000) := by
  exact
    packedTile65536 1081266432 1081331968 13 3111 32882 30 _ _ (1040069 / 50000) (2080141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081331968 :
    ThetaLowerSegment 1081331968 1081397504 (108129394872921 / 100000)
      (108135878681769 / 100000) := by
  exact
    packedTile65536 1081331968 1081397504 13 3117 32883 30 _ _ (130009 / 6250) (2080147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081397504 :
    ThetaLowerSegment 1081397504 1081463040 (108135878681769 / 100000)
      (108142472760439 / 100000) := by
  exact
    packedTile65536 1081397504 1081463040 13 3170 32884 30 _ _ (2080151 / 100000) (1040077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081463040 :
    ThetaLowerSegment 1081463040 1081528576 (108142472760439 / 100000) (3379662174606 / 3125) := by
  exact
    packedTile65536 1081463040 1081528576 13 3229 32885 30 _ _ (2080157 / 100000) (13001 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081528576 :
    ThetaLowerSegment 1081528576 1081594112 (3379662174606 / 3125) (270389698479 / 250) := by
  exact
    packedTile65536 1081528576 1081594112 13 3216 32886 30 _ _ (2080163 / 100000) (1040083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081594112 :
    ThetaLowerSegment 1081594112 1081659648 (270389698479 / 250) (21632488464959 / 20000) := by
  exact
    packedTile65536 1081594112 1081659648 13 3155 32887 30 _ _ (2080169 / 100000) (520043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081659648 :
    ThetaLowerSegment 1081659648 1081725184 (21632488464959 / 20000) (1352112773979 / 1250) := by
  exact
    packedTile65536 1081659648 1081725184 13 3163 32888 30 _ _ (83207 / 4000) (1040089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081725184 :
    ThetaLowerSegment 1081725184 1081790720 (1352112773979 / 1250) (108175593210099 / 100000) := by
  exact
    packedTile65536 1081725184 1081790720 13 3159 32889 30 _ _ (2080181 / 100000) (260023 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081790720 :
    ThetaLowerSegment 1081790720 1081856256 (108175593210099 / 100000)
      (21636432488129 / 20000) := by
  exact
    packedTile65536 1081790720 1081856256 13 3158 32890 30 _ _ (2080187 / 100000) (208019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081856256 :
    ThetaLowerSegment 1081856256 1081921792 (21636432488129 / 20000) (3380898190347 / 3125) := by
  exact
    packedTile65536 1081856256 1081921792 13 3163 32891 30 _ _ (2080193 / 100000) (520049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081921792 :
    ThetaLowerSegment 1081921792 1081987328 (3380898190347 / 3125) (108195246873377 / 100000) := by
  exact
    packedTile65536 1081921792 1081987328 13 3127 32892 30 _ _ (2080199 / 100000) (1040101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081987328 :
    ThetaLowerSegment 1081987328 1082052864 (108195246873377 / 100000)
      (27050475362293 / 25000) := by
  exact
    packedTile65536 1081987328 1082052864 13 3199 32893 30 _ _ (416041 / 20000) (130013 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082052864 :
    ThetaLowerSegment 1082052864 1082118400 (27050475362293 / 25000)
      (108208472835721 / 100000) := by
  exact
    packedTile65536 1082052864 1082118400 13 3159 32894 30 _ _ (2080211 / 100000) (1040107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082118400 :
    ThetaLowerSegment 1082118400 1082183936 (108208472835721 / 100000)
      (108215017198403 / 100000) := by
  exact
    packedTile65536 1082118400 1082183936 13 3146 32895 30 _ _ (2080217 / 100000) (104011 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082183936 :
    ThetaLowerSegment 1082183936 1082249472 (108215017198403 / 100000)
      (108221544938177 / 100000) := by
  exact
    packedTile65536 1082183936 1082249472 13 3138 32896 30 _ _ (2080223 / 100000) (1040113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082249472 :
    ThetaLowerSegment 1082249472 1082315008 (108221544938177 / 100000)
      (10822819543029 / 10000) := by
  exact
    packedTile65536 1082249472 1082315008 13 3197 32897 30 _ _ (2080229 / 100000) (260029 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082315008 :
    ThetaLowerSegment 1082315008 1082446080 (10822819543029 / 10000) (21648271415427 / 20000) := by
  exact
    packedTile65536 1082315008 1082446080 14 6327 32898 30 _ _ (416047 / 20000) (1040119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082446080 :
    ThetaLowerSegment 1082446080 1082577152 (21648271415427 / 20000)
      (108254487596199 / 100000) := by
  exact
    packedTile65536 1082446080 1082577152 14 6312 32900 30 _ _ (2080247 / 100000) (8321 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082577152 :
    ThetaLowerSegment 1082577152 1082708224 (108254487596199 / 100000)
      (108267406010799 / 100000) := by
  exact
    packedTile65536 1082577152 1082708224 14 6210 32902 30 _ _ (104013 / 5000) (2080263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082708224 :
    ThetaLowerSegment 1082708224 1082773760 (108267406010799 / 100000)
      (108274000473039 / 100000) := by
  exact
    packedTile65536 1082708224 1082773760 13 3170 32904 30 _ _ (130017 / 6250) (83211 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082773760 :
    ThetaLowerSegment 1082773760 1082839296 (108274000473039 / 100000)
      (108280542947349 / 100000) := by
  exact
    packedTile65536 1082773760 1082839296 13 3145 32905 30 _ _ (1040139 / 50000) (2080281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082839296 :
    ThetaLowerSegment 1082839296 1082904832 (108280542947349 / 100000)
      (108287066717973 / 100000) := by
  exact
    packedTile65536 1082839296 1082904832 13 3136 32906 30 _ _ (520071 / 25000) (2080287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082904832 :
    ThetaLowerSegment 1082904832 1082970368 (108287066717973 / 100000)
      (108293696602203 / 100000) := by
  exact
    packedTile65536 1082904832 1082970368 13 3187 32907 30 _ _ (208029 / 10000) (2080293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1082970368 :
    ThetaLowerSegment 1082970368 1083101440 (108293696602203 / 100000)
      (108306789985227 / 100000) := by
  exact
    packedTile65536 1082970368 1083101440 14 6294 32908 30 _ _ (260037 / 12500) (2080299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083101440 :
    ThetaLowerSegment 1083101440 1083166976 (108306789985227 / 100000)
      (108313488576987 / 100000) := by
  exact
    packedTile65536 1083101440 1083166976 13 3220 32910 30 _ _ (520077 / 25000) (2080311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083166976 :
    ThetaLowerSegment 1083166976 1083298048 (108313488576987 / 100000)
      (108326592474873 / 100000) := by
  exact
    packedTile65536 1083166976 1083298048 14 6299 32911 30 _ _ (1040157 / 50000) (2080317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083298048 :
    ThetaLowerSegment 1083298048 1083429120 (108326592474873 / 100000)
      (21667955100147 / 20000) := by
  exact
    packedTile65536 1083298048 1083429120 14 6337 32913 30 _ _ (1040163 / 50000) (2080329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083429120 :
    ThetaLowerSegment 1083429120 1083560192 (21667955100147 / 20000)
      (108352804657629 / 100000) := by
  exact
    packedTile65536 1083429120 1083560192 14 6263 32915 30 _ _ (1040169 / 50000) (2080341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083560192 :
    ThetaLowerSegment 1083560192 1083691264 (108352804657629 / 100000)
      (108365994076629 / 100000) := by
  exact
    packedTile65536 1083560192 1083691264 14 6340 32917 30 _ _ (41607 / 2000) (2080353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083691264 :
    ThetaLowerSegment 1083691264 1083822336 (108365994076629 / 100000)
      (108379139884107 / 100000) := by
  exact
    packedTile65536 1083691264 1083822336 14 6319 32919 30 _ _ (1040181 / 50000) (416073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083822336 :
    ThetaLowerSegment 1083822336 1083953408 (108379139884107 / 100000)
      (108392192150583 / 100000) := by
  exact
    packedTile65536 1083822336 1083953408 14 6274 32921 30 _ _ (1040187 / 50000) (2080377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083953408 :
    ThetaLowerSegment 1083953408 1084084480 (108392192150583 / 100000)
      (108405398447259 / 100000) := by
  exact
    packedTile65536 1083953408 1084084480 14 6348 32923 30 _ _ (2080387 / 100000) (208039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084084480 :
    ThetaLowerSegment 1084084480 1084215552 (108405398447259 / 100000)
      (108418559051333 / 100000) := by
  exact
    packedTile65536 1084084480 1084215552 14 6326 32925 30 _ _ (2080399 / 100000) (1040201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084215552 :
    ThetaLowerSegment 1084215552 1084346624 (108418559051333 / 100000)
      (108431761339539 / 100000) := by
  exact
    packedTile65536 1084215552 1084346624 14 6346 32927 30 _ _ (2080411 / 100000) (1040207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084346624 :
    ThetaLowerSegment 1084346624 1084477696 (108431761339539 / 100000)
      (27111156148737 / 25000) := by
  exact
    packedTile65536 1084346624 1084477696 14 6183 32929 30 _ _ (2080423 / 100000) (1040213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084477696 :
    ThetaLowerSegment 1084477696 1084608768 (27111156148737 / 25000)
      (108457849920243 / 100000) := by
  exact
    packedTile65536 1084477696 1084608768 14 6357 32931 30 _ _ (416087 / 20000) (1040219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084608768 :
    ThetaLowerSegment 1084608768 1084739840 (108457849920243 / 100000)
      (10847100042573 / 10000) := by
  exact
    packedTile65536 1084608768 1084739840 14 6321 32933 30 _ _ (2080447 / 100000) (41609 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084739840 :
    ThetaLowerSegment 1084739840 1084870912 (10847100042573 / 10000)
      (108484063627791 / 100000) := by
  exact
    packedTile65536 1084739840 1084870912 14 6279 32935 30 _ _ (2080459 / 100000) (1040231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1084870912 :
    ThetaLowerSegment 1084870912 1085001984 (108484063627791 / 100000)
      (27124342059959 / 25000) := by
  exact
    packedTile65536 1084870912 1085001984 14 6395 32937 30 _ _ (2080471 / 100000) (1040237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085001984 :
    ThetaLowerSegment 1085001984 1085133056 (27124342059959 / 25000) (54255239721851 / 50000) := by
  exact
    packedTile65536 1085001984 1085133056 14 6302 32939 30 _ _ (2080483 / 100000) (1040243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085133056 :
    ThetaLowerSegment 1085133056 1085264128 (54255239721851 / 50000)
      (108523497100917 / 100000) := by
  exact
    packedTile65536 1085133056 1085264128 14 6257 32941 30 _ _ (416099 / 20000) (1040249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085264128 :
    ThetaLowerSegment 1085264128 1085395200 (108523497100917 / 100000)
      (54268230370017 / 50000) := by
  exact
    packedTile65536 1085264128 1085395200 14 6231 32943 30 _ _ (2080507 / 100000) (208051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085395200 :
    ThetaLowerSegment 1085395200 1085526272 (54268230370017 / 50000) (54274759038639 / 50000) := by
  exact
    packedTile65536 1085395200 1085526272 14 6276 32945 30 _ _ (2080519 / 100000) (1040261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085526272 :
    ThetaLowerSegment 1085526272 1085657344 (54274759038639 / 50000) (54281377210931 / 50000) := by
  exact
    packedTile65536 1085526272 1085657344 14 6362 32947 30 _ _ (520133 / 25000) (416107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085657344 :
    ThetaLowerSegment 1085657344 1085788416 (54281377210931 / 50000) (54288002703299 / 50000) := by
  exact
    packedTile65536 1085657344 1085788416 14 6369 32949 30 _ _ (65017 / 3125) (2080547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085788416 :
    ThetaLowerSegment 1085788416 1085919488 (54288002703299 / 50000) (54294524206081 / 50000) := by
  exact
    packedTile65536 1085788416 1085919488 14 6269 32951 30 _ _ (520139 / 25000) (2080559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085919488 :
    ThetaLowerSegment 1085919488 1086050560 (54294524206081 / 50000) (54301044706193 / 50000) := by
  exact
    packedTile65536 1085919488 1086050560 14 6268 32953 30 _ _ (260071 / 12500) (2080571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086050560 :
    ThetaLowerSegment 1086050560 1086181632 (54301044706193 / 50000) (54307637023923 / 50000) := by
  exact
    packedTile65536 1086050560 1086181632 14 6337 32955 30 _ _ (104029 / 5000) (2080583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086181632 :
    ThetaLowerSegment 1086181632 1086312704 (54307637023923 / 50000) (54314175284283 / 50000) := by
  exact
    packedTile65536 1086181632 1086312704 14 6285 32957 30 _ _ (130037 / 6250) (416119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086312704 :
    ThetaLowerSegment 1086312704 1086443776 (54314175284283 / 50000) (54320742710809 / 50000) := by
  exact
    packedTile65536 1086312704 1086443776 14 6313 32959 30 _ _ (520151 / 25000) (2080607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086443776 :
    ThetaLowerSegment 1086443776 1086574848 (54320742710809 / 50000) (54327333061989 / 50000) := by
  exact
    packedTile65536 1086443776 1086574848 14 6335 32961 30 _ _ (260077 / 12500) (2080619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086574848 :
    ThetaLowerSegment 1086574848 1086705920 (54327333061989 / 50000) (54333869354851 / 50000) := by
  exact
    packedTile65536 1086574848 1086705920 14 6283 32963 30 _ _ (520157 / 25000) (2080631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086705920 :
    ThetaLowerSegment 1086705920 1086836992 (54333869354851 / 50000) (54340454580451 / 50000) := by
  exact
    packedTile65536 1086705920 1086836992 14 6330 32965 30 _ _ (13004 / 625) (2080643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086836992 :
    ThetaLowerSegment 1086836992 1086968064 (54340454580451 / 50000) (10869390075199 / 10000) := by
  exact
    packedTile65536 1086836992 1086968064 14 6244 32967 30 _ _ (520163 / 25000) (416131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1086968064 :
    ThetaLowerSegment 1086968064 1087099136 (10869390075199 / 10000) (54353570008511 / 50000) := by
  exact
    packedTile65536 1086968064 1087099136 14 6363 32969 30 _ _ (260083 / 12500) (2080667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087099136 :
    ThetaLowerSegment 1087099136 1087230208 (54353570008511 / 50000) (10872034814827 / 10000) := by
  exact
    packedTile65536 1087099136 1087230208 14 6348 32971 30 _ _ (520169 / 25000) (2080679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087230208 :
    ThetaLowerSegment 1087230208 1087361280 (10872034814827 / 10000) (54366818751263 / 50000) := by
  exact
    packedTile65536 1087230208 1087361280 14 6387 32973 30 _ _ (130043 / 6250) (2080691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087361280 :
    ThetaLowerSegment 1087361280 1087492352 (54366818751263 / 50000) (54373408328163 / 50000) := by
  exact
    packedTile65536 1087361280 1087492352 14 6334 32975 30 _ _ (20807 / 1000) (2080703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087492352 :
    ThetaLowerSegment 1087492352 1087623424 (54373408328163 / 50000) (3398748571194 / 3125) := by
  exact
    packedTile65536 1087492352 1087623424 14 6314 32977 30 _ _ (2080713 / 100000) (520179 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087623424 :
    ThetaLowerSegment 1087623424 1087754496 (3398748571194 / 3125) (108772885984083 / 100000) := by
  exact
    packedTile65536 1087623424 1087754496 14 6215 32979 30 _ _ (83229 / 4000) (260091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087754496 :
    ThetaLowerSegment 1087754496 1087885568 (108772885984083 / 100000)
      (108785911397703 / 100000) := by
  exact
    packedTile65536 1087754496 1087885568 14 6260 32981 30 _ _ (2080737 / 100000) (104037 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087885568 :
    ThetaLowerSegment 1087885568 1088016640 (108785911397703 / 100000)
      (10879915120359 / 10000) := by
  exact
    packedTile65536 1087885568 1088016640 14 6363 32983 30 _ _ (2080749 / 100000) (130047 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088016640 :
    ThetaLowerSegment 1088016640 1088147712 (10879915120359 / 10000)
      (108812224624953 / 100000) := by
  exact
    packedTile65536 1088016640 1088147712 14 6283 32985 30 _ _ (2080761 / 100000) (520191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088147712 :
    ThetaLowerSegment 1088147712 1088278784 (108812224624953 / 100000)
      (13603151861349 / 12500) := by
  exact
    packedTile65536 1088147712 1088278784 14 6243 32987 30 _ _ (2080773 / 100000) (260097 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088278784 :
    ThetaLowerSegment 1088278784 1088409856 (13603151861349 / 12500)
      (108838380017487 / 100000) := by
  exact
    packedTile65536 1088278784 1088409856 14 6327 32989 30 _ _ (416157 / 20000) (520197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088409856 :
    ThetaLowerSegment 1088409856 1088540928 (108838380017487 / 100000)
      (108851264312511 / 100000) := by
  exact
    packedTile65536 1088409856 1088540928 14 6192 32991 30 _ _ (2080797 / 100000) (2601 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088540928 :
    ThetaLowerSegment 1088540928 1088672000 (108851264312511 / 100000) (435457252263 / 400) := by
  exact
    packedTile65536 1088540928 1088672000 14 6271 32993 30 _ _ (2080809 / 100000) (520203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088672000 :
    ThetaLowerSegment 1088672000 1088803072 (435457252263 / 400) (27219348276639 / 25000) := by
  exact
    packedTile65536 1088672000 1088803072 14 6286 32995 30 _ _ (2080821 / 100000) (260103 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088803072 :
    ThetaLowerSegment 1088803072 1088934144 (27219348276639 / 25000) (54445369784709 / 50000) := by
  exact
    packedTile65536 1088803072 1088934144 14 6414 32997 30 _ _ (2080833 / 100000) (520209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1088934144 :
    ThetaLowerSegment 1088934144 1089065216 (54445369784709 / 50000) (54451845374349 / 50000) := by
  exact
    packedTile65536 1088934144 1089065216 14 6224 32999 30 _ _ (416169 / 20000) (130053 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089065216 :
    ThetaLowerSegment 1089065216 1089196288 (54451845374349 / 50000) (6807301309773 / 6250) := by
  exact
    packedTile65536 1089065216 1089196288 14 6310 33000 30 _ _ (2080857 / 100000) (104043 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089196288 :
    ThetaLowerSegment 1089196288 1089327360 (6807301309773 / 6250) (108929911703247 / 100000) := by
  exact
    packedTile65536 1089196288 1089327360 14 6291 33002 30 _ _ (2080869 / 100000) (260109 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089327360 :
    ThetaLowerSegment 1089327360 1089458432 (108929911703247 / 100000)
      (108942962988879 / 100000) := by
  exact
    packedTile65536 1089327360 1089458432 14 6272 33004 30 _ _ (2080881 / 100000) (520221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089458432 :
    ThetaLowerSegment 1089458432 1089589504 (108942962988879 / 100000)
      (108955997702631 / 100000) := by
  exact
    packedTile65536 1089458432 1089589504 14 6264 33006 30 _ _ (2080893 / 100000) (65028 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089589504 :
    ThetaLowerSegment 1089589504 1089720576 (108955997702631 / 100000)
      (54484619250573 / 50000) := by
  exact
    packedTile65536 1089589504 1089720576 14 6363 33008 30 _ _ (416181 / 20000) (520227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089720576 :
    ThetaLowerSegment 1089720576 1089851648 (54484619250573 / 50000) (27245586029103 / 25000) := by
  exact
    packedTile65536 1089720576 1089851648 14 6298 33010 30 _ _ (2080917 / 100000) (52023 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089851648 :
    ThetaLowerSegment 1089851648 1089982720 (27245586029103 / 25000) (54497720741769 / 50000) := by
  exact
    packedTile65536 1089851648 1089982720 14 6294 33012 30 _ _ (2080929 / 100000) (520233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089982720 :
    ThetaLowerSegment 1089982720 1090113792 (54497720741769 / 50000) (54504279867801 / 50000) := by
  exact
    packedTile65536 1089982720 1090113792 14 6304 33014 30 _ _ (2080941 / 100000) (130059 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090113792 :
    ThetaLowerSegment 1090113792 1090244864 (54504279867801 / 50000) (54510839031657 / 50000) := by
  exact
    packedTile65536 1090113792 1090244864 14 6304 33016 30 _ _ (2080953 / 100000) (520239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090244864 :
    ThetaLowerSegment 1090244864 1090375936 (54510839031657 / 50000) (54517410719127 / 50000) := by
  exact
    packedTile65536 1090244864 1090375936 14 6316 33018 30 _ _ (416193 / 20000) (260121 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090375936 :
    ThetaLowerSegment 1090375936 1090507008 (54517410719127 / 50000) (6815496504951 / 6250) := by
  exact
    packedTile65536 1090375936 1090507008 14 6306 33020 30 _ _ (2080977 / 100000) (104049 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090507008 :
    ThetaLowerSegment 1090507008 1090638080 (6815496504951 / 6250) (54530466806277 / 50000) := by
  exact
    packedTile65536 1090507008 1090638080 14 6242 33022 30 _ _ (2080989 / 100000) (65031 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090638080 :
    ThetaLowerSegment 1090638080 1090769152 (54530466806277 / 50000) (54537001149417 / 50000) := by
  exact
    packedTile65536 1090638080 1090769152 14 6280 33024 30 _ _ (2081001 / 100000) (520251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090769152 :
    ThetaLowerSegment 1090769152 1090900224 (54537001149417 / 50000) (10908722089341 / 10000) := by
  exact
    packedTile65536 1090769152 1090900224 14 6352 33026 30 _ _ (2081013 / 100000) (260127 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1090900224 :
    ThetaLowerSegment 1090900224 1091031296 (10908722089341 / 10000) (681877513161 / 625) := by
  exact
    packedTile65536 1090900224 1091031296 14 6334 33028 30 _ _ (83241 / 4000) (520257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091031296 :
    ThetaLowerSegment 1091031296 1091162368 (681877513161 / 625) (4364535927273 / 4000) := by
  exact
    packedTile65536 1091031296 1091162368 14 6245 33030 30 _ _ (2081037 / 100000) (26013 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091162368 :
    ThetaLowerSegment 1091162368 1091293440 (4364535927273 / 4000) (109126525438917 / 100000) := by
  exact
    packedTile65536 1091162368 1091293440 14 6308 33032 30 _ _ (2081049 / 100000) (520263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091293440 :
    ThetaLowerSegment 1091293440 1091424512 (109126525438917 / 100000)
      (54569785805163 / 50000) := by
  exact
    packedTile65536 1091293440 1091424512 14 6269 33034 30 _ _ (2081061 / 100000) (260133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091424512 :
    ThetaLowerSegment 1091424512 1091555584 (54569785805163 / 50000)
      (109152701099883 / 100000) := by
  exact
    packedTile65536 1091424512 1091555584 14 6309 33036 30 _ _ (2081073 / 100000) (520269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091555584 :
    ThetaLowerSegment 1091555584 1091686656 (109152701099883 / 100000)
      (54582929900169 / 50000) := by
  exact
    packedTile65536 1091555584 1091686656 14 6323 33038 30 _ _ (416217 / 20000) (65034 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091686656 :
    ThetaLowerSegment 1091686656 1091817728 (54582929900169 / 50000) (1091790664419 / 1000) := by
  exact
    packedTile65536 1091686656 1091817728 14 6346 33040 30 _ _ (2081097 / 100000) (20811 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091817728 :
    ThetaLowerSegment 1091817728 1091948800 (1091790664419 / 1000) (109192071292041 / 100000) := by
  exact
    packedTile65536 1091817728 1091948800 14 6249 33042 30 _ _ (2081109 / 100000) (260139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1091948800 :
    ThetaLowerSegment 1091948800 1092079872 (109192071292041 / 100000)
      (27301324203999 / 25000) := by
  exact
    packedTile65536 1091948800 1092079872 14 6355 33044 30 _ _ (2081121 / 100000) (520281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092079872 :
    ThetaLowerSegment 1092079872 1092210944 (27301324203999 / 25000) (54609239356209 / 50000) := by
  exact
    packedTile65536 1092079872 1092210944 14 6334 33046 30 _ _ (2081133 / 100000) (130071 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092210944 :
    ThetaLowerSegment 1092210944 1092342016 (54609239356209 / 50000)
      (109231712713473 / 100000) := by
  exact
    packedTile65536 1092210944 1092342016 14 6359 33048 30 _ _ (416229 / 20000) (520287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092342016 :
    ThetaLowerSegment 1092342016 1092473088 (109231712713473 / 100000)
      (109244686646211 / 100000) := by
  exact
    packedTile65536 1092342016 1092473088 14 6234 33050 30 _ _ (2081157 / 100000) (52029 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092473088 :
    ThetaLowerSegment 1092473088 1092604160 (109244686646211 / 100000) (3414303131124 / 3125) := by
  exact
    packedTile65536 1092473088 1092604160 14 6253 33052 30 _ _ (2081169 / 100000) (520293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092604160 :
    ThetaLowerSegment 1092604160 1092735232 (3414303131124 / 3125) (109270842853983 / 100000) := by
  exact
    packedTile65536 1092604160 1092735232 14 6315 33054 30 _ _ (2081181 / 100000) (65037 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092735232 :
    ThetaLowerSegment 1092735232 1092866304 (109270842853983 / 100000)
      (109283987668971 / 100000) := by
  exact
    packedTile65536 1092735232 1092866304 14 6316 33056 30 _ _ (2081193 / 100000) (520299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092866304 :
    ThetaLowerSegment 1092866304 1092997376 (109283987668971 / 100000)
      (54648515290353 / 50000) := by
  exact
    packedTile65536 1092866304 1092997376 14 6267 33058 30 _ _ (416241 / 20000) (260151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1092997376 :
    ThetaLowerSegment 1092997376 1093128448 (54648515290353 / 50000) (54655171022319 / 50000) := by
  exact
    packedTile65536 1092997376 1093128448 14 6396 33060 30 _ _ (2081217 / 100000) (104061 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093128448 :
    ThetaLowerSegment 1093128448 1093259520 (54655171022319 / 50000) (21864683681289 / 20000) := by
  exact
    packedTile65536 1093128448 1093259520 14 6283 33062 30 _ _ (2081229 / 100000) (130077 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093259520 :
    ThetaLowerSegment 1093259520 1093390592 (21864683681289 / 20000)
      (109336625961831 / 100000) := by
  exact
    packedTile65536 1093259520 1093390592 14 6346 33064 30 _ _ (2081241 / 100000) (520311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093390592 :
    ThetaLowerSegment 1093390592 1093521664 (109336625961831 / 100000)
      (21869996688717 / 20000) := by
  exact
    packedTile65536 1093390592 1093521664 14 6418 33066 30 _ _ (2081253 / 100000) (260157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093521664 :
    ThetaLowerSegment 1093521664 1093652736 (21869996688717 / 20000) (21872624077653 / 20000) := by
  exact
    packedTile65536 1093521664 1093652736 14 6312 33068 30 _ _ (416253 / 20000) (520317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093652736 :
    ThetaLowerSegment 1093652736 1093783808 (21872624077653 / 20000) (13672037119119 / 12500) := by
  exact
    packedTile65536 1093652736 1093783808 14 6331 33070 30 _ _ (2081277 / 100000) (13008 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093783808 :
    ThetaLowerSegment 1093783808 1093914880 (13672037119119 / 12500) (21877859753067 / 20000) := by
  exact
    packedTile65536 1093783808 1093914880 14 6247 33072 30 _ _ (2081289 / 100000) (520323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093914880 :
    ThetaLowerSegment 1093914880 1094045952 (21877859753067 / 20000) (54701125350729 / 50000) := by
  exact
    packedTile65536 1093914880 1094045952 14 6223 33074 30 _ _ (2081301 / 100000) (260163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094045952 :
    ThetaLowerSegment 1094045952 1094177024 (54701125350729 / 50000)
      (109415448307191 / 100000) := by
  exact
    packedTile65536 1094045952 1094177024 14 6341 33076 30 _ _ (2081313 / 100000) (520329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094177024 :
    ThetaLowerSegment 1094177024 1094308096 (109415448307191 / 100000)
      (109428431612541 / 100000) := by
  exact
    packedTile65536 1094177024 1094308096 14 6238 33078 30 _ _ (83253 / 4000) (130083 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094308096 :
    ThetaLowerSegment 1094308096 1094439168 (109428431612541 / 100000)
      (54720718943727 / 50000) := by
  exact
    packedTile65536 1094308096 1094439168 14 6249 33080 30 _ _ (2081337 / 100000) (104067 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094439168 :
    ThetaLowerSegment 1094439168 1094570240 (54720718943727 / 50000)
      (109454431749261 / 100000) := by
  exact
    packedTile65536 1094439168 1094570240 14 6243 33082 30 _ _ (2081349 / 100000) (260169 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094570240 :
    ThetaLowerSegment 1094570240 1094701312 (109454431749261 / 100000)
      (109467540160839 / 100000) := by
  exact
    packedTile65536 1094570240 1094701312 14 6298 33084 30 _ _ (2081361 / 100000) (520341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094701312 :
    ThetaLowerSegment 1094701312 1094832384 (109467540160839 / 100000) (4379228776587 / 4000) := by
  exact
    packedTile65536 1094701312 1094832384 14 6332 33086 30 _ _ (2081373 / 100000) (65043 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094832384 :
    ThetaLowerSegment 1094832384 1094963456 (4379228776587 / 4000) (2737346688093 / 2500) := by
  exact
    packedTile65536 1094832384 1094963456 14 6317 33088 30 _ _ (416277 / 20000) (520347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1094963456 :
    ThetaLowerSegment 1094963456 1095094528 (2737346688093 / 2500) (109506882499161 / 100000) := by
  exact
    packedTile65536 1094963456 1095094528 14 6253 33090 30 _ _ (2081397 / 100000) (10407 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095094528 :
    ThetaLowerSegment 1095094528 1095225600 (109506882499161 / 100000)
      (109520061980949 / 100000) := by
  exact
    packedTile65536 1095094528 1095225600 14 6332 33092 30 _ _ (2081409 / 100000) (520353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095225600 :
    ThetaLowerSegment 1095225600 1095356672 (109520061980949 / 100000)
      (21906624995829 / 20000) := by
  exact
    packedTile65536 1095225600 1095356672 14 6276 33094 30 _ _ (2081421 / 100000) (130089 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095356672 :
    ThetaLowerSegment 1095356672 1095487744 (21906624995829 / 20000) (54773074252713 / 50000) := by
  exact
    packedTile65536 1095356672 1095487744 14 6257 33096 30 _ _ (2081433 / 100000) (520359 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095487744 :
    ThetaLowerSegment 1095487744 1095618816 (54773074252713 / 50000)
      (109559284504821 / 100000) := by
  exact
    packedTile65536 1095487744 1095618816 14 6311 33098 30 _ _ (416289 / 20000) (260181 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095618816 :
    ThetaLowerSegment 1095618816 1095749888 (109559284504821 / 100000)
      (109572210352791 / 100000) := by
  exact
    packedTile65536 1095618816 1095749888 14 6210 33100 30 _ _ (2081457 / 100000) (104073 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095749888 :
    ThetaLowerSegment 1095749888 1095880960 (109572210352791 / 100000) (684908285556 / 625) := by
  exact
    packedTile65536 1095749888 1095880960 14 6301 33102 30 _ _ (2081469 / 100000) (65046 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1095880960 :
    ThetaLowerSegment 1095880960 1096012032 (684908285556 / 625) (3424953561018 / 3125) := by
  exact
    packedTile65536 1095880960 1096012032 14 6336 33104 30 _ _ (2081481 / 100000) (520371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096012032 :
    ThetaLowerSegment 1096012032 1096143104 (3424953561018 / 3125) (109611608625039 / 100000) := by
  exact
    packedTile65536 1096012032 1096143104 14 6291 33106 30 _ _ (2081493 / 100000) (260187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096143104 :
    ThetaLowerSegment 1096143104 1096274176 (109611608625039 / 100000)
      (54812364175527 / 50000) := by
  exact
    packedTile65536 1096143104 1096274176 14 6303 33108 30 _ _ (416301 / 20000) (520377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096274176 :
    ThetaLowerSegment 1096274176 1096405248 (54812364175527 / 50000)
      (109638039652269 / 100000) := by
  exact
    packedTile65536 1096274176 1096405248 14 6395 33110 30 _ _ (2081517 / 100000) (26019 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096405248 :
    ThetaLowerSegment 1096405248 1096536320 (109638039652269 / 100000) (1096510263117 / 1000) := by
  exact
    packedTile65536 1096405248 1096536320 14 6239 33112 30 _ _ (2081529 / 100000) (520383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096536320 :
    ThetaLowerSegment 1096536320 1096667392 (1096510263117 / 1000) (27416037086541 / 25000) := by
  exact
    packedTile65536 1096536320 1096667392 14 6304 33113 30 _ _ (2081541 / 100000) (260193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096667392 :
    ThetaLowerSegment 1096667392 1096798464 (27416037086541 / 25000)
      (109677310005783 / 100000) := by
  exact
    packedTile65536 1096667392 1096798464 14 6323 33115 30 _ _ (2081553 / 100000) (520389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096798464 :
    ThetaLowerSegment 1096798464 1096929536 (109677310005783 / 100000) (6855657866373 / 6250) := by
  exact
    packedTile65536 1096798464 1096929536 14 6349 33117 30 _ _ (416313 / 20000) (65049 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1096929536 :
    ThetaLowerSegment 1096929536 1097060608 (6855657866373 / 6250) (109703708489109 / 100000) := by
  exact
    packedTile65536 1096929536 1097060608 14 6333 33119 30 _ _ (2081577 / 100000) (104079 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097060608 :
    ThetaLowerSegment 1097060608 1097191680 (109703708489109 / 100000)
      (109716730909893 / 100000) := by
  exact
    packedTile65536 1097060608 1097191680 14 6256 33121 30 _ _ (2081589 / 100000) (260199 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097191680 :
    ThetaLowerSegment 1097191680 1097322752 (109716730909893 / 100000)
      (109729922009093 / 100000) := by
  exact
    packedTile65536 1097191680 1097322752 14 6337 33123 30 _ _ (2602 / 125) (2081603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097322752 :
    ThetaLowerSegment 1097322752 1097339136 (109729922009093 / 100000)
      (109731566482573 / 100000) := by
  exact
    packedTile65536 1097322752 1097339136 11 790 33125 30 _ _ (520403 / 25000) (416323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097339136 :
    ThetaLowerSegment 1097339136 1097341184 (109731566482573 / 100000)
      (109731766317517 / 100000) := by
  exact
    packedTile65536 1097339136 1097341184 8 96 33126 30 _ _ (1040807 / 50000) (2081617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1065341184_1097341184 :
    ThetaLowerSegment 1065341184 1097341184 (13316273891833 / 12500)
      (109731766317517 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1065341184 cell1065406720)
                    (ThetaLowerSegment.join cell1065472256 cell1065537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1065603328 cell1065668864)
                    (ThetaLowerSegment.join cell1065734400 cell1065799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1065865472 cell1065931008)
                    (ThetaLowerSegment.join cell1065996544 cell1066062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1066127616 cell1066193152)
                    (ThetaLowerSegment.join cell1066258688 cell1066324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1066389760 cell1066455296)
                    (ThetaLowerSegment.join cell1066520832 cell1066586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1066651904 cell1066717440)
                    (ThetaLowerSegment.join cell1066782976 cell1066848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1066914048 cell1066979584)
                    (ThetaLowerSegment.join cell1067045120 cell1067110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1067176192 cell1067241728)
                    (ThetaLowerSegment.join cell1067307264 cell1067372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1067438336 cell1067503872)
                    (ThetaLowerSegment.join cell1067569408 cell1067634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1067700480 cell1067766016)
                    (ThetaLowerSegment.join cell1067831552 cell1067897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1067962624 cell1068028160)
                    (ThetaLowerSegment.join cell1068093696 cell1068159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1068224768 cell1068290304)
                    (ThetaLowerSegment.join cell1068355840 cell1068421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1068486912 cell1068552448)
                    (ThetaLowerSegment.join cell1068617984 cell1068683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1068749056 cell1068880128)
                    (ThetaLowerSegment.join cell1068945664 cell1069076736)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1069207808 cell1069273344)
                    (ThetaLowerSegment.join cell1069338880 cell1069469952))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1069601024 cell1069732096)
                    (ThetaLowerSegment.join cell1069797632 cell1069863168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1069928704 cell1069994240)
                    (ThetaLowerSegment.join cell1070059776 cell1070125312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1070190848 cell1070256384)
                    (ThetaLowerSegment.join cell1070321920 cell1070387456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1070518528 cell1070649600)
                    (ThetaLowerSegment.join cell1070715136 cell1070846208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1070977280 cell1071108352)
                    (ThetaLowerSegment.join cell1071239424 cell1071370496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1071501568 cell1071632640)
                    (ThetaLowerSegment.join cell1071763712 cell1071894784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1072025856 cell1072156928)
                    (ThetaLowerSegment.join cell1072288000 cell1072419072)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1072550144 cell1072681216)
                    (ThetaLowerSegment.join cell1072812288 cell1072943360))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1073074432 cell1073205504)
                    (ThetaLowerSegment.join cell1073336576 cell1073467648)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1073598720 cell1073729792)
                    (ThetaLowerSegment.join cell1073860864 cell1073991936))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1074057472 cell1074188544)
                    (ThetaLowerSegment.join cell1074319616 cell1074450688)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1074581760 cell1074712832)
                    (ThetaLowerSegment.join cell1074843904 cell1074974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1075106048 cell1075237120)
                    (ThetaLowerSegment.join cell1075302656 cell1075368192))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1075433728 cell1075499264)
                    (ThetaLowerSegment.join cell1075564800 cell1075630336))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1075695872 cell1075761408)
                    (ThetaLowerSegment.join cell1075826944 cell1075892480)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1075958016 cell1076023552)
                    (ThetaLowerSegment.join cell1076089088 cell1076154624))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1076220160 cell1076285696)
                    (ThetaLowerSegment.join cell1076351232 cell1076416768)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1076482304 cell1076547840)
                    (ThetaLowerSegment.join cell1076613376 cell1076678912))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1076744448 cell1076809984)
                    (ThetaLowerSegment.join cell1076875520 cell1076941056)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1077006592 cell1077072128)
                    (ThetaLowerSegment.join cell1077137664 cell1077203200))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1077268736 cell1077334272)
                    (ThetaLowerSegment.join cell1077399808 cell1077465344))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1077530880 cell1077596416)
                    (ThetaLowerSegment.join cell1077661952 cell1077727488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1077793024 cell1077858560)
                    (ThetaLowerSegment.join cell1077924096 cell1077989632)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1078055168 cell1078120704)
                    (ThetaLowerSegment.join cell1078186240 cell1078251776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1078317312 cell1078382848)
                    (ThetaLowerSegment.join cell1078448384 cell1078513920)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1078579456 cell1078644992)
                    (ThetaLowerSegment.join cell1078710528 cell1078776064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1078841600 cell1078907136)
                    (ThetaLowerSegment.join cell1078972672 cell1079038208)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1079103744 cell1079169280)
                    (ThetaLowerSegment.join cell1079234816 cell1079300352))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1079365888 cell1079431424)
                    (ThetaLowerSegment.join cell1079496960 cell1079562496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1079628032 cell1079693568)
                    (ThetaLowerSegment.join cell1079759104 cell1079824640))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1079890176 cell1079955712)
                    (ThetaLowerSegment.join cell1080021248 cell1080086784)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1080152320 cell1080217856)
                    (ThetaLowerSegment.join cell1080283392 cell1080348928))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1080414464 cell1080480000)
                    (ThetaLowerSegment.join cell1080545536 cell1080611072))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1080676608 cell1080742144)
                    (ThetaLowerSegment.join cell1080807680 cell1080873216))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1080938752 cell1081004288)
                    (ThetaLowerSegment.join cell1081069824 cell1081135360)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1081200896 cell1081266432)
                    (ThetaLowerSegment.join cell1081331968 cell1081397504))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1081463040 cell1081528576)
                    (ThetaLowerSegment.join cell1081594112 cell1081659648))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1081725184 cell1081790720)
                    (ThetaLowerSegment.join cell1081856256 cell1081921792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1081987328 cell1082052864)
                    (ThetaLowerSegment.join cell1082118400 cell1082183936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1082249472 cell1082315008)
                    (ThetaLowerSegment.join cell1082446080 cell1082577152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1082708224 cell1082773760)
                    (ThetaLowerSegment.join cell1082839296 cell1082904832)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1082970368 cell1083101440)
                    (ThetaLowerSegment.join cell1083166976 cell1083298048))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1083429120 cell1083560192)
                    (ThetaLowerSegment.join cell1083691264 cell1083822336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1083953408 cell1084084480)
                    (ThetaLowerSegment.join cell1084215552 cell1084346624))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1084477696 cell1084608768)
                    (ThetaLowerSegment.join cell1084739840 cell1084870912))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1085001984 cell1085133056)
                    (ThetaLowerSegment.join cell1085264128 cell1085395200))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1085526272 cell1085657344)
                    (ThetaLowerSegment.join cell1085788416 cell1085919488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1086050560 cell1086181632)
                    (ThetaLowerSegment.join cell1086312704 cell1086443776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1086574848 cell1086705920)
                    (ThetaLowerSegment.join cell1086836992 cell1086968064))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1087099136 cell1087230208)
                  (ThetaLowerSegment.join cell1087361280 cell1087492352))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1087623424 cell1087754496)
                  (ThetaLowerSegment.join cell1087885568 cell1088016640)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1088147712 cell1088278784)
                  (ThetaLowerSegment.join cell1088409856 cell1088540928))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1088672000 cell1088803072)
                  (ThetaLowerSegment.join cell1088934144 cell1089065216))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1089196288 cell1089327360)
                  (ThetaLowerSegment.join cell1089458432 cell1089589504))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1089720576 cell1089851648)
                  (ThetaLowerSegment.join cell1089982720 cell1090113792)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1090244864 cell1090375936)
                  (ThetaLowerSegment.join cell1090507008 cell1090638080))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1090769152 cell1090900224)
                  (ThetaLowerSegment.join cell1091031296 cell1091162368)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1091293440 cell1091424512)
                  (ThetaLowerSegment.join cell1091555584 cell1091686656))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1091817728 cell1091948800)
                  (ThetaLowerSegment.join cell1092079872 cell1092210944)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1092342016 cell1092473088)
                  (ThetaLowerSegment.join cell1092604160 cell1092735232))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1092866304 cell1092997376)
                  (ThetaLowerSegment.join cell1093128448 cell1093259520))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1093390592 cell1093521664)
                  (ThetaLowerSegment.join cell1093652736 cell1093783808))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1093914880 cell1094045952)
                  (ThetaLowerSegment.join cell1094177024 cell1094308096)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1094439168 cell1094570240)
                  (ThetaLowerSegment.join cell1094701312 cell1094832384))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1094963456 cell1095094528)
                  (ThetaLowerSegment.join cell1095225600 cell1095356672))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1095487744 cell1095618816)
              (ThetaLowerSegment.join cell1095749888 cell1095880960))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1096012032 cell1096143104)
              (ThetaLowerSegment.join cell1096274176 cell1096405248)))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1096536320 cell1096667392)
              (ThetaLowerSegment.join cell1096798464 cell1096929536))
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1097060608 cell1097191680)
              (ThetaLowerSegment.join cell1097322752 cell1097339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
