/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2601341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2569341184 :
    ThetaLowerSegment 2569341184 2569472256 (128464904250273 / 50000)
      (128471521321533 / 50000) := by
  exact
    packedTile65536 2569341184 2569472256 14 6108 50688 31 _ _ (216669 / 10000) (2166693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569472256 :
    ThetaLowerSegment 2569472256 2569603328 (128471521321533 / 50000)
      (128478069073823 / 50000) := by
  exact
    packedTile65536 2569472256 2569603328 14 6044 50689 31 _ _ (433339 / 20000) (1083349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569603328 :
    ThetaLowerSegment 2569603328 2569734400 (128478069073823 / 50000)
      (128484636341523 / 50000) := by
  exact
    packedTile65536 2569603328 2569734400 14 6062 50691 31 _ _ (21667 / 1000) (2166703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569734400 :
    ThetaLowerSegment 2569734400 2569865472 (128484636341523 / 50000)
      (256982439749331 / 100000) := by
  exact
    packedTile65536 2569734400 2569865472 14 6077 50692 31 _ _ (433341 / 20000) (541677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569865472 :
    ThetaLowerSegment 2569865472 2569996544 (256982439749331 / 100000)
      (256995548344831 / 100000) := by
  exact
    packedTile65536 2569865472 2569996544 14 6050 50693 31 _ _ (216671 / 10000) (2166713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2569996544 :
    ThetaLowerSegment 2569996544 2570127616 (256995548344831 / 100000)
      (257008604975447 / 100000) := by
  exact
    packedTile65536 2569996544 2570127616 14 6026 50695 31 _ _ (541679 / 25000) (2166719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570127616 :
    ThetaLowerSegment 2570127616 2570258688 (257008604975447 / 100000) (16063851550121 / 6250) := by
  exact
    packedTile65536 2570127616 2570258688 14 6009 50696 31 _ _ (2166721 / 100000) (541681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570258688 :
    ThetaLowerSegment 2570258688 2570389760 (16063851550121 / 6250) (64258650872669 / 25000) := by
  exact
    packedTile65536 2570258688 2570389760 14 5990 50697 31 _ _ (1083363 / 50000) (2166729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570389760 :
    ThetaLowerSegment 2570389760 2570520832 (64258650872669 / 25000)
      (257047762048039 / 100000) := by
  exact
    packedTile65536 2570389760 2570520832 14 6073 50699 31 _ _ (2166731 / 100000) (1083367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570520832 :
    ThetaLowerSegment 2570520832 2570651904 (257047762048039 / 100000)
      (257060920635767 / 100000) := by
  exact
    packedTile65536 2570520832 2570651904 14 6073 50700 31 _ _ (135421 / 6250) (2166739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570651904 :
    ThetaLowerSegment 2570651904 2570782976 (257060920635767 / 100000)
      (32134282657513 / 12500) := by
  exact
    packedTile65536 2570651904 2570782976 14 6157 50701 31 _ _ (2166741 / 100000) (270843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570782976 :
    ThetaLowerSegment 2570782976 2570914048 (32134282657513 / 12500) (12854363736829 / 5000) := by
  exact
    packedTile65536 2570782976 2570914048 14 6006 50702 31 _ _ (1083373 / 50000) (2166749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2570914048 :
    ThetaLowerSegment 2570914048 2571045120 (12854363736829 / 5000) (257100429081901 / 100000) := by
  exact
    packedTile65536 2570914048 2571045120 14 6071 50704 31 _ _ (2166751 / 100000) (1083377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571045120 :
    ThetaLowerSegment 2571045120 2571176192 (257100429081901 / 100000)
      (257113316946589 / 100000) := by
  exact
    packedTile65536 2571045120 2571176192 14 5948 50705 31 _ _ (541689 / 25000) (2166759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571176192 :
    ThetaLowerSegment 2571176192 2571307264 (257113316946589 / 100000)
      (257126516854601 / 100000) := by
  exact
    packedTile65536 2571176192 2571307264 14 6092 50706 31 _ _ (2166761 / 100000) (541691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571307264 :
    ThetaLowerSegment 2571307264 2571438336 (257126516854601 / 100000)
      (257139534790737 / 100000) := by
  exact
    packedTile65536 2571307264 2571438336 14 6008 50708 31 _ _ (2166767 / 100000) (216677 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571438336 :
    ThetaLowerSegment 2571438336 2571569408 (257139534790737 / 100000)
      (51430528318913 / 20000) := by
  exact
    packedTile65536 2571438336 2571569408 14 6049 50709 31 _ _ (541693 / 25000) (86671 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571569408 :
    ThetaLowerSegment 2571569408 2571700480 (51430528318913 / 20000)
      (257165542584823 / 100000) := by
  exact
    packedTile65536 2571569408 2571700480 14 5954 50710 31 _ _ (2166777 / 100000) (108339 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571700480 :
    ThetaLowerSegment 2571700480 2571831552 (257165542584823 / 100000) (2057430270317 / 800) := by
  exact
    packedTile65536 2571700480 2571831552 14 6111 50711 31 _ _ (1083391 / 50000) (433357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571831552 :
    ThetaLowerSegment 2571831552 2571962624 (2057430270317 / 800) (257191814846643 / 100000) := by
  exact
    packedTile65536 2571831552 2571962624 14 6014 50713 31 _ _ (2166787 / 100000) (216679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2571962624 :
    ThetaLowerSegment 2571962624 2572093696 (257191814846643 / 100000)
      (257204928271827 / 100000) := by
  exact
    packedTile65536 2571962624 2572093696 14 6052 50714 31 _ _ (270849 / 12500) (433359 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572093696 :
    ThetaLowerSegment 2572093696 2572224768 (257204928271827 / 100000)
      (32152260903751 / 12500) := by
  exact
    packedTile65536 2572093696 2572224768 14 6073 50715 31 _ _ (2166797 / 100000) (5417 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572224768 :
    ThetaLowerSegment 2572224768 2572355840 (32152260903751 / 12500) (32153905506469 / 12500) := by
  exact
    packedTile65536 2572224768 2572355840 14 6072 50717 31 _ _ (1083401 / 50000) (433361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572355840 :
    ThetaLowerSegment 2572355840 2572486912 (32153905506469 / 12500)
      (257244593749679 / 100000) := by
  exact
    packedTile65536 2572355840 2572486912 14 6161 50718 31 _ _ (2166807 / 100000) (216681 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572486912 :
    ThetaLowerSegment 2572486912 2572617984 (257244593749679 / 100000)
      (257257811302879 / 100000) := by
  exact
    packedTile65536 2572486912 2572617984 14 6100 50719 31 _ _ (541703 / 25000) (433363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572617984 :
    ThetaLowerSegment 2572617984 2572749056 (257257811302879 / 100000)
      (257270911878461 / 100000) := by
  exact
    packedTile65536 2572617984 2572749056 14 6046 50720 31 _ _ (2166817 / 100000) (108341 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572749056 :
    ThetaLowerSegment 2572749056 2572880128 (257270911878461 / 100000)
      (257283956152921 / 100000) := by
  exact
    packedTile65536 2572749056 2572880128 14 6020 50722 31 _ _ (2166823 / 100000) (1083413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2572880128 :
    ThetaLowerSegment 2572880128 2573011200 (257283956152921 / 100000)
      (51459427393529 / 20000) := by
  exact
    packedTile65536 2572880128 2573011200 14 6083 50723 31 _ _ (541707 / 25000) (2166831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573011200 :
    ThetaLowerSegment 2573011200 2573142272 (51459427393529 / 20000)
      (257310081627987 / 100000) := by
  exact
    packedTile65536 2573011200 2573142272 14 5974 50724 31 _ _ (2166833 / 100000) (541709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573142272 :
    ThetaLowerSegment 2573142272 2573273344 (257310081627987 / 100000)
      (51464647300297 / 20000) := by
  exact
    packedTile65536 2573142272 2573273344 14 6071 50726 31 _ _ (1083419 / 50000) (2166841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573273344 :
    ThetaLowerSegment 2573273344 2573404416 (51464647300297 / 20000)
      (257336207223683 / 100000) := by
  exact
    packedTile65536 2573273344 2573404416 14 5986 50727 31 _ _ (2166843 / 100000) (1083423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573404416 :
    ThetaLowerSegment 2573404416 2573535488 (257336207223683 / 100000)
      (257349409828547 / 100000) := by
  exact
    packedTile65536 2573404416 2573535488 14 6093 50728 31 _ _ (67714 / 3125) (2166851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573535488 :
    ThetaLowerSegment 2573535488 2573666560 (257349409828547 / 100000)
      (128681265061731 / 50000) := by
  exact
    packedTile65536 2573535488 2573666560 14 6055 50730 31 _ _ (2166853 / 100000) (270857 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573666560 :
    ThetaLowerSegment 2573666560 2573797632 (128681265061731 / 50000) (25737565261551 / 10000) := by
  exact
    packedTile65536 2573666560 2573797632 14 6056 50731 31 _ _ (1083429 / 50000) (2166861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573797632 :
    ThetaLowerSegment 2573797632 2573928704 (25737565261551 / 10000)
      (257388907316481 / 100000) := by
  exact
    packedTile65536 2573797632 2573928704 14 6117 50732 31 _ _ (2166863 / 100000) (1083433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2573928704 :
    ThetaLowerSegment 2573928704 2574059776 (257388907316481 / 100000)
      (257401854352781 / 100000) := by
  exact
    packedTile65536 2573928704 2574059776 14 5975 50733 31 _ _ (541717 / 25000) (2166871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574059776 :
    ThetaLowerSegment 2574059776 2574190848 (257401854352781 / 100000)
      (257415070117307 / 100000) := by
  exact
    packedTile65536 2574059776 2574190848 14 6099 50735 31 _ _ (1083437 / 50000) (2166877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574190848 :
    ThetaLowerSegment 2574190848 2574321920 (257415070117307 / 100000)
      (128714114786737 / 50000) := by
  exact
    packedTile65536 2574190848 2574321920 14 6073 50736 31 _ _ (2166879 / 100000) (1083441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574321920 :
    ThetaLowerSegment 2574321920 2574452992 (128714114786737 / 50000)
      (128720613271853 / 50000) := by
  exact
    packedTile65536 2574321920 2574452992 14 5998 50737 31 _ _ (541721 / 25000) (2166887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574452992 :
    ThetaLowerSegment 2574452992 2574584064 (128720613271853 / 50000)
      (257454394728159 / 100000) := by
  exact
    packedTile65536 2574452992 2574584064 14 6077 50739 31 _ _ (2166889 / 100000) (541723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574584064 :
    ThetaLowerSegment 2574584064 2574715136 (257454394728159 / 100000)
      (257467601947089 / 100000) := by
  exact
    packedTile65536 2574584064 2574715136 14 6095 50740 31 _ _ (1083447 / 50000) (2166897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574715136 :
    ThetaLowerSegment 2574715136 2574846208 (257467601947089 / 100000)
      (64370186047381 / 25000) := by
  exact
    packedTile65536 2574715136 2574846208 14 6065 50741 31 _ _ (2166899 / 100000) (1083451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574846208 :
    ThetaLowerSegment 2574846208 2574977280 (64370186047381 / 25000) (64373485158721 / 25000) := by
  exact
    packedTile65536 2574846208 2574977280 14 6090 50742 31 _ _ (270863 / 12500) (2166907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2574977280 :
    ThetaLowerSegment 2574977280 2575108352 (64373485158721 / 25000) (51501392318213 / 20000) := by
  exact
    packedTile65536 2574977280 2575108352 14 6009 50744 31 _ _ (2166909 / 100000) (67716 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575108352 :
    ThetaLowerSegment 2575108352 2575239424 (51501392318213 / 20000)
      (257520023748657 / 100000) := by
  exact
    packedTile65536 2575108352 2575239424 14 6028 50745 31 _ _ (1083457 / 50000) (2166917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575239424 :
    ThetaLowerSegment 2575239424 2575370496 (257520023748657 / 100000)
      (25753317044623 / 10000) := by
  exact
    packedTile65536 2575239424 2575370496 14 6067 50746 31 _ _ (2166919 / 100000) (1083461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575370496 :
    ThetaLowerSegment 2575370496 2575501568 (25753317044623 / 10000) (128773114165127 / 50000) := by
  exact
    packedTile65536 2575370496 2575501568 14 6026 50748 31 _ _ (541731 / 25000) (2166927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575501568 :
    ThetaLowerSegment 2575501568 2575632640 (128773114165127 / 50000) (64389854608291 / 25000) := by
  exact
    packedTile65536 2575501568 2575632640 14 6087 50749 31 _ _ (216693 / 10000) (2166933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575632640 :
    ThetaLowerSegment 2575632640 2575763712 (64389854608291 / 25000) (16098286545639 / 6250) := by
  exact
    packedTile65536 2575632640 2575763712 14 6076 50750 31 _ _ (433387 / 20000) (1083469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575763712 :
    ThetaLowerSegment 2575763712 2575894784 (16098286545639 / 6250) (32198214006593 / 12500) := by
  exact
    packedTile65536 2575763712 2575894784 14 6058 50751 31 _ _ (108347 / 5000) (2166943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2575894784 :
    ThetaLowerSegment 2575894784 2576025856 (32198214006593 / 12500) (128799333024977 / 50000) := by
  exact
    packedTile65536 2575894784 2576025856 14 5978 50753 31 _ _ (433389 / 20000) (541737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576025856 :
    ThetaLowerSegment 2576025856 2576156928 (128799333024977 / 50000) (64402933731351 / 25000) := by
  exact
    packedTile65536 2576025856 2576156928 14 6031 50754 31 _ _ (43339 / 2000) (2166953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576156928 :
    ThetaLowerSegment 2576156928 2576288000 (64402933731351 / 25000) (64406227502951 / 25000) := by
  exact
    packedTile65536 2576156928 2576288000 14 6080 50755 31 _ _ (433391 / 20000) (1083479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576288000 :
    ThetaLowerSegment 2576288000 2576419072 (64406227502951 / 25000) (64409532658691 / 25000) := by
  exact
    packedTile65536 2576288000 2576419072 14 6101 50757 31 _ _ (27087 / 1250) (2166963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576419072 :
    ThetaLowerSegment 2576419072 2576550144 (64409532658691 / 25000) (32206407805333 / 12500) := by
  exact
    packedTile65536 2576419072 2576550144 14 6060 50758 31 _ _ (433393 / 20000) (270871 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576550144 :
    ThetaLowerSegment 2576550144 2576681216 (32206407805333 / 12500) (16104023559069 / 6250) := by
  exact
    packedTile65536 2576550144 2576681216 14 6052 50759 31 _ _ (216697 / 10000) (2166973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576681216 :
    ThetaLowerSegment 2576681216 2576812288 (16104023559069 / 6250) (128838730570077 / 50000) := by
  exact
    packedTile65536 2576681216 2576812288 14 6038 50761 31 _ _ (86679 / 4000) (1083489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576812288 :
    ThetaLowerSegment 2576812288 2576943360 (128838730570077 / 50000)
      (128845170834637 / 50000) := by
  exact
    packedTile65536 2576812288 2576943360 14 5944 50762 31 _ _ (108349 / 5000) (2166983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2576943360 :
    ThetaLowerSegment 2576943360 2577074432 (128845170834637 / 50000)
      (128851723797277 / 50000) := by
  exact
    packedTile65536 2576943360 2577074432 14 6048 50763 31 _ _ (433397 / 20000) (541747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577074432 :
    ThetaLowerSegment 2577074432 2577205504 (128851723797277 / 50000)
      (257716590394969 / 100000) := by
  exact
    packedTile65536 2577074432 2577205504 14 6065 50764 31 _ _ (2166991 / 100000) (1083497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577205504 :
    ThetaLowerSegment 2577205504 2577336576 (257716590394969 / 100000)
      (257729917420369 / 100000) := by
  exact
    packedTile65536 2577205504 2577336576 14 6150 50766 31 _ _ (541749 / 25000) (2166999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577336576 :
    ThetaLowerSegment 2577336576 2577467648 (257729917420369 / 100000)
      (51548599487681 / 20000) := by
  exact
    packedTile65536 2577336576 2577467648 14 6036 50767 31 _ _ (2167001 / 100000) (541751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577467648 :
    ThetaLowerSegment 2577467648 2577598720 (51548599487681 / 20000)
      (257755938798237 / 100000) := by
  exact
    packedTile65536 2577467648 2577598720 14 5972 50768 31 _ _ (1083503 / 50000) (2167009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577598720 :
    ThetaLowerSegment 2577598720 2577729792 (257755938798237 / 100000)
      (25776907738593 / 10000) := by
  exact
    packedTile65536 2577598720 2577729792 14 6063 50770 31 _ _ (2167011 / 100000) (1083507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577729792 :
    ThetaLowerSegment 2577729792 2577860864 (25776907738593 / 10000) (128891135089669 / 50000) := by
  exact
    packedTile65536 2577729792 2577860864 14 6088 50771 31 _ _ (270877 / 12500) (2167019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577860864 :
    ThetaLowerSegment 2577860864 2577991936 (128891135089669 / 50000) (51559092167233 / 20000) := by
  exact
    packedTile65536 2577860864 2577991936 14 6087 50772 31 _ _ (2167021 / 100000) (135439 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2577991936 :
    ThetaLowerSegment 2577991936 2578123008 (51559092167233 / 20000)
      (257808530169971 / 100000) := by
  exact
    packedTile65536 2577991936 2578123008 14 6031 50773 31 _ _ (1083513 / 50000) (2167029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578123008 :
    ThetaLowerSegment 2578123008 2578254080 (257808530169971 / 100000)
      (257821662377831 / 100000) := by
  exact
    packedTile65536 2578123008 2578254080 14 6060 50775 31 _ _ (2167031 / 100000) (1083517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578254080 :
    ThetaLowerSegment 2578254080 2578385152 (257821662377831 / 100000)
      (257834798950063 / 100000) := by
  exact
    packedTile65536 2578254080 2578385152 14 6062 50776 31 _ _ (541759 / 25000) (2167039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578385152 :
    ThetaLowerSegment 2578385152 2578516224 (257834798950063 / 100000) (2062782964331 / 800) := by
  exact
    packedTile65536 2578385152 2578516224 14 6032 50777 31 _ _ (2167041 / 100000) (541761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578516224 :
    ThetaLowerSegment 2578516224 2578647296 (2062782964331 / 800) (257860961666261 / 100000) := by
  exact
    packedTile65536 2578516224 2578647296 14 6041 50779 31 _ _ (1083523 / 50000) (2167049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578647296 :
    ThetaLowerSegment 2578647296 2578778368 (257860961666261 / 100000)
      (257874002985197 / 100000) := by
  exact
    packedTile65536 2578647296 2578778368 14 6018 50780 31 _ _ (541763 / 25000) (433411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578778368 :
    ThetaLowerSegment 2578778368 2578909440 (257874002985197 / 100000)
      (64471720451237 / 25000) := by
  exact
    packedTile65536 2578778368 2578909440 14 5943 50781 31 _ _ (2167057 / 100000) (108353 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2578909440 :
    ThetaLowerSegment 2578909440 2579040512 (64471720451237 / 25000) (8059376933626 / 3125) := by
  exact
    packedTile65536 2578909440 2579040512 14 6082 50782 31 _ _ (1083531 / 50000) (433413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579040512 :
    ThetaLowerSegment 2579040512 2579171584 (8059376933626 / 3125) (257913218139789 / 100000) := by
  exact
    packedTile65536 2579040512 2579171584 14 6071 50784 31 _ _ (2167067 / 100000) (216707 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579171584 :
    ThetaLowerSegment 2579171584 2579302656 (257913218139789 / 100000)
      (51585258417033 / 20000) := by
  exact
    packedTile65536 2579171584 2579302656 14 6033 50785 31 _ _ (67721 / 3125) (86683 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579302656 :
    ThetaLowerSegment 2579302656 2579433728 (51585258417033 / 20000)
      (257939151520083 / 100000) := by
  exact
    packedTile65536 2579302656 2579433728 14 5934 50786 31 _ _ (2167077 / 100000) (54177 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579433728 :
    ThetaLowerSegment 2579433728 2579564800 (257939151520083 / 100000)
      (257952548421007 / 100000) := by
  exact
    packedTile65536 2579433728 2579564800 14 6182 50788 31 _ _ (1083541 / 50000) (433417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579564800 :
    ThetaLowerSegment 2579564800 2579695872 (257952548421007 / 100000)
      (257965680968227 / 100000) := by
  exact
    packedTile65536 2579564800 2579695872 14 6060 50789 31 _ _ (2167087 / 100000) (216709 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579695872 :
    ThetaLowerSegment 2579695872 2579826944 (257965680968227 / 100000)
      (257978807044471 / 100000) := by
  exact
    packedTile65536 2579695872 2579826944 14 6057 50790 31 _ _ (541773 / 25000) (433419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579826944 :
    ThetaLowerSegment 2579826944 2579958016 (257978807044471 / 100000)
      (51598393131491 / 20000) := by
  exact
    packedTile65536 2579826944 2579958016 14 6072 50791 31 _ _ (2167097 / 100000) (21671 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2579958016 :
    ThetaLowerSegment 2579958016 2580089088 (51598393131491 / 20000)
      (258004929261619 / 100000) := by
  exact
    packedTile65536 2579958016 2580089088 14 5982 50793 31 _ _ (1083551 / 50000) (433421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580089088 :
    ThetaLowerSegment 2580089088 2580220160 (258004929261619 / 100000)
      (258017936237833 / 100000) := by
  exact
    packedTile65536 2580089088 2580220160 14 6002 50794 31 _ _ (2167107 / 100000) (216711 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580220160 :
    ThetaLowerSegment 2580220160 2580351232 (258017936237833 / 100000)
      (51606241527569 / 20000) := by
  exact
    packedTile65536 2580220160 2580351232 14 6124 50795 31 _ _ (2167113 / 100000) (541779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580351232 :
    ThetaLowerSegment 2580351232 2580482304 (51606241527569 / 20000) (10321773614917 / 4000) := by
  exact
    packedTile65536 2580351232 2580482304 14 6060 50797 31 _ _ (1083559 / 50000) (2167121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580482304 :
    ThetaLowerSegment 2580482304 2580613376 (10321773614917 / 4000) (258057460135567 / 100000) := by
  exact
    packedTile65536 2580482304 2580613376 14 6054 50798 31 _ _ (2167123 / 100000) (1083563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580613376 :
    ThetaLowerSegment 2580613376 2580744448 (258057460135567 / 100000)
      (258070582095607 / 100000) := by
  exact
    packedTile65536 2580613376 2580744448 14 6055 50799 31 _ _ (270891 / 12500) (2167131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580744448 :
    ThetaLowerSegment 2580744448 2580875520 (258070582095607 / 100000)
      (258083680247459 / 100000) := by
  exact
    packedTile65536 2580744448 2580875520 14 6044 50801 31 _ _ (2167133 / 100000) (67723 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2580875520 :
    ThetaLowerSegment 2580875520 2581006592 (258083680247459 / 100000)
      (258096680908321 / 100000) := by
  exact
    packedTile65536 2580875520 2581006592 14 5999 50802 31 _ _ (1083569 / 50000) (2167141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581006592 :
    ThetaLowerSegment 2581006592 2581137664 (258096680908321 / 100000)
      (258109649092033 / 100000) := by
  exact
    packedTile65536 2581006592 2581137664 14 5984 50803 31 _ _ (2167143 / 100000) (1083573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581137664 :
    ThetaLowerSegment 2581137664 2581268736 (258109649092033 / 100000)
      (258122946712161 / 100000) := by
  exact
    packedTile65536 2581137664 2581268736 14 6136 50804 31 _ _ (541787 / 25000) (2167151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581268736 :
    ThetaLowerSegment 2581268736 2581399808 (258122946712161 / 100000)
      (258136083993647 / 100000) := by
  exact
    packedTile65536 2581268736 2581399808 14 6062 50806 31 _ _ (2167153 / 100000) (541789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581399808 :
    ThetaLowerSegment 2581399808 2581530880 (258136083993647 / 100000)
      (258149203968179 / 100000) := by
  exact
    packedTile65536 2581399808 2581530880 14 6054 50807 31 _ _ (1083579 / 50000) (2167161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581530880 :
    ThetaLowerSegment 2581530880 2581661952 (258149203968179 / 100000)
      (258162371650567 / 100000) := by
  exact
    packedTile65536 2581530880 2581661952 14 6076 50808 31 _ _ (2167163 / 100000) (1083583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581661952 :
    ThetaLowerSegment 2581661952 2581793024 (258162371650567 / 100000)
      (258175621715719 / 100000) := by
  exact
    packedTile65536 2581661952 2581793024 14 6114 50810 31 _ _ (67724 / 3125) (2167171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581793024 :
    ThetaLowerSegment 2581793024 2581924096 (258175621715719 / 100000)
      (129094415317577 / 50000) := by
  exact
    packedTile65536 2581793024 2581924096 14 6095 50811 31 _ _ (2167173 / 100000) (270897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2581924096 :
    ThetaLowerSegment 2581924096 2582055168 (129094415317577 / 50000)
      (258201870551197 / 100000) := by
  exact
    packedTile65536 2581924096 2582055168 14 6017 50812 31 _ _ (2167179 / 100000) (1083591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582055168 :
    ThetaLowerSegment 2582055168 2582186240 (258201870551197 / 100000)
      (258214847648989 / 100000) := by
  exact
    packedTile65536 2582055168 2582186240 14 5988 50813 31 _ _ (135449 / 6250) (2167187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582186240 :
    ThetaLowerSegment 2582186240 2582317312 (258214847648989 / 100000)
      (32278507083243 / 12500) := by
  exact
    packedTile65536 2582186240 2582317312 14 6095 50815 31 _ _ (2167189 / 100000) (270899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582317312 :
    ThetaLowerSegment 2582317312 2582448384 (32278507083243 / 12500) (64560302883381 / 25000) := by
  exact
    packedTile65536 2582317312 2582448384 14 6070 50816 31 _ _ (1083597 / 50000) (2167197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582448384 :
    ThetaLowerSegment 2582448384 2582579456 (64560302883381 / 25000) (129127118199757 / 50000) := by
  exact
    packedTile65536 2582448384 2582579456 14 6010 50817 31 _ _ (2167199 / 100000) (1083601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582579456 :
    ThetaLowerSegment 2582579456 2582710528 (129127118199757 / 50000)
      (129133676159061 / 50000) := by
  exact
    packedTile65536 2582579456 2582710528 14 6052 50819 31 _ _ (541801 / 25000) (2167207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582710528 :
    ThetaLowerSegment 2582710528 2582841600 (129133676159061 / 50000) (12914017995327 / 5000) := by
  exact
    packedTile65536 2582710528 2582841600 14 6002 50820 31 _ _ (2167209 / 100000) (541803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582841600 :
    ThetaLowerSegment 2582841600 2582972672 (12914017995327 / 5000) (64573366804203 / 25000) := by
  exact
    packedTile65536 2582841600 2582972672 14 6048 50821 31 _ _ (1083607 / 50000) (2167217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2582972672 :
    ThetaLowerSegment 2582972672 2583103744 (64573366804203 / 25000) (129153376134641 / 50000) := by
  exact
    packedTile65536 2582972672 2583103744 14 6130 50822 31 _ _ (2167219 / 100000) (1083611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583103744 :
    ThetaLowerSegment 2583103744 2583234816 (129153376134641 / 50000) (25831978161997 / 10000) := by
  exact
    packedTile65536 2583103744 2583234816 14 6012 50824 31 _ _ (270903 / 12500) (2167227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583234816 :
    ThetaLowerSegment 2583234816 2583365888 (25831978161997 / 10000) (129166422838191 / 50000) := by
  exact
    packedTile65536 2583234816 2583365888 14 6028 50825 31 _ _ (2167229 / 100000) (67726 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583365888 :
    ThetaLowerSegment 2583365888 2583496960 (129166422838191 / 50000)
      (129172967884871 / 50000) := by
  exact
    packedTile65536 2583365888 2583496960 14 6040 50826 31 _ _ (1083617 / 50000) (2167237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583496960 :
    ThetaLowerSegment 2583496960 2583628032 (129172967884871 / 50000)
      (258359010722629 / 100000) := by
  exact
    packedTile65536 2583496960 2583628032 14 6033 50828 31 _ _ (2167239 / 100000) (1083621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583628032 :
    ThetaLowerSegment 2583628032 2583759104 (258359010722629 / 100000)
      (258372005523649 / 100000) := by
  exact
    packedTile65536 2583628032 2583759104 14 5996 50829 31 _ _ (433449 / 20000) (135453 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583759104 :
    ThetaLowerSegment 2583759104 2583890176 (258372005523649 / 100000)
      (258385243086649 / 100000) := by
  exact
    packedTile65536 2583759104 2583890176 14 6108 50830 31 _ _ (8669 / 400) (2167253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2583890176 :
    ThetaLowerSegment 2583890176 2584021248 (258385243086649 / 100000)
      (258398276958219 / 100000) := by
  exact
    packedTile65536 2583890176 2584021248 14 6014 50831 31 _ _ (433451 / 20000) (1083629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584021248 :
    ThetaLowerSegment 2584021248 2584152320 (258398276958219 / 100000)
      (258411490742439 / 100000) := by
  exact
    packedTile65536 2584021248 2584152320 14 6097 50833 31 _ _ (108363 / 5000) (2167263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584152320 :
    ThetaLowerSegment 2584152320 2584283392 (258411490742439 / 100000)
      (129212315435067 / 50000) := by
  exact
    packedTile65536 2584152320 2584283392 14 6063 50834 31 _ _ (433453 / 20000) (541817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584283392 :
    ThetaLowerSegment 2584283392 2584414464 (129212315435067 / 50000) (64609428669781 / 25000) := by
  exact
    packedTile65536 2584283392 2584414464 14 6037 50835 31 _ _ (216727 / 10000) (2167273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584414464 :
    ThetaLowerSegment 2584414464 2584545536 (64609428669781 / 25000)
      (258450781180099 / 100000) := by
  exact
    packedTile65536 2584414464 2584545536 14 6029 50837 31 _ _ (86691 / 4000) (1083639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584545536 :
    ThetaLowerSegment 2584545536 2584676608 (258450781180099 / 100000)
      (258463839042099 / 100000) := by
  exact
    packedTile65536 2584545536 2584676608 14 6025 50838 31 _ _ (27091 / 1250) (2167283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584676608 :
    ThetaLowerSegment 2584676608 2584807680 (258463839042099 / 100000)
      (258477029138609 / 100000) := by
  exact
    packedTile65536 2584676608 2584807680 14 6086 50839 31 _ _ (433457 / 20000) (270911 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584807680 :
    ThetaLowerSegment 2584807680 2584938752 (258477029138609 / 100000)
      (258490186756199 / 100000) := by
  exact
    packedTile65536 2584807680 2584938752 14 6071 50841 31 _ _ (216729 / 10000) (2167293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2584938752 :
    ThetaLowerSegment 2584938752 2585069824 (258490186756199 / 100000)
      (258503177522429 / 100000) := by
  exact
    packedTile65536 2584938752 2585069824 14 5994 50842 31 _ _ (433459 / 20000) (1083649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585069824 :
    ThetaLowerSegment 2585069824 2585200896 (258503177522429 / 100000)
      (258516346037229 / 100000) := by
  exact
    packedTile65536 2585069824 2585200896 14 6076 50843 31 _ _ (21673 / 1000) (2167303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585200896 :
    ThetaLowerSegment 2585200896 2585331968 (258516346037229 / 100000)
      (258529354201839 / 100000) := by
  exact
    packedTile65536 2585200896 2585331968 14 6002 50844 31 _ _ (433461 / 20000) (541827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585331968 :
    ThetaLowerSegment 2585331968 2585463040 (258529354201839 / 100000)
      (258542600800559 / 100000) := by
  exact
    packedTile65536 2585331968 2585463040 14 6112 50846 31 _ _ (216731 / 10000) (2167313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585463040 :
    ThetaLowerSegment 2585463040 2585594112 (258542600800559 / 100000)
      (258555665381407 / 100000) := by
  exact
    packedTile65536 2585463040 2585594112 14 6028 50847 31 _ _ (541829 / 25000) (2167319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585594112 :
    ThetaLowerSegment 2585594112 2585725184 (258555665381407 / 100000)
      (64642191709213 / 25000) := by
  exact
    packedTile65536 2585594112 2585725184 14 6045 50848 31 _ _ (2167321 / 100000) (541831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585725184 :
    ThetaLowerSegment 2585725184 2585856256 (64642191709213 / 25000) (64645418857627 / 25000) := by
  exact
    packedTile65536 2585725184 2585856256 14 5956 50850 31 _ _ (1083663 / 50000) (2167329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585856256 :
    ThetaLowerSegment 2585856256 2585987328 (64645418857627 / 25000)
      (258594742269107 / 100000) := by
  exact
    packedTile65536 2585856256 2585987328 14 6029 50851 31 _ _ (2167331 / 100000) (1083667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2585987328 :
    ThetaLowerSegment 2585987328 2586118400 (258594742269107 / 100000)
      (258607878492603 / 100000) := by
  exact
    packedTile65536 2585987328 2586118400 14 6061 50852 31 _ _ (270917 / 12500) (2167339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586118400 :
    ThetaLowerSegment 2586118400 2586249472 (258607878492603 / 100000)
      (258621029917791 / 100000) := by
  exact
    packedTile65536 2586118400 2586249472 14 6068 50853 31 _ _ (2167341 / 100000) (135459 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586249472 :
    ThetaLowerSegment 2586249472 2586380544 (258621029917791 / 100000)
      (258634138026399 / 100000) := by
  exact
    packedTile65536 2586249472 2586380544 14 6048 50855 31 _ _ (1083673 / 50000) (2167349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586380544 :
    ThetaLowerSegment 2586380544 2586511616 (258634138026399 / 100000)
      (64661808832123 / 25000) := by
  exact
    packedTile65536 2586380544 2586511616 14 6043 50856 31 _ _ (2167351 / 100000) (1083677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586511616 :
    ThetaLowerSegment 2586511616 2586642688 (64661808832123 / 25000) (12933025844303 / 5000) := by
  exact
    packedTile65536 2586511616 2586642688 14 6128 50857 31 _ _ (541839 / 25000) (2167359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586642688 :
    ThetaLowerSegment 2586642688 2586773760 (12933025844303 / 5000) (51734702043051 / 20000) := by
  exact
    packedTile65536 2586642688 2586773760 14 5995 50859 31 _ _ (2167361 / 100000) (541841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586773760 :
    ThetaLowerSegment 2586773760 2586904832 (51734702043051 / 20000)
      (258686551256477 / 100000) := by
  exact
    packedTile65536 2586773760 2586904832 14 6017 50860 31 _ _ (1083683 / 50000) (2167369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2586904832 :
    ThetaLowerSegment 2586904832 2587035904 (258686551256477 / 100000)
      (25869964867943 / 10000) := by
  exact
    packedTile65536 2586904832 2587035904 14 6043 50861 31 _ _ (2167371 / 100000) (1083687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587035904 :
    ThetaLowerSegment 2587035904 2587166976 (25869964867943 / 10000) (129356244107427 / 50000) := by
  exact
    packedTile65536 2587035904 2587166976 14 5924 50862 31 _ _ (135461 / 6250) (2167379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587166976 :
    ThetaLowerSegment 2587166976 2587298048 (129356244107427 / 50000)
      (258725611706809 / 100000) := by
  exact
    packedTile65536 2587166976 2587298048 14 6055 50864 31 _ _ (2167381 / 100000) (270923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587298048 :
    ThetaLowerSegment 2587298048 2587429120 (258725611706809 / 100000)
      (258738687546547 / 100000) := by
  exact
    packedTile65536 2587298048 2587429120 14 6033 50865 31 _ _ (1083693 / 50000) (2167389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587429120 :
    ThetaLowerSegment 2587429120 2587560192 (258738687546547 / 100000)
      (258751882629043 / 100000) := by
  exact
    packedTile65536 2587429120 2587560192 14 6088 50866 31 _ _ (67731 / 3125) (433479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587560192 :
    ThetaLowerSegment 2587560192 2587691264 (258751882629043 / 100000)
      (51753036355407 / 20000) := by
  exact
    packedTile65536 2587560192 2587691264 14 6136 50868 31 _ _ (2167397 / 100000) (10837 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587691264 :
    ThetaLowerSegment 2587691264 2587822336 (51753036355407 / 20000)
      (258778307563547 / 100000) := by
  exact
    packedTile65536 2587691264 2587822336 14 6056 50869 31 _ _ (1083701 / 50000) (433481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587822336 :
    ThetaLowerSegment 2587822336 2587953408 (258778307563547 / 100000)
      (32348923483099 / 12500) := by
  exact
    packedTile65536 2587822336 2587953408 14 6035 50870 31 _ _ (2167407 / 100000) (216741 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2587953408 :
    ThetaLowerSegment 2587953408 2588084480 (32348923483099 / 12500) (64701147392821 / 25000) := by
  exact
    packedTile65536 2587953408 2588084480 14 6091 50871 31 _ _ (541853 / 25000) (433483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588084480 :
    ThetaLowerSegment 2588084480 2588215552 (64701147392821 / 25000) (64704407187989 / 25000) := by
  exact
    packedTile65536 2588084480 2588215552 14 6016 50873 31 _ _ (2167417 / 100000) (108371 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588215552 :
    ThetaLowerSegment 2588215552 2588346624 (64704407187989 / 25000) (129415296051469 / 50000) := by
  exact
    packedTile65536 2588215552 2588346624 14 5981 50874 31 _ _ (1083711 / 50000) (86697 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588346624 :
    ThetaLowerSegment 2588346624 2588477696 (129415296051469 / 50000)
      (258843746217401 / 100000) := by
  exact
    packedTile65536 2588346624 2588477696 14 6069 50875 31 _ _ (2167427 / 100000) (216743 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588477696 :
    ThetaLowerSegment 2588477696 2588608768 (258843746217401 / 100000)
      (51771390042629 / 20000) := by
  exact
    packedTile65536 2588477696 2588608768 14 6092 50877 31 _ _ (270929 / 12500) (433487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588608768 :
    ThetaLowerSegment 2588608768 2588739840 (51771390042629 / 20000)
      (258869937495649 / 100000) := by
  exact
    packedTile65536 2588608768 2588739840 14 5992 50878 31 _ _ (2167437 / 100000) (27093 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588739840 :
    ThetaLowerSegment 2588739840 2588870912 (258869937495649 / 100000)
      (258883061356959 / 100000) := by
  exact
    packedTile65536 2588739840 2588870912 14 6055 50879 31 _ _ (1083721 / 50000) (433489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2588870912 :
    ThetaLowerSegment 2588870912 2589001984 (258883061356959 / 100000)
      (129448086121931 / 50000) := by
  exact
    packedTile65536 2588870912 2589001984 14 6049 50880 31 _ _ (2167447 / 100000) (43349 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589001984 :
    ThetaLowerSegment 2589001984 2589133056 (129448086121931 / 50000)
      (129454579808123 / 50000) := by
  exact
    packedTile65536 2589001984 2589133056 14 5992 50882 31 _ _ (541863 / 25000) (433491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589133056 :
    ThetaLowerSegment 2589133056 2589264128 (129454579808123 / 50000)
      (129461194886887 / 50000) := by
  exact
    packedTile65536 2589133056 2589264128 14 6104 50883 31 _ _ (2167457 / 100000) (108373 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589264128 :
    ThetaLowerSegment 2589264128 2589395200 (129461194886887 / 50000) (16183480988937 / 6250) := by
  exact
    packedTile65536 2589264128 2589395200 14 6139 50884 31 _ _ (1083731 / 50000) (433493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589395200 :
    ThetaLowerSegment 2589395200 2589526272 (16183480988937 / 6250) (1618429324757 / 625) := by
  exact
    packedTile65536 2589395200 2589526272 14 5996 50886 31 _ _ (541867 / 25000) (2167471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589526272 :
    ThetaLowerSegment 2589526272 2589657344 (1618429324757 / 625) (258961742316053 / 100000) := by
  exact
    packedTile65536 2589526272 2589657344 14 6021 50887 31 _ _ (2167473 / 100000) (541869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589657344 :
    ThetaLowerSegment 2589657344 2589788416 (258961742316053 / 100000)
      (258974838218129 / 100000) := by
  exact
    packedTile65536 2589657344 2589788416 14 6042 50888 31 _ _ (1083739 / 50000) (2167481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589788416 :
    ThetaLowerSegment 2589788416 2589919488 (258974838218129 / 100000)
      (258987968830143 / 100000) := by
  exact
    packedTile65536 2589788416 2589919488 14 6058 50889 31 _ _ (2167483 / 100000) (1083743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2589919488 :
    ThetaLowerSegment 2589919488 2590050560 (258987968830143 / 100000)
      (259001207846847 / 100000) := by
  exact
    packedTile65536 2589919488 2590050560 14 6108 50891 31 _ _ (67734 / 3125) (2167491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590050560 :
    ThetaLowerSegment 2590050560 2590181632 (259001207846847 / 100000)
      (259014394874259 / 100000) := by
  exact
    packedTile65536 2590050560 2590181632 14 6084 50892 31 _ _ (2167493 / 100000) (270937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590181632 :
    ThetaLowerSegment 2590181632 2590312704 (259014394874259 / 100000)
      (51805545864391 / 20000) := by
  exact
    packedTile65536 2590181632 2590312704 14 6152 50893 31 _ _ (1083749 / 50000) (2167501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590312704 :
    ThetaLowerSegment 2590312704 2590443776 (51805545864391 / 20000)
      (259040795030039 / 100000) := by
  exact
    packedTile65536 2590312704 2590443776 14 6028 50895 31 _ _ (2167503 / 100000) (1083753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590443776 :
    ThetaLowerSegment 2590443776 2590574848 (259040795030039 / 100000) (10362159979551 / 4000) := by
  exact
    packedTile65536 2590443776 2590574848 14 6092 50896 31 _ _ (541877 / 25000) (2167511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590574848 :
    ThetaLowerSegment 2590574848 2590705920 (10362159979551 / 4000) (259067021906879 / 100000) := by
  exact
    packedTile65536 2590574848 2590705920 14 6008 50897 31 _ _ (2167513 / 100000) (541879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590705920 :
    ThetaLowerSegment 2590705920 2590836992 (259067021906879 / 100000)
      (51816032280199 / 20000) := by
  exact
    packedTile65536 2590705920 2590836992 14 6062 50898 31 _ _ (1083759 / 50000) (2167521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590836992 :
    ThetaLowerSegment 2590836992 2590968064 (51816032280199 / 20000) (51818667988167 / 20000) := by
  exact
    packedTile65536 2590836992 2590968064 14 6080 50900 31 _ _ (2167523 / 100000) (1083763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2590968064 :
    ThetaLowerSegment 2590968064 2591099136 (51818667988167 / 20000)
      (259106275747939 / 100000) := by
  exact
    packedTile65536 2590968064 2591099136 14 5968 50901 31 _ _ (270941 / 12500) (2167531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591099136 :
    ThetaLowerSegment 2591099136 2591230208 (259106275747939 / 100000)
      (259119389322589 / 100000) := by
  exact
    packedTile65536 2591099136 2591230208 14 6050 50902 31 _ _ (2167533 / 100000) (135471 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591230208 :
    ThetaLowerSegment 2591230208 2591361280 (259119389322589 / 100000)
      (259132587461471 / 100000) := by
  exact
    packedTile65536 2591230208 2591361280 14 6089 50904 31 _ _ (1083769 / 50000) (2167541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591361280 :
    ThetaLowerSegment 2591361280 2591492352 (259132587461471 / 100000) (10365834806599 / 4000) := by
  exact
    packedTile65536 2591361280 2591492352 14 6128 50905 31 _ _ (2167543 / 100000) (1083773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591492352 :
    ThetaLowerSegment 2591492352 2591623424 (10365834806599 / 4000) (259158977327731 / 100000) := by
  exact
    packedTile65536 2591492352 2591623424 14 6047 50906 31 _ _ (541887 / 25000) (2167551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591623424 :
    ThetaLowerSegment 2591623424 2591754496 (259158977327731 / 100000)
      (259172108369863 / 100000) := by
  exact
    packedTile65536 2591623424 2591754496 14 6058 50907 31 _ _ (1083777 / 50000) (2167557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591754496 :
    ThetaLowerSegment 2591754496 2591885568 (259172108369863 / 100000)
      (64796310402461 / 25000) := by
  exact
    packedTile65536 2591754496 2591885568 14 6059 50909 31 _ _ (2167559 / 100000) (1083781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2591885568 :
    ThetaLowerSegment 2591885568 2592016640 (64796310402461 / 25000) (8099947453858 / 3125) := by
  exact
    packedTile65536 2591885568 2592016640 14 6033 50910 31 _ _ (541891 / 25000) (2167567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592016640 :
    ThetaLowerSegment 2592016640 2592147712 (8099947453858 / 3125) (8100359291968 / 3125) := by
  exact
    packedTile65536 2592016640 2592147712 14 6080 50911 31 _ _ (2167569 / 100000) (541893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592147712 :
    ThetaLowerSegment 2592147712 2592278784 (8100359291968 / 3125) (64806124612957 / 25000) := by
  exact
    packedTile65536 2592147712 2592278784 14 5998 50913 31 _ _ (1083787 / 50000) (2167577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592278784 :
    ThetaLowerSegment 2592278784 2592409856 (64806124612957 / 25000) (25923758629383 / 10000) := by
  exact
    packedTile65536 2592278784 2592409856 14 6038 50914 31 _ _ (2167579 / 100000) (1083791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592409856 :
    ThetaLowerSegment 2592409856 2592540928 (25923758629383 / 10000) (129625385853651 / 50000) := by
  exact
    packedTile65536 2592409856 2592540928 14 6083 50915 31 _ _ (67737 / 3125) (2167587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592540928 :
    ThetaLowerSegment 2592540928 2592672000 (129625385853651 / 50000)
      (129631975324211 / 50000) := by
  exact
    packedTile65536 2592540928 2592672000 14 6080 50917 31 _ _ (2167589 / 100000) (270949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592672000 :
    ThetaLowerSegment 2592672000 2592803072 (129631975324211 / 50000)
      (129638441257113 / 50000) := by
  exact
    packedTile65536 2592672000 2592803072 14 5966 50918 31 _ _ (1083797 / 50000) (2167597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592803072 :
    ThetaLowerSegment 2592803072 2592934144 (129638441257113 / 50000) (25929009619773 / 10000) := by
  exact
    packedTile65536 2592803072 2592934144 14 6096 50919 31 _ _ (2167599 / 100000) (1083801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2592934144 :
    ThetaLowerSegment 2592934144 2593065216 (25929009619773 / 10000) (129651593179143 / 50000) := by
  exact
    packedTile65536 2592934144 2593065216 14 6039 50920 31 _ _ (541901 / 25000) (2167607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593065216 :
    ThetaLowerSegment 2593065216 2593196288 (129651593179143 / 50000)
      (129658148028759 / 50000) := by
  exact
    packedTile65536 2593065216 2593196288 14 6048 50922 31 _ _ (2167609 / 100000) (541903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593196288 :
    ThetaLowerSegment 2593196288 2593327360 (129658148028759 / 50000) (16208085558597 / 6250) := by
  exact
    packedTile65536 2593196288 2593327360 14 6031 50923 31 _ _ (1083807 / 50000) (2167617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593327360 :
    ThetaLowerSegment 2593327360 2593458432 (16208085558597 / 6250) (64835604500983 / 25000) := by
  exact
    packedTile65536 2593327360 2593458432 14 6020 50924 31 _ _ (2167619 / 100000) (1083811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593458432 :
    ThetaLowerSegment 2593458432 2593589504 (64835604500983 / 25000) (12967768152723 / 5000) := by
  exact
    packedTile65536 2593458432 2593589504 14 5972 50926 31 _ _ (270953 / 12500) (2167627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593589504 :
    ThetaLowerSegment 2593589504 2593720576 (12967768152723 / 5000) (10374742123077 / 4000) := by
  exact
    packedTile65536 2593589504 2593720576 14 6085 50927 31 _ _ (2167629 / 100000) (135477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593720576 :
    ThetaLowerSegment 2593720576 2593851648 (10374742123077 / 4000) (259381545875121 / 100000) := by
  exact
    packedTile65536 2593720576 2593851648 14 5994 50928 31 _ _ (1083817 / 50000) (2167637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593851648 :
    ThetaLowerSegment 2593851648 2593982720 (259381545875121 / 100000)
      (129697318123521 / 50000) := by
  exact
    packedTile65536 2593851648 2593982720 14 6039 50929 31 _ _ (2167639 / 100000) (1083821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2593982720 :
    ThetaLowerSegment 2593982720 2594113792 (129697318123521 / 50000) (8106491390236 / 3125) := by
  exact
    packedTile65536 2593982720 2594113792 14 6038 50931 31 _ _ (433529 / 20000) (67739 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594113792 :
    ThetaLowerSegment 2594113792 2594244864 (8106491390236 / 3125) (129710411798251 / 50000) := by
  exact
    packedTile65536 2594113792 2594244864 14 6043 50932 31 _ _ (43353 / 2000) (2167653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594244864 :
    ThetaLowerSegment 2594244864 2594375936 (129710411798251 / 50000)
      (259433922735667 / 100000) := by
  exact
    packedTile65536 2594244864 2594375936 14 6043 50933 31 _ _ (433531 / 20000) (1083829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594375936 :
    ThetaLowerSegment 2594375936 2594507008 (259433922735667 / 100000)
      (259447069593567 / 100000) := by
  exact
    packedTile65536 2594375936 2594507008 14 6065 50935 31 _ _ (108383 / 5000) (2167663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594507008 :
    ThetaLowerSegment 2594507008 2594638080 (259447069593567 / 100000)
      (64865043282123 / 25000) := by
  exact
    packedTile65536 2594507008 2594638080 14 6045 50936 31 _ _ (433533 / 20000) (541917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594638080 :
    ThetaLowerSegment 2594638080 2594769152 (64865043282123 / 25000) (129736679532551 / 50000) := by
  exact
    packedTile65536 2594638080 2594769152 14 6083 50937 31 _ _ (216767 / 10000) (2167673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594769152 :
    ThetaLowerSegment 2594769152 2594900224 (129736679532551 / 50000)
      (259486501678627 / 100000) := by
  exact
    packedTile65536 2594769152 2594900224 14 6063 50938 31 _ _ (86707 / 4000) (1083839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2594900224 :
    ThetaLowerSegment 2594900224 2595031296 (259486501678627 / 100000)
      (259499551112227 / 100000) := by
  exact
    packedTile65536 2594900224 2595031296 14 6020 50940 31 _ _ (13548 / 625) (2167683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595031296 :
    ThetaLowerSegment 2595031296 2595162368 (259499551112227 / 100000)
      (129756372905411 / 50000) := by
  exact
    packedTile65536 2595031296 2595162368 14 6087 50941 31 _ _ (433537 / 20000) (270961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595162368 :
    ThetaLowerSegment 2595162368 2595293440 (129756372905411 / 50000) (64881469961133 / 25000) := by
  exact
    packedTile65536 2595162368 2595293440 14 6059 50942 31 _ _ (216769 / 10000) (2167693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595293440 :
    ThetaLowerSegment 2595293440 2595424512 (64881469961133 / 25000)
      (259538883846837 / 100000) := by
  exact
    packedTile65536 2595293440 2595424512 14 5999 50944 31 _ _ (433539 / 20000) (1083849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595424512 :
    ThetaLowerSegment 2595424512 2595555584 (259538883846837 / 100000)
      (259552106816837 / 100000) := by
  exact
    packedTile65536 2595424512 2595555584 14 6100 50945 31 _ _ (21677 / 1000) (2167703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595555584 :
    ThetaLowerSegment 2595555584 2595686656 (259552106816837 / 100000)
      (32445646446859 / 12500) := by
  exact
    packedTile65536 2595555584 2595686656 14 6027 50946 31 _ _ (433541 / 20000) (541927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595686656 :
    ThetaLowerSegment 2595686656 2595817728 (32445646446859 / 12500) (64894593232193 / 25000) := by
  exact
    packedTile65536 2595686656 2595817728 14 6090 50947 31 _ _ (216771 / 10000) (2167713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595817728 :
    ThetaLowerSegment 2595817728 2595948800 (64894593232193 / 25000)
      (259591429076217 / 100000) := by
  exact
    packedTile65536 2595817728 2595948800 14 6023 50949 31 _ _ (433543 / 20000) (1083859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2595948800 :
    ThetaLowerSegment 2595948800 2596079872 (259591429076217 / 100000)
      (259604526440457 / 100000) := by
  exact
    packedTile65536 2595948800 2596079872 14 6042 50950 31 _ _ (54193 / 2500) (2167723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596079872 :
    ThetaLowerSegment 2596079872 2596210944 (259604526440457 / 100000)
      (64904417339283 / 25000) := by
  exact
    packedTile65536 2596079872 2596210944 14 6063 50951 31 _ _ (86709 / 4000) (135483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596210944 :
    ThetaLowerSegment 2596210944 2596342016 (64904417339283 / 25000) (32453844763859 / 12500) := by
  exact
    packedTile65536 2596210944 2596342016 14 6038 50953 31 _ _ (216773 / 10000) (2167733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596342016 :
    ThetaLowerSegment 2596342016 2596473088 (32453844763859 / 12500) (64910930291543 / 25000) := by
  exact
    packedTile65536 2596342016 2596473088 14 5980 50954 31 _ _ (433547 / 20000) (1083869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596473088 :
    ThetaLowerSegment 2596473088 2596604160 (64910930291543 / 25000) (32457108563659 / 12500) := by
  exact
    packedTile65536 2596473088 2596604160 14 6065 50955 31 _ _ (108387 / 5000) (2167743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596604160 :
    ThetaLowerSegment 2596604160 2596735232 (32457108563659 / 12500) (64917485004413 / 25000) := by
  exact
    packedTile65536 2596604160 2596735232 14 6030 50956 31 _ _ (1083873 / 50000) (2167749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596735232 :
    ThetaLowerSegment 2596735232 2596866304 (64917485004413 / 25000)
      (259683074420961 / 100000) := by
  exact
    packedTile65536 2596735232 2596866304 14 6059 50958 31 _ _ (2167751 / 100000) (1083877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596866304 :
    ThetaLowerSegment 2596866304 2596997376 (259683074420961 / 100000)
      (51939250441937 / 20000) := by
  exact
    packedTile65536 2596866304 2596997376 14 6079 50959 31 _ _ (541939 / 25000) (2167759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2596997376 :
    ThetaLowerSegment 2596997376 2597128448 (51939250441937 / 20000)
      (259709414854477 / 100000) := by
  exact
    packedTile65536 2596997376 2597128448 14 6072 50960 31 _ _ (2167761 / 100000) (541941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597128448 :
    ThetaLowerSegment 2597128448 2597259520 (259709414854477 / 100000)
      (259722603542821 / 100000) := by
  exact
    packedTile65536 2597128448 2597259520 14 6084 50962 31 _ _ (1083883 / 50000) (2167769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597259520 :
    ThetaLowerSegment 2597259520 2597390592 (259722603542821 / 100000) (6493386406427 / 2500) := by
  exact
    packedTile65536 2597259520 2597390592 14 5929 50963 31 _ _ (2167771 / 100000) (1083887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597390592 :
    ThetaLowerSegment 2597390592 2597521664 (6493386406427 / 2500) (6493710759911 / 2500) := by
  exact
    packedTile65536 2597390592 2597521664 14 5985 50964 31 _ _ (67743 / 3125) (2167779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597521664 :
    ThetaLowerSegment 2597521664 2597652736 (6493710759911 / 2500) (32470205648677 / 12500) := by
  exact
    packedTile65536 2597521664 2597652736 14 6096 50965 31 _ _ (2167781 / 100000) (270973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597652736 :
    ThetaLowerSegment 2597652736 2597783808 (32470205648677 / 12500) (32471879179469 / 12500) := by
  exact
    packedTile65536 2597652736 2597783808 14 6176 50967 31 _ _ (1083893 / 50000) (2167789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597783808 :
    ThetaLowerSegment 2597783808 2597914880 (32471879179469 / 12500)
      (259787972980231 / 100000) := by
  exact
    packedTile65536 2597783808 2597914880 14 5969 50968 31 _ _ (2167791 / 100000) (1083897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2597914880 :
    ThetaLowerSegment 2597914880 2598045952 (259787972980231 / 100000)
      (51960217195647 / 20000) := by
  exact
    packedTile65536 2597914880 2598045952 14 6049 50969 31 _ _ (541949 / 25000) (2167799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598045952 :
    ThetaLowerSegment 2598045952 2598177024 (51960217195647 / 20000)
      (259814175160673 / 100000) := by
  exact
    packedTile65536 2598045952 2598177024 14 6038 50971 31 _ _ (2167801 / 100000) (541951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598177024 :
    ThetaLowerSegment 2598177024 2598308096 (259814175160673 / 100000)
      (51965428595233 / 20000) := by
  exact
    packedTile65536 2598177024 2598308096 14 5982 50972 31 _ _ (1083903 / 50000) (2167809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598308096 :
    ThetaLowerSegment 2598308096 2598439168 (51965428595233 / 20000)
      (259840418650729 / 100000) := by
  exact
    packedTile65536 2598308096 2598439168 14 6124 50973 31 _ _ (2167811 / 100000) (1083907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598439168 :
    ThetaLowerSegment 2598439168 2598570240 (259840418650729 / 100000)
      (259853447224889 / 100000) := by
  exact
    packedTile65536 2598439168 2598570240 14 6010 50974 31 _ _ (270977 / 12500) (2167819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598570240 :
    ThetaLowerSegment 2598570240 2598701312 (259853447224889 / 100000)
      (129933319207837 / 50000) := by
  exact
    packedTile65536 2598570240 2598701312 14 6085 50976 31 _ _ (2167821 / 100000) (135489 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598701312 :
    ThetaLowerSegment 2598701312 2598832384 (129933319207837 / 50000) (32484959736133 / 12500) := by
  exact
    packedTile65536 2598701312 2598832384 14 6015 50977 31 _ _ (1083913 / 50000) (2167829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598832384 :
    ThetaLowerSegment 2598832384 2598963456 (32484959736133 / 12500) (129946418311617 / 50000) := by
  exact
    packedTile65536 2598832384 2598963456 14 6070 50978 31 _ _ (2167831 / 100000) (1083917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2598963456 :
    ThetaLowerSegment 2598963456 2599094528 (129946418311617 / 50000)
      (129953086575153 / 50000) := by
  exact
    packedTile65536 2598963456 2599094528 14 6152 50980 31 _ _ (541959 / 25000) (2167839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599094528 :
    ThetaLowerSegment 2599094528 2599225600 (129953086575153 / 50000)
      (259919212713921 / 100000) := by
  exact
    packedTile65536 2599094528 2599225600 14 6015 50981 31 _ _ (2167841 / 100000) (541961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599225600 :
    ThetaLowerSegment 2599225600 2599356672 (259919212713921 / 100000) (10397288704883 / 4000) := by
  exact
    packedTile65536 2599225600 2599356672 14 5999 50982 31 _ _ (1083923 / 50000) (2167849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599356672 :
    ThetaLowerSegment 2599356672 2599487744 (10397288704883 / 4000) (6498633598997 / 2500) := by
  exact
    packedTile65536 2599356672 2599487744 14 6055 50983 31 _ _ (2167851 / 100000) (1083927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599487744 :
    ThetaLowerSegment 2599487744 2599618816 (6498633598997 / 2500) (51991724416801 / 20000) := by
  exact
    packedTile65536 2599487744 2599618816 14 6125 50985 31 _ _ (2167857 / 100000) (108393 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599618816 :
    ThetaLowerSegment 2599618816 2599749888 (51991724416801 / 20000) (51994317179753 / 20000) := by
  exact
    packedTile65536 2599618816 2599749888 14 5980 50986 31 _ _ (1083931 / 50000) (433573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599749888 :
    ThetaLowerSegment 2599749888 2599880960 (51994317179753 / 20000) (12999238868473 / 5000) := by
  exact
    packedTile65536 2599749888 2599880960 14 6085 50987 31 _ _ (2167867 / 100000) (216787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2599880960 :
    ThetaLowerSegment 2599880960 2600012032 (12999238868473 / 5000) (64999454821853 / 25000) := by
  exact
    packedTile65536 2599880960 2600012032 14 6016 50989 31 _ _ (67746 / 3125) (17343 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600012032 :
    ThetaLowerSegment 2600012032 2600143104 (64999454821853 / 25000) (16250684788877 / 6250) := by
  exact
    packedTile65536 2600012032 2600143104 14 6060 50990 31 _ _ (2167877 / 100000) (54197 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600143104 :
    ThetaLowerSegment 2600143104 2600274176 (16250684788877 / 6250) (13001201881101 / 5000) := by
  exact
    packedTile65536 2600143104 2600274176 14 6034 50991 31 _ _ (1083941 / 50000) (433577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600274176 :
    ThetaLowerSegment 2600274176 2600405248 (13001201881101 / 5000) (52007450178657 / 20000) := by
  exact
    packedTile65536 2600274176 2600405248 14 6095 50992 31 _ _ (2167887 / 100000) (216789 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600405248 :
    ThetaLowerSegment 2600405248 2600536320 (52007450178657 / 20000)
      (260050362304101 / 100000) := by
  exact
    packedTile65536 2600405248 2600536320 14 6048 50994 31 _ _ (541973 / 25000) (433579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600536320 :
    ThetaLowerSegment 2600536320 2600667392 (260050362304101 / 100000)
      (260063538782067 / 100000) := by
  exact
    packedTile65536 2600536320 2600667392 14 6078 50995 31 _ _ (2167897 / 100000) (21679 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600667392 :
    ThetaLowerSegment 2600667392 2600798464 (260063538782067 / 100000)
      (260076487660713 / 100000) := by
  exact
    packedTile65536 2600667392 2600798464 14 5973 50996 31 _ _ (1083951 / 50000) (433581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600798464 :
    ThetaLowerSegment 2600798464 2600929536 (260076487660713 / 100000)
      (260089555804109 / 100000) := by
  exact
    packedTile65536 2600798464 2600929536 14 6028 50998 31 _ _ (2167907 / 100000) (216791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2600929536 :
    ThetaLowerSegment 2600929536 2601060608 (260089555804109 / 100000)
      (260102660832149 / 100000) := by
  exact
    packedTile65536 2600929536 2601060608 14 6045 50999 31 _ _ (270989 / 12500) (433583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601060608 :
    ThetaLowerSegment 2601060608 2601191680 (260102660832149 / 100000)
      (26011569651707 / 10000) := by
  exact
    packedTile65536 2601060608 2601191680 14 6013 51000 31 _ _ (2167917 / 100000) (27099 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601191680 :
    ThetaLowerSegment 2601191680 2601322752 (26011569651707 / 10000) (130064304330251 / 50000) := by
  exact
    packedTile65536 2601191680 2601322752 14 5956 51001 31 _ _ (1083961 / 50000) (86717 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601322752 :
    ThetaLowerSegment 2601322752 2601339136 (130064304330251 / 50000) (32516279325719 / 12500) := by
  exact
    packedTile65536 2601322752 2601339136 11 750 51003 31 _ _ (2167927 / 100000) (216793 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2601339136 :
    ThetaLowerSegment 2601339136 2601341184 (32516279325719 / 12500) (325163039859 / 125) := by
  exact
    packedTile65536 2601339136 2601341184 8 91 51003 31 _ _ (270991 / 12500) (2167931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2569341184_2601341184 :
    ThetaLowerSegment 2569341184 2601341184 (128464904250273 / 50000) (325163039859 / 125) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2569341184 cell2569472256)
                  (ThetaLowerSegment.join cell2569603328 cell2569734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2569865472 cell2569996544)
                  (ThetaLowerSegment.join cell2570127616 cell2570258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2570389760 cell2570520832)
                  (ThetaLowerSegment.join cell2570651904 cell2570782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2570914048 cell2571045120)
                  (ThetaLowerSegment.join cell2571176192 cell2571307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2571438336 cell2571569408)
                  (ThetaLowerSegment.join cell2571700480 cell2571831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2571962624 cell2572093696)
                  (ThetaLowerSegment.join cell2572224768 cell2572355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2572486912 cell2572617984)
                  (ThetaLowerSegment.join cell2572749056 cell2572880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2573011200 cell2573142272)
                  (ThetaLowerSegment.join cell2573273344 cell2573404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2573535488 cell2573666560)
                  (ThetaLowerSegment.join cell2573797632 cell2573928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2574059776 cell2574190848)
                  (ThetaLowerSegment.join cell2574321920 cell2574452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2574584064 cell2574715136)
                  (ThetaLowerSegment.join cell2574846208 cell2574977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2575108352 cell2575239424)
                  (ThetaLowerSegment.join cell2575370496 cell2575501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2575632640 cell2575763712)
                  (ThetaLowerSegment.join cell2575894784 cell2576025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2576156928 cell2576288000)
                  (ThetaLowerSegment.join cell2576419072 cell2576550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2576681216 cell2576812288)
                  (ThetaLowerSegment.join cell2576943360 cell2577074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2577205504 cell2577336576)
                  (ThetaLowerSegment.join cell2577467648 cell2577598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2577729792 cell2577860864)
                  (ThetaLowerSegment.join cell2577991936 cell2578123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2578254080 cell2578385152)
                  (ThetaLowerSegment.join cell2578516224 cell2578647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2578778368 cell2578909440)
                  (ThetaLowerSegment.join cell2579040512 cell2579171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2579302656 cell2579433728)
                  (ThetaLowerSegment.join cell2579564800 cell2579695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2579826944 cell2579958016)
                  (ThetaLowerSegment.join cell2580089088 cell2580220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2580351232 cell2580482304)
                  (ThetaLowerSegment.join cell2580613376 cell2580744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2580875520 cell2581006592)
                  (ThetaLowerSegment.join cell2581137664 cell2581268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2581399808 cell2581530880)
                  (ThetaLowerSegment.join cell2581661952 cell2581793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2581924096 cell2582055168)
                  (ThetaLowerSegment.join cell2582186240 cell2582317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2582448384 cell2582579456)
                  (ThetaLowerSegment.join cell2582710528 cell2582841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2582972672 cell2583103744)
                  (ThetaLowerSegment.join cell2583234816 cell2583365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2583496960 cell2583628032)
                  (ThetaLowerSegment.join cell2583759104 cell2583890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2584021248 cell2584152320)
                  (ThetaLowerSegment.join cell2584283392 cell2584414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2584545536 cell2584676608)
                  (ThetaLowerSegment.join cell2584807680 cell2584938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2585069824 cell2585200896)
                  (ThetaLowerSegment.join cell2585331968 cell2585463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2585594112 cell2585725184)
                  (ThetaLowerSegment.join cell2585856256 cell2585987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2586118400 cell2586249472)
                  (ThetaLowerSegment.join cell2586380544 cell2586511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2586642688 cell2586773760)
                  (ThetaLowerSegment.join cell2586904832 cell2587035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2587166976 cell2587298048)
                  (ThetaLowerSegment.join cell2587429120 cell2587560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2587691264 cell2587822336)
                  (ThetaLowerSegment.join cell2587953408 cell2588084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2588215552 cell2588346624)
                  (ThetaLowerSegment.join cell2588477696 cell2588608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2588739840 cell2588870912)
                  (ThetaLowerSegment.join cell2589001984 cell2589133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2589264128 cell2589395200)
                  (ThetaLowerSegment.join cell2589526272 cell2589657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2589788416 cell2589919488)
                  (ThetaLowerSegment.join cell2590050560 cell2590181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2590312704 cell2590443776)
                  (ThetaLowerSegment.join cell2590574848 cell2590705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2590836992 cell2590968064)
                  (ThetaLowerSegment.join cell2591099136 cell2591230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2591361280 cell2591492352)
                  (ThetaLowerSegment.join cell2591623424 cell2591754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2591885568 cell2592016640)
                  (ThetaLowerSegment.join cell2592147712 cell2592278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2592409856 cell2592540928)
                  (ThetaLowerSegment.join cell2592672000 cell2592803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2592934144 cell2593065216)
                  (ThetaLowerSegment.join cell2593196288 cell2593327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2593458432 cell2593589504)
                  (ThetaLowerSegment.join cell2593720576 cell2593851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2593982720 cell2594113792)
                  (ThetaLowerSegment.join cell2594244864 cell2594375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2594507008 cell2594638080)
                  (ThetaLowerSegment.join cell2594769152 cell2594900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2595031296 cell2595162368)
                  (ThetaLowerSegment.join cell2595293440 cell2595424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2595555584 cell2595686656)
                  (ThetaLowerSegment.join cell2595817728 cell2595948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2596079872 cell2596210944)
                  (ThetaLowerSegment.join cell2596342016 cell2596473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2596604160 cell2596735232)
                  (ThetaLowerSegment.join cell2596866304 cell2596997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2597128448 cell2597259520)
                  (ThetaLowerSegment.join cell2597390592 cell2597521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2597652736 cell2597783808)
                  (ThetaLowerSegment.join cell2597914880 cell2598045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2598177024 cell2598308096)
                  (ThetaLowerSegment.join cell2598439168 cell2598570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2598701312 cell2598832384)
                  (ThetaLowerSegment.join cell2598963456 cell2599094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2599225600 cell2599356672)
                  (ThetaLowerSegment.join cell2599487744 cell2599618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2599749888 cell2599880960)
                  (ThetaLowerSegment.join cell2600012032 cell2600143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2600274176 cell2600405248)
                  (ThetaLowerSegment.join cell2600536320 cell2600667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2600798464 cell2600929536)
                (ThetaLowerSegment.join cell2601060608 cell2601191680))
              (ThetaLowerSegment.join cell2601322752 cell2601339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
