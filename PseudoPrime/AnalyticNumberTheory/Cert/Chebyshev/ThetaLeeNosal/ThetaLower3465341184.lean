/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3465341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3433341184 :
    ThetaLowerSegment 3433341184 3433472256 (343324875317073 / 100000)
      (343338029623971 / 100000) := by
  exact
    packedTile65536 3433341184 3433472256 14 5991 58594 32 _ _ (1097839 / 50000) (2195681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433472256 :
    ThetaLowerSegment 3433472256 3433603328 (343338029623971 / 100000)
      (343351214694381 / 100000) := by
  exact
    packedTile65536 3433472256 3433603328 14 6005 58595 32 _ _ (1097841 / 50000) (439137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433603328 :
    ThetaLowerSegment 3433603328 3433734400 (343351214694381 / 100000)
      (343364257069221 / 100000) := by
  exact
    packedTile65536 3433603328 3433734400 14 5940 58596 32 _ _ (1097843 / 50000) (2195689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433734400 :
    ThetaLowerSegment 3433734400 3433865472 (343364257069221 / 100000)
      (343377358751451 / 100000) := by
  exact
    packedTile65536 3433734400 3433865472 14 5967 58598 32 _ _ (219569 / 10000) (2195693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433865472 :
    ThetaLowerSegment 3433865472 3433996544 (343377358751451 / 100000)
      (343390460457549 / 100000) := by
  exact
    packedTile65536 3433865472 3433996544 14 5967 58599 32 _ _ (1097847 / 50000) (2195697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3433996544 :
    ThetaLowerSegment 3433996544 3434127616 (343390460457549 / 100000)
      (343403412880051 / 100000) := by
  exact
    packedTile65536 3433996544 3434127616 14 5899 58600 32 _ _ (1097849 / 50000) (2195701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434127616 :
    ThetaLowerSegment 3434127616 3434258688 (343403412880051 / 100000)
      (343416512432217 / 100000) := by
  exact
    packedTile65536 3434127616 3434258688 14 5966 58601 32 _ _ (2195701 / 100000) (274463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434258688 :
    ThetaLowerSegment 3434258688 3434389760 (343416512432217 / 100000)
      (343429682270807 / 100000) := by
  exact
    packedTile65536 3434258688 3434389760 14 5998 58602 32 _ _ (439141 / 20000) (548927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434389760 :
    ThetaLowerSegment 3434389760 3434520832 (343429682270807 / 100000)
      (68688515094811 / 20000) := by
  exact
    packedTile65536 3434389760 3434520832 14 5872 58603 32 _ _ (2195709 / 100000) (68616 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434520832 :
    ThetaLowerSegment 3434520832 3434651904 (68688515094811 / 20000)
      (343455679489239 / 100000) := by
  exact
    packedTile65536 3434520832 3434651904 14 5968 58604 32 _ _ (2195713 / 100000) (548929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434651904 :
    ThetaLowerSegment 3434651904 3434782976 (343455679489239 / 100000) (3434689262499 / 1000) := by
  exact
    packedTile65536 3434651904 3434782976 14 6033 58605 32 _ _ (2195717 / 100000) (54893 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434782976 :
    ThetaLowerSegment 3434782976 3434914048 (3434689262499 / 1000) (17174099100051 / 5000) := by
  exact
    packedTile65536 3434782976 3434914048 14 5946 58607 32 _ _ (54893 / 2500) (2195723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3434914048 :
    ThetaLowerSegment 3434914048 3435045120 (17174099100051 / 5000) (42936886034697 / 12500) := by
  exact
    packedTile65536 3434914048 3435045120 14 5969 58608 32 _ _ (548931 / 25000) (2195727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435045120 :
    ThetaLowerSegment 3435045120 3435176192 (42936886034697 / 12500) (42938512245747 / 12500) := by
  exact
    packedTile65536 3435045120 3435176192 14 5925 58609 32 _ _ (137233 / 6250) (2195731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435176192 :
    ThetaLowerSegment 3435176192 3435307264 (42938512245747 / 12500) (42940166729809 / 12500) := by
  exact
    packedTile65536 3435176192 3435307264 14 6028 58610 32 _ _ (548933 / 25000) (439147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435307264 :
    ThetaLowerSegment 3435307264 3435438336 (42940166729809 / 12500) (21470900041463 / 6250) := by
  exact
    packedTile65536 3435307264 3435438336 14 5951 58611 32 _ _ (274467 / 12500) (2195739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435438336 :
    ThetaLowerSegment 3435438336 3435569408 (21470900041463 / 6250) (85886872367387 / 25000) := by
  exact
    packedTile65536 3435438336 3435569408 14 5961 58612 32 _ _ (109787 / 5000) (2195743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435569408 :
    ThetaLowerSegment 3435569408 3435700480 (85886872367387 / 25000)
      (343560613425459 / 100000) := by
  exact
    packedTile65536 3435569408 3435700480 14 5977 58613 32 _ _ (2195743 / 100000) (1097873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435700480 :
    ThetaLowerSegment 3435700480 3435831552 (343560613425459 / 100000)
      (343573735209531 / 100000) := by
  exact
    packedTile65536 3435700480 3435831552 14 5976 58614 32 _ _ (2195747 / 100000) (8783 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435831552 :
    ThetaLowerSegment 3435831552 3435962624 (343573735209531 / 100000)
      (343586839451499 / 100000) := by
  exact
    packedTile65536 3435831552 3435962624 14 5968 58615 32 _ _ (2195751 / 100000) (1097877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3435962624 :
    ThetaLowerSegment 3435962624 3436093696 (343586839451499 / 100000)
      (171800003697117 / 50000) := by
  exact
    packedTile65536 3435962624 3436093696 14 5997 58617 32 _ _ (439151 / 20000) (1097879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436093696 :
    ThetaLowerSegment 3436093696 3436224768 (171800003697117 / 50000)
      (343613175360957 / 100000) := by
  exact
    packedTile65536 3436093696 3436224768 14 5997 58618 32 _ _ (2195759 / 100000) (1097881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436224768 :
    ThetaLowerSegment 3436224768 3436355840 (343613175360957 / 100000)
      (343626189642331 / 100000) := by
  exact
    packedTile65536 3436224768 3436355840 14 5927 58619 32 _ _ (1097881 / 50000) (439153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436355840 :
    ThetaLowerSegment 3436355840 3436486912 (343626189642331 / 100000)
      (68727837276257 / 20000) := by
  exact
    packedTile65536 3436355840 3436486912 14 5919 58620 32 _ _ (1097883 / 50000) (2195769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436486912 :
    ThetaLowerSegment 3436486912 3436617984 (68727837276257 / 20000) (13746092419943 / 4000) := by
  exact
    packedTile65536 3436486912 3436617984 14 5977 58621 32 _ _ (219577 / 10000) (2195773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436617984 :
    ThetaLowerSegment 3436617984 3436749056 (13746092419943 / 4000) (68733094832741 / 20000) := by
  exact
    packedTile65536 3436617984 3436749056 14 5995 58622 32 _ _ (1097887 / 50000) (2195777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436749056 :
    ThetaLowerSegment 3436749056 3436880128 (68733094832741 / 20000)
      (343678543434361 / 100000) := by
  exact
    packedTile65536 3436749056 3436880128 14 5952 58623 32 _ _ (1097889 / 50000) (2195781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3436880128 :
    ThetaLowerSegment 3436880128 3437011200 (343678543434361 / 100000)
      (68738323422887 / 20000) := by
  exact
    packedTile65536 3436880128 3437011200 14 5954 58624 32 _ _ (2195781 / 100000) (274473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437011200 :
    ThetaLowerSegment 3437011200 3437142272 (68738323422887 / 20000) (3437045480923 / 1000) := by
  exact
    packedTile65536 3437011200 3437142272 14 5889 58626 32 _ _ (439157 / 20000) (548947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437142272 :
    ThetaLowerSegment 3437142272 3437273344 (3437045480923 / 1000) (42964701080659 / 12500) := by
  exact
    packedTile65536 3437142272 3437273344 14 5948 58627 32 _ _ (2195789 / 100000) (137237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437273344 :
    ThetaLowerSegment 3437273344 3437404416 (42964701080659 / 12500) (171865472945977 / 50000) := by
  exact
    packedTile65536 3437273344 3437404416 14 6074 58628 32 _ _ (2195793 / 100000) (548949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437404416 :
    ThetaLowerSegment 3437404416 3437535488 (171865472945977 / 50000) (8593602907059 / 2500) := by
  exact
    packedTile65536 3437404416 3437535488 14 5998 58629 32 _ _ (2195797 / 100000) (10979 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437535488 :
    ThetaLowerSegment 3437535488 3437666560 (8593602907059 / 2500) (343757100053673 / 100000) := by
  exact
    packedTile65536 3437535488 3437666560 14 5913 58630 32 _ _ (2195801 / 100000) (548951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437666560 :
    ThetaLowerSegment 3437666560 3437797632 (343757100053673 / 100000)
      (343770252919633 / 100000) := by
  exact
    packedTile65536 3437666560 3437797632 14 5990 58631 32 _ _ (548951 / 25000) (2195807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437797632 :
    ThetaLowerSegment 3437797632 3437928704 (343770252919633 / 100000)
      (343783594649041 / 100000) := by
  exact
    packedTile65536 3437797632 3437928704 14 6076 58632 32 _ _ (68619 / 3125) (2195811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3437928704 :
    ThetaLowerSegment 3437928704 3438059776 (343783594649041 / 100000)
      (343796591660269 / 100000) := by
  exact
    packedTile65536 3437928704 3438059776 14 5919 58633 32 _ _ (548953 / 25000) (439163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438059776 :
    ThetaLowerSegment 3438059776 3438190848 (343796591660269 / 100000)
      (343809773143717 / 100000) := by
  exact
    packedTile65536 3438059776 3438190848 14 6003 58634 32 _ _ (274477 / 12500) (2195819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438190848 :
    ThetaLowerSegment 3438190848 3438321920 (343809773143717 / 100000)
      (343822866818377 / 100000) := by
  exact
    packedTile65536 3438190848 3438321920 14 5963 58636 32 _ _ (109791 / 5000) (2195823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438321920 :
    ThetaLowerSegment 3438321920 3438452992 (343822866818377 / 100000)
      (343835874873829 / 100000) := by
  exact
    packedTile65536 3438321920 3438452992 14 5924 58637 32 _ _ (2195823 / 100000) (1097913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438452992 :
    ThetaLowerSegment 3438452992 3438584064 (343835874873829 / 100000)
      (85962252028779 / 25000) := by
  exact
    packedTile65536 3438452992 3438584064 14 5981 58638 32 _ _ (2195827 / 100000) (219583 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438584064 :
    ThetaLowerSegment 3438584064 3438715136 (85962252028779 / 25000)
      (343862194080271 / 100000) := by
  exact
    packedTile65536 3438584064 3438715136 14 6005 58639 32 _ _ (2195831 / 100000) (1097917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438715136 :
    ThetaLowerSegment 3438715136 3438846208 (343862194080271 / 100000)
      (85968802198579 / 25000) := by
  exact
    packedTile65536 3438715136 3438846208 14 5927 58640 32 _ _ (439167 / 20000) (1097919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438846208 :
    ThetaLowerSegment 3438846208 3438977280 (85968802198579 / 25000) (68777677204831 / 20000) := by
  exact
    packedTile65536 3438846208 3438977280 14 6001 58641 32 _ _ (2195839 / 100000) (1097921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3438977280 :
    ThetaLowerSegment 3438977280 3439108352 (68777677204831 / 20000)
      (343901556684471 / 100000) := by
  exact
    packedTile65536 3438977280 3439108352 14 5998 58642 32 _ _ (1097921 / 50000) (439169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439108352 :
    ThetaLowerSegment 3439108352 3439239424 (343901556684471 / 100000)
      (343914615380633 / 100000) := by
  exact
    packedTile65536 3439108352 3439239424 14 5947 58643 32 _ _ (1097923 / 50000) (2195849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439239424 :
    ThetaLowerSegment 3439239424 3439370496 (343914615380633 / 100000)
      (343927520391083 / 100000) := by
  exact
    packedTile65536 3439239424 3439370496 14 5877 58645 32 _ _ (43917 / 2000) (2195853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439370496 :
    ThetaLowerSegment 3439370496 3439501568 (343927520391083 / 100000)
      (343940796524367 / 100000) := by
  exact
    packedTile65536 3439370496 3439501568 14 6046 58646 32 _ _ (1097927 / 50000) (2195857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439501568 :
    ThetaLowerSegment 3439501568 3439632640 (343940796524367 / 100000)
      (343953932146923 / 100000) := by
  exact
    packedTile65536 3439501568 3439632640 14 5982 58647 32 _ _ (1097929 / 50000) (2195861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439632640 :
    ThetaLowerSegment 3439632640 3439763712 (343953932146923 / 100000)
      (343967111710647 / 100000) := by
  exact
    packedTile65536 3439632640 3439763712 14 6002 58648 32 _ _ (1097931 / 50000) (439173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439763712 :
    ThetaLowerSegment 3439763712 3439894784 (343967111710647 / 100000)
      (343980185890857 / 100000) := by
  exact
    packedTile65536 3439763712 3439894784 14 5954 58649 32 _ _ (439173 / 20000) (548967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3439894784 :
    ThetaLowerSegment 3439894784 3440025856 (343980185890857 / 100000)
      (343993317187477 / 100000) := by
  exact
    packedTile65536 3439894784 3440025856 14 5980 58650 32 _ _ (2195869 / 100000) (68621 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440025856 :
    ThetaLowerSegment 3440025856 3440156928 (343993317187477 / 100000)
      (172003229743691 / 50000) := by
  exact
    packedTile65536 3440025856 3440156928 14 5985 58651 32 _ _ (2195873 / 100000) (548969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440156928 :
    ThetaLowerSegment 3440156928 3440288000 (172003229743691 / 50000)
      (344019672079291 / 100000) := by
  exact
    packedTile65536 3440156928 3440288000 14 6017 58652 32 _ _ (2195877 / 100000) (54897 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440288000 :
    ThetaLowerSegment 3440288000 3440419072 (344019672079291 / 100000) (13761301949019 / 4000) := by
  exact
    packedTile65536 3440288000 3440419072 14 5864 58653 32 _ _ (2195881 / 100000) (548971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440419072 :
    ThetaLowerSegment 3440419072 3440550144 (13761301949019 / 4000) (344045816256603 / 100000) := by
  exact
    packedTile65536 3440419072 3440550144 14 6042 58655 32 _ _ (548971 / 25000) (2195887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440550144 :
    ThetaLowerSegment 3440550144 3440681216 (344045816256603 / 100000)
      (344058750036923 / 100000) := by
  exact
    packedTile65536 3440550144 3440681216 14 5890 58656 32 _ _ (137243 / 6250) (2195891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440681216 :
    ThetaLowerSegment 3440681216 3440812288 (344058750036923 / 100000)
      (344071980286223 / 100000) := by
  exact
    packedTile65536 3440681216 3440812288 14 6025 58657 32 _ _ (548973 / 25000) (439179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440812288 :
    ThetaLowerSegment 3440812288 3440943360 (344071980286223 / 100000)
      (344085133703263 / 100000) := by
  exact
    packedTile65536 3440812288 3440943360 14 5990 58658 32 _ _ (274487 / 12500) (2195899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3440943360 :
    ThetaLowerSegment 3440943360 3441074432 (344085133703263 / 100000)
      (344098065358363 / 100000) := by
  exact
    packedTile65536 3440943360 3441074432 14 5889 58659 32 _ _ (21959 / 1000) (2195903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441074432 :
    ThetaLowerSegment 3441074432 3441205504 (344098065358363 / 100000)
      (43013905920509 / 12500) := by
  exact
    packedTile65536 3441074432 3441205504 14 6003 58660 32 _ _ (2195903 / 100000) (1097953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441205504 :
    ThetaLowerSegment 3441205504 3441336576 (43013905920509 / 12500)
      (344124183452209 / 100000) := by
  exact
    packedTile65536 3441205504 3441336576 14 5891 58661 32 _ _ (2195907 / 100000) (219591 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441336576 :
    ThetaLowerSegment 3441336576 3441467648 (344124183452209 / 100000)
      (172068586132887 / 50000) := by
  exact
    packedTile65536 3441336576 3441467648 14 5915 58662 32 _ _ (2195911 / 100000) (1097957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441467648 :
    ThetaLowerSegment 3441467648 3441598720 (172068586132887 / 50000)
      (172075191445207 / 50000) := by
  exact
    packedTile65536 3441467648 3441598720 14 6016 58664 32 _ _ (439183 / 20000) (1097959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441598720 :
    ThetaLowerSegment 3441598720 3441729792 (172075191445207 / 50000)
      (172081735283827 / 50000) := by
  exact
    packedTile65536 3441598720 3441729792 14 5960 58665 32 _ _ (2195919 / 100000) (1097961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441729792 :
    ThetaLowerSegment 3441729792 3441860864 (172081735283827 / 50000)
      (344176591207579 / 100000) := by
  exact
    packedTile65536 3441729792 3441860864 14 5975 58666 32 _ _ (2195923 / 100000) (1097963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441860864 :
    ThetaLowerSegment 3441860864 3441991936 (344176591207579 / 100000)
      (344189569130239 / 100000) := by
  exact
    packedTile65536 3441860864 3441991936 14 5910 58667 32 _ _ (1097963 / 50000) (2195929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3441991936 :
    ThetaLowerSegment 3441991936 3442123008 (344189569130239 / 100000)
      (344202735926519 / 100000) := by
  exact
    packedTile65536 3441991936 3442123008 14 5996 58668 32 _ _ (219593 / 10000) (2195933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442123008 :
    ThetaLowerSegment 3442123008 3442254080 (344202735926519 / 100000)
      (344215775382611 / 100000) := by
  exact
    packedTile65536 3442123008 3442254080 14 5938 58669 32 _ _ (1097967 / 50000) (2195937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442254080 :
    ThetaLowerSegment 3442254080 3442385152 (344215775382611 / 100000)
      (344228882936533 / 100000) := by
  exact
    packedTile65536 3442254080 3442385152 14 5969 58670 32 _ _ (1097969 / 50000) (2195941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442385152 :
    ThetaLowerSegment 3442385152 3442516224 (344228882936533 / 100000)
      (344242240851719 / 100000) := by
  exact
    packedTile65536 3442385152 3442516224 14 6083 58671 32 _ _ (1097971 / 50000) (439189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442516224 :
    ThetaLowerSegment 3442516224 3442647296 (344242240851719 / 100000)
      (172127720338557 / 50000) := by
  exact
    packedTile65536 3442516224 3442647296 14 6011 58672 32 _ _ (439189 / 20000) (548987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442647296 :
    ThetaLowerSegment 3442647296 3442778368 (172127720338557 / 50000)
      (344268675661737 / 100000) := by
  exact
    packedTile65536 3442647296 3442778368 14 6027 58674 32 _ _ (2195949 / 100000) (137247 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442778368 :
    ThetaLowerSegment 3442778368 3442909440 (344268675661737 / 100000)
      (344281899690703 / 100000) := by
  exact
    packedTile65536 3442778368 3442909440 14 6022 58675 32 _ _ (2195953 / 100000) (548989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3442909440 :
    ThetaLowerSegment 3442909440 3443040512 (344281899690703 / 100000)
      (172147435604351 / 50000) := by
  exact
    packedTile65536 3442909440 3443040512 14 5907 58676 32 _ _ (2195957 / 100000) (54899 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443040512 :
    ThetaLowerSegment 3443040512 3443171584 (172147435604351 / 50000)
      (344308005251443 / 100000) := by
  exact
    packedTile65536 3443040512 3443171584 14 5981 58677 32 _ _ (2195961 / 100000) (548991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443171584 :
    ThetaLowerSegment 3443171584 3443302656 (344308005251443 / 100000)
      (344321273265931 / 100000) := by
  exact
    packedTile65536 3443171584 3443302656 14 6042 58678 32 _ _ (548991 / 25000) (2195967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443302656 :
    ThetaLowerSegment 3443302656 3443433728 (344321273265931 / 100000)
      (344334396370699 / 100000) := by
  exact
    packedTile65536 3443302656 3443433728 14 5976 58679 32 _ _ (68624 / 3125) (2195971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443433728 :
    ThetaLowerSegment 3443433728 3443564800 (344334396370699 / 100000)
      (344347363585359 / 100000) := by
  exact
    packedTile65536 3443433728 3443564800 14 5905 58680 32 _ _ (548993 / 25000) (87839 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443564800 :
    ThetaLowerSegment 3443564800 3443695872 (344347363585359 / 100000)
      (68872088563683 / 20000) := by
  exact
    packedTile65536 3443564800 3443695872 14 5956 58681 32 _ _ (274497 / 12500) (2195979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443695872 :
    ThetaLowerSegment 3443695872 3443826944 (68872088563683 / 20000) (68874689921591 / 20000) := by
  exact
    packedTile65536 3443695872 3443826944 14 5923 58683 32 _ _ (109799 / 5000) (2195983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443826944 :
    ThetaLowerSegment 3443826944 3443958016 (68874689921591 / 20000)
      (344386484963043 / 100000) := by
  exact
    packedTile65536 3443826944 3443958016 14 5936 58684 32 _ _ (2195983 / 100000) (1097993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3443958016 :
    ThetaLowerSegment 3443958016 3444089088 (344386484963043 / 100000)
      (43049959532119 / 12500) := by
  exact
    packedTile65536 3443958016 3444089088 14 6007 58685 32 _ _ (2195987 / 100000) (219599 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444089088 :
    ThetaLowerSegment 3444089088 3444220160 (43049959532119 / 12500)
      (344412911494709 / 100000) := by
  exact
    packedTile65536 3444089088 3444220160 14 6027 58686 32 _ _ (2195991 / 100000) (1097997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444220160 :
    ThetaLowerSegment 3444220160 3444351232 (344412911494709 / 100000)
      (344426065504759 / 100000) := by
  exact
    packedTile65536 3444220160 3444351232 14 5990 58687 32 _ _ (439199 / 20000) (1097999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444351232 :
    ThetaLowerSegment 3444351232 3444482304 (344426065504759 / 100000)
      (172219582319397 / 50000) := by
  exact
    packedTile65536 3444351232 3444482304 14 5965 58688 32 _ _ (2195999 / 100000) (1098001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444482304 :
    ThetaLowerSegment 3444482304 3444613376 (172219582319397 / 50000)
      (172226108837341 / 50000) := by
  exact
    packedTile65536 3444482304 3444613376 14 5944 58689 32 _ _ (1098001 / 50000) (439201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444613376 :
    ThetaLowerSegment 3444613376 3444744448 (172226108837341 / 50000)
      (172232745167473 / 50000) := by
  exact
    packedTile65536 3444613376 3444744448 14 6044 58690 32 _ _ (1098003 / 50000) (2196009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444744448 :
    ThetaLowerSegment 3444744448 3444875520 (172232745167473 / 50000)
      (172239315629393 / 50000) := by
  exact
    packedTile65536 3444744448 3444875520 14 5984 58691 32 _ _ (219601 / 10000) (2196013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3444875520 :
    ThetaLowerSegment 3444875520 3445006592 (172239315629393 / 50000) (86122929326553 / 25000) := by
  exact
    packedTile65536 3444875520 3445006592 14 5959 58693 32 _ _ (1098007 / 50000) (2196017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445006592 :
    ThetaLowerSegment 3445006592 3445137664 (86122929326553 / 25000) (86126223353553 / 25000) := by
  exact
    packedTile65536 3445006592 3445137664 14 6000 58694 32 _ _ (1098009 / 50000) (2196021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445137664 :
    ThetaLowerSegment 3445137664 3445268736 (86126223353553 / 25000) (86129442720339 / 25000) := by
  exact
    packedTile65536 3445137664 3445268736 14 5864 58695 32 _ _ (2196021 / 100000) (274503 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445268736 :
    ThetaLowerSegment 3445268736 3445399808 (86129442720339 / 25000) (172265423007103 / 50000) := by
  exact
    packedTile65536 3445268736 3445399808 14 5954 58696 32 _ _ (87841 / 4000) (549007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445399808 :
    ThetaLowerSegment 3445399808 3445530880 (172265423007103 / 50000)
      (172271888116479 / 50000) := by
  exact
    packedTile65536 3445399808 3445530880 14 5888 58697 32 _ _ (2196029 / 100000) (68626 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445530880 :
    ThetaLowerSegment 3445530880 3445661952 (172271888116479 / 50000)
      (344557055644509 / 100000) := by
  exact
    packedTile65536 3445530880 3445661952 14 6047 58698 32 _ _ (2196033 / 100000) (549009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445661952 :
    ThetaLowerSegment 3445661952 3445793024 (344557055644509 / 100000)
      (344570174769547 / 100000) := by
  exact
    packedTile65536 3445661952 3445793024 14 5974 58699 32 _ _ (2196037 / 100000) (54901 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445793024 :
    ThetaLowerSegment 3445793024 3445924096 (344570174769547 / 100000)
      (344583315872907 / 100000) := by
  exact
    packedTile65536 3445793024 3445924096 14 5984 58700 32 _ _ (54901 / 2500) (2196043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3445924096 :
    ThetaLowerSegment 3445924096 3446055168 (344583315872907 / 100000)
      (344596516293391 / 100000) := by
  exact
    packedTile65536 3445924096 3446055168 14 6011 58701 32 _ _ (549011 / 25000) (2196047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446055168 :
    ThetaLowerSegment 3446055168 3446186240 (344596516293391 / 100000)
      (344609778227263 / 100000) := by
  exact
    packedTile65536 3446055168 3446186240 14 6039 58703 32 _ _ (137253 / 6250) (2196051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446186240 :
    ThetaLowerSegment 3446186240 3446317312 (344609778227263 / 100000)
      (344623005048459 / 100000) := by
  exact
    packedTile65536 3446186240 3446317312 14 6023 58704 32 _ _ (549013 / 25000) (439211 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446317312 :
    ThetaLowerSegment 3446317312 3446448384 (344623005048459 / 100000)
      (68927245500327 / 20000) := by
  exact
    packedTile65536 3446317312 3446448384 14 6021 58705 32 _ _ (274507 / 12500) (2196059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446448384 :
    ThetaLowerSegment 3446448384 3446579456 (68927245500327 / 20000) (68929872866511 / 20000) := by
  exact
    packedTile65536 3446448384 3446579456 14 5982 58706 32 _ _ (109803 / 5000) (2196063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446579456 :
    ThetaLowerSegment 3446579456 3446710528 (68929872866511 / 20000)
      (344662690042839 / 100000) := by
  exact
    packedTile65536 3446579456 3446710528 14 6068 58707 32 _ _ (2196063 / 100000) (1098033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446710528 :
    ThetaLowerSegment 3446710528 3446841600 (344662690042839 / 100000)
      (344675954287519 / 100000) := by
  exact
    packedTile65536 3446710528 3446841600 14 6040 58708 32 _ _ (2196067 / 100000) (219607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446841600 :
    ThetaLowerSegment 3446841600 3446972672 (344675954287519 / 100000)
      (344689091184241 / 100000) := by
  exact
    packedTile65536 3446841600 3446972672 14 5982 58709 32 _ _ (2196071 / 100000) (1098037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3446972672 :
    ThetaLowerSegment 3446972672 3447103744 (344689091184241 / 100000)
      (43087762866077 / 12500) := by
  exact
    packedTile65536 3446972672 3447103744 14 5925 58710 32 _ _ (87843 / 4000) (1098039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447103744 :
    ThetaLowerSegment 3447103744 3447234816 (43087762866077 / 12500) (172357606760123 / 50000) := by
  exact
    packedTile65536 3447103744 3447234816 14 5970 58712 32 _ _ (2196079 / 100000) (1098041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447234816 :
    ThetaLowerSegment 3447234816 3447365888 (172357606760123 / 50000) (21545511885549 / 6250) := by
  exact
    packedTile65536 3447234816 3447365888 14 5909 58713 32 _ _ (1098041 / 50000) (439217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447365888 :
    ThetaLowerSegment 3447365888 3447496960 (21545511885549 / 6250) (172370517537899 / 50000) := by
  exact
    packedTile65536 3447365888 3447496960 14 5849 58714 32 _ _ (1098043 / 50000) (2196089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447496960 :
    ThetaLowerSegment 3447496960 3447628032 (172370517537899 / 50000)
      (172377092631359 / 50000) := by
  exact
    packedTile65536 3447496960 3447628032 14 5988 58715 32 _ _ (219609 / 10000) (2196093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447628032 :
    ThetaLowerSegment 3447628032 3447759104 (172377092631359 / 50000) (86191845397891 / 25000) := by
  exact
    packedTile65536 3447628032 3447759104 14 6009 58716 32 _ _ (1098047 / 50000) (2196097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447759104 :
    ThetaLowerSegment 3447759104 3447890176 (86191845397891 / 25000) (172390304344909 / 50000) := by
  exact
    packedTile65536 3447759104 3447890176 14 6023 58717 32 _ _ (1098049 / 50000) (2196101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3447890176 :
    ThetaLowerSegment 3447890176 3448021248 (172390304344909 / 50000)
      (172396831157081 / 50000) := by
  exact
    packedTile65536 3447890176 3448021248 14 5944 58718 32 _ _ (2196101 / 100000) (274513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448021248 :
    ThetaLowerSegment 3448021248 3448152320 (172396831157081 / 50000)
      (344806595176507 / 100000) := by
  exact
    packedTile65536 3448021248 3448152320 14 5889 58719 32 _ _ (439221 / 20000) (549027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448152320 :
    ThetaLowerSegment 3448152320 3448283392 (344806595176507 / 100000)
      (172409810149493 / 50000) := by
  exact
    packedTile65536 3448152320 3448283392 14 5931 58720 32 _ _ (2196109 / 100000) (137257 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448283392 :
    ThetaLowerSegment 3448283392 3448414464 (172409810149493 / 50000)
      (172416402880719 / 50000) := by
  exact
    packedTile65536 3448283392 3448414464 14 6004 58722 32 _ _ (2196113 / 100000) (549029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448414464 :
    ThetaLowerSegment 3448414464 3448545536 (172416402880719 / 50000)
      (344845826539131 / 100000) := by
  exact
    packedTile65536 3448414464 3448545536 14 5929 58723 32 _ _ (2196117 / 100000) (54903 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448545536 :
    ThetaLowerSegment 3448545536 3448676608 (344845826539131 / 100000)
      (344858827569531 / 100000) := by
  exact
    packedTile65536 3448545536 3448676608 14 5920 58724 32 _ _ (54903 / 2500) (2196123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448676608 :
    ThetaLowerSegment 3448676608 3448807680 (344858827569531 / 100000)
      (344871982352291 / 100000) := by
  exact
    packedTile65536 3448676608 3448807680 14 5990 58725 32 _ _ (549031 / 25000) (2196127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448807680 :
    ThetaLowerSegment 3448807680 3448938752 (344871982352291 / 100000)
      (68977002395943 / 20000) := by
  exact
    packedTile65536 3448807680 3448938752 14 5933 58726 32 _ _ (68629 / 3125) (2196131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3448938752 :
    ThetaLowerSegment 3448938752 3449069824 (68977002395943 / 20000)
      (344898074572851 / 100000) := by
  exact
    packedTile65536 3448938752 3449069824 14 5948 58727 32 _ _ (549033 / 25000) (439227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449069824 :
    ThetaLowerSegment 3449069824 3449200896 (344898074572851 / 100000)
      (344911053736611 / 100000) := by
  exact
    packedTile65536 3449069824 3449200896 14 5910 58728 32 _ _ (274517 / 12500) (2196139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449200896 :
    ThetaLowerSegment 3449200896 3449331968 (344911053736611 / 100000)
      (344924406261731 / 100000) := by
  exact
    packedTile65536 3449200896 3449331968 14 6080 58729 32 _ _ (2196139 / 100000) (1098071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449331968 :
    ThetaLowerSegment 3449331968 3449463040 (344924406261731 / 100000)
      (172468713596789 / 50000) := by
  exact
    packedTile65536 3449331968 3449463040 14 5929 58731 32 _ _ (2196143 / 100000) (1098073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449463040 :
    ThetaLowerSegment 3449463040 3449594112 (172468713596789 / 50000)
      (344950465718317 / 100000) := by
  exact
    packedTile65536 3449463040 3449594112 14 5937 58732 32 _ _ (2196147 / 100000) (43923 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449594112 :
    ThetaLowerSegment 3449594112 3449725184 (344950465718317 / 100000) (8624091779357 / 2500) := by
  exact
    packedTile65536 3449594112 3449725184 14 6013 58733 32 _ _ (2196151 / 100000) (1098077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449725184 :
    ThetaLowerSegment 3449725184 3449856256 (8624091779357 / 2500) (4312209942457 / 1250) := by
  exact
    packedTile65536 3449725184 3449856256 14 5976 58734 32 _ _ (439231 / 20000) (1098079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449856256 :
    ThetaLowerSegment 3449856256 3449987328 (4312209942457 / 1250) (43123738856517 / 12500) := by
  exact
    packedTile65536 3449856256 3449987328 14 5972 58735 32 _ _ (1098079 / 50000) (2196161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3449987328 :
    ThetaLowerSegment 3449987328 3450118400 (43123738856517 / 12500) (172501450575183 / 50000) := by
  exact
    packedTile65536 3449987328 3450118400 14 5915 58736 32 _ _ (1098081 / 50000) (439233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450118400 :
    ThetaLowerSegment 3450118400 3450249472 (172501450575183 / 50000) (86254006908637 / 25000) := by
  exact
    packedTile65536 3450118400 3450249472 14 5977 58737 32 _ _ (1098083 / 50000) (2196169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450249472 :
    ThetaLowerSegment 3450249472 3450380544 (86254006908637 / 25000) (86257307752147 / 25000) := by
  exact
    packedTile65536 3450249472 3450380544 14 6012 58738 32 _ _ (219617 / 10000) (2196173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450380544 :
    ThetaLowerSegment 3450380544 3450511616 (86257307752147 / 25000) (21565152424939 / 6250) := by
  exact
    packedTile65536 3450380544 3450511616 14 6014 58739 32 _ _ (1098087 / 50000) (2196177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450511616 :
    ThetaLowerSegment 3450511616 3450642688 (21565152424939 / 6250) (172527770595503 / 50000) := by
  exact
    packedTile65536 3450511616 3450642688 14 5966 58741 32 _ _ (2196177 / 100000) (109809 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450642688 :
    ThetaLowerSegment 3450642688 3450773760 (172527770595503 / 50000)
      (345068654587757 / 100000) := by
  exact
    packedTile65536 3450642688 3450773760 14 5971 58742 32 _ _ (2196181 / 100000) (274523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450773760 :
    ThetaLowerSegment 3450773760 3450904832 (345068654587757 / 100000)
      (43135216608679 / 12500) := by
  exact
    packedTile65536 3450773760 3450904832 14 5955 58743 32 _ _ (439237 / 20000) (549047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3450904832 :
    ThetaLowerSegment 3450904832 3451035904 (43135216608679 / 12500) (172547444020771 / 50000) := by
  exact
    packedTile65536 3450904832 3451035904 14 5990 58744 32 _ _ (2196189 / 100000) (68631 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451035904 :
    ThetaLowerSegment 3451035904 3451166976 (172547444020771 / 50000)
      (172554023814999 / 50000) := by
  exact
    packedTile65536 3451035904 3451166976 14 5992 58745 32 _ _ (2196193 / 100000) (549049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451166976 :
    ThetaLowerSegment 3451166976 3451298048 (172554023814999 / 50000)
      (172560594833431 / 50000) := by
  exact
    packedTile65536 3451166976 3451298048 14 5984 58746 32 _ _ (549049 / 25000) (2196199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451298048 :
    ThetaLowerSegment 3451298048 3451429120 (172560594833431 / 50000)
      (172567210885931 / 50000) := by
  exact
    packedTile65536 3451298048 3451429120 14 6025 58747 32 _ _ (10981 / 500) (2196203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451429120 :
    ThetaLowerSegment 3451429120 3451560192 (172567210885931 / 50000)
      (172573728121301 / 50000) := by
  exact
    packedTile65536 3451429120 3451560192 14 5935 58748 32 _ _ (549051 / 25000) (2196207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451560192 :
    ThetaLowerSegment 3451560192 3451691264 (172573728121301 / 50000) (34516058078161 / 10000) := by
  exact
    packedTile65536 3451560192 3451691264 14 5976 58749 32 _ _ (137263 / 6250) (2196211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451691264 :
    ThetaLowerSegment 3451691264 3451822336 (34516058078161 / 10000) (172586899890819 / 50000) := by
  exact
    packedTile65536 3451691264 3451822336 14 6019 58751 32 _ _ (549053 / 25000) (439243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451822336 :
    ThetaLowerSegment 3451822336 3451953408 (172586899890819 / 50000) (86296692656857 / 25000) := by
  exact
    packedTile65536 3451822336 3451953408 14 5906 58752 32 _ _ (439243 / 20000) (1098109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3451953408 :
    ThetaLowerSegment 3451953408 3452084480 (86296692656857 / 25000) (862999803967 / 250) := by
  exact
    packedTile65536 3451953408 3452084480 14 5988 58753 32 _ _ (2196219 / 100000) (1098111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452084480 :
    ThetaLowerSegment 3452084480 3452215552 (862999803967 / 250) (345213008879657 / 100000) := by
  exact
    packedTile65536 3452084480 3452215552 14 5959 58754 32 _ _ (2196223 / 100000) (1098113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452215552 :
    ThetaLowerSegment 3452215552 3452346624 (345213008879657 / 100000)
      (69045221435497 / 20000) := by
  exact
    packedTile65536 3452215552 3452346624 14 5964 58755 32 _ _ (2196227 / 100000) (219623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452346624 :
    ThetaLowerSegment 3452346624 3452477696 (69045221435497 / 20000)
      (345239258208713 / 100000) := by
  exact
    packedTile65536 3452346624 3452477696 14 5988 58756 32 _ _ (2196231 / 100000) (1098117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452477696 :
    ThetaLowerSegment 3452477696 3452608768 (345239258208713 / 100000)
      (345252290661269 / 100000) := by
  exact
    packedTile65536 3452477696 3452608768 14 5934 58757 32 _ _ (1098117 / 50000) (2196237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452608768 :
    ThetaLowerSegment 3452608768 3452739840 (345252290661269 / 100000)
      (345265509817791 / 100000) := by
  exact
    packedTile65536 3452608768 3452739840 14 6019 58758 32 _ _ (1098119 / 50000) (2196241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452739840 :
    ThetaLowerSegment 3452739840 3452870912 (345265509817791 / 100000)
      (345278623578773 / 100000) := by
  exact
    packedTile65536 3452739840 3452870912 14 5971 58760 32 _ _ (1098121 / 50000) (439249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3452870912 :
    ThetaLowerSegment 3452870912 3453001984 (345278623578773 / 100000)
      (345291770307329 / 100000) := by
  exact
    packedTile65536 3452870912 3453001984 14 5986 58761 32 _ _ (1098123 / 50000) (2196249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453001984 :
    ThetaLowerSegment 3453001984 3453133056 (345291770307329 / 100000)
      (345304886306357 / 100000) := by
  exact
    packedTile65536 3453001984 3453133056 14 5972 58762 32 _ _ (2196249 / 100000) (549063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453133056 :
    ThetaLowerSegment 3453133056 3453264128 (345304886306357 / 100000)
      (34531806602061 / 10000) := by
  exact
    packedTile65536 3453133056 3453264128 14 6001 58763 32 _ _ (2196253 / 100000) (68633 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453264128 :
    ThetaLowerSegment 3453264128 3453395200 (34531806602061 / 10000) (69066250908779 / 20000) := by
  exact
    packedTile65536 3453264128 3453395200 14 6005 58764 32 _ _ (2196257 / 100000) (109813 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453395200 :
    ThetaLowerSegment 3453395200 3453526272 (69066250908779 / 20000)
      (345344445287461 / 100000) := by
  exact
    packedTile65536 3453395200 3453526272 14 6006 58765 32 _ _ (2196261 / 100000) (274533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453526272 :
    ThetaLowerSegment 3453526272 3453657344 (345344445287461 / 100000) (10792422626423 / 3125) := by
  exact
    packedTile65536 3453526272 3453657344 14 5955 58766 32 _ _ (439253 / 20000) (549067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453657344 :
    ThetaLowerSegment 3453657344 3453788416 (10792422626423 / 3125) (17268522234509 / 5000) := by
  exact
    packedTile65536 3453657344 3453788416 14 5883 58767 32 _ _ (549067 / 25000) (2196271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453788416 :
    ThetaLowerSegment 3453788416 3453919488 (17268522234509 / 5000) (86345855066289 / 25000) := by
  exact
    packedTile65536 3453788416 3453919488 14 5908 58768 32 _ _ (137267 / 6250) (87851 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3453919488 :
    ThetaLowerSegment 3453919488 3454050560 (86345855066289 / 25000) (690793169487 / 200) := by
  exact
    packedTile65536 3453919488 3454050560 14 5994 58770 32 _ _ (549069 / 25000) (2196279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454050560 :
    ThetaLowerSegment 3454050560 3454181632 (690793169487 / 200) (17270488230989 / 5000) := by
  exact
    packedTile65536 3454050560 3454181632 14 6001 58771 32 _ _ (54907 / 2500) (2196283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454181632 :
    ThetaLowerSegment 3454181632 3454312704 (17270488230989 / 5000) (86355745464223 / 25000) := by
  exact
    packedTile65536 3454181632 3454312704 14 6018 58772 32 _ _ (549071 / 25000) (2196287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454312704 :
    ThetaLowerSegment 3454312704 3454443776 (86355745464223 / 25000) (86359017931853 / 25000) := by
  exact
    packedTile65536 3454312704 3454443776 14 5960 58773 32 _ _ (2196287 / 100000) (219629 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454443776 :
    ThetaLowerSegment 3454443776 3454574848 (86359017931853 / 25000)
      (345449229706793 / 100000) := by
  exact
    packedTile65536 3454443776 3454574848 14 5991 58774 32 _ _ (2196291 / 100000) (1098147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454574848 :
    ThetaLowerSegment 3454574848 3454705920 (345449229706793 / 100000)
      (345462121958443 / 100000) := by
  exact
    packedTile65536 3454574848 3454705920 14 5870 58775 32 _ _ (439259 / 20000) (1098149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454705920 :
    ThetaLowerSegment 3454705920 3454836992 (345462121958443 / 100000)
      (172737580692803 / 50000) := by
  exact
    packedTile65536 3454705920 3454836992 14 5937 58776 32 _ _ (2196299 / 100000) (1098151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454836992 :
    ThetaLowerSegment 3454836992 3454968064 (172737580692803 / 50000)
      (172744059786653 / 50000) := by
  exact
    packedTile65536 3454836992 3454968064 14 5900 58777 32 _ _ (2196303 / 100000) (1098153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3454968064 :
    ThetaLowerSegment 3454968064 3455099136 (172744059786653 / 50000) (43187646527483 / 12500) := by
  exact
    packedTile65536 3454968064 3455099136 14 5943 58778 32 _ _ (1098153 / 50000) (2196309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455099136 :
    ThetaLowerSegment 3455099136 3455230208 (43187646527483 / 12500) (172757151978677 / 50000) := by
  exact
    packedTile65536 3455099136 3455230208 14 5979 58780 32 _ _ (219631 / 10000) (2196313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455230208 :
    ThetaLowerSegment 3455230208 3455361280 (172757151978677 / 50000) (34552735884777 / 10000) := by
  exact
    packedTile65536 3455230208 3455361280 14 5944 58781 32 _ _ (1098157 / 50000) (2196317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455361280 :
    ThetaLowerSegment 3455361280 3455492352 (34552735884777 / 10000) (86385144621453 / 25000) := by
  exact
    packedTile65536 3455361280 3455492352 14 6019 58782 32 _ _ (1098159 / 50000) (2196321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455492352 :
    ThetaLowerSegment 3455492352 3455623424 (86385144621453 / 25000) (172776806828441 / 50000) := by
  exact
    packedTile65536 3455492352 3455623424 14 5935 58783 32 _ _ (1098161 / 50000) (87853 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455623424 :
    ThetaLowerSegment 3455623424 3455754496 (172776806828441 / 50000)
      (172783378232841 / 50000) := by
  exact
    packedTile65536 3455623424 3455754496 14 5984 58784 32 _ _ (87853 / 4000) (274541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455754496 :
    ThetaLowerSegment 3455754496 3455885568 (172783378232841 / 50000) (34557987294247 / 10000) := by
  exact
    packedTile65536 3455754496 3455885568 14 5972 58785 32 _ _ (2196329 / 100000) (549083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3455885568 :
    ThetaLowerSegment 3455885568 3456016640 (34557987294247 / 10000) (69118629955091 / 20000) := by
  exact
    packedTile65536 3455885568 3456016640 14 6045 58786 32 _ _ (2196333 / 100000) (137271 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456016640 :
    ThetaLowerSegment 3456016640 3456147712 (69118629955091 / 20000) (172803140837189 / 50000) := by
  exact
    packedTile65536 3456016640 3456147712 14 5979 58787 32 _ _ (2196337 / 100000) (109817 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456147712 :
    ThetaLowerSegment 3456147712 3456278784 (172803140837189 / 50000)
      (345619422382581 / 100000) := by
  exact
    packedTile65536 3456147712 3456278784 14 5983 58789 32 _ _ (2196341 / 100000) (274543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456278784 :
    ThetaLowerSegment 3456278784 3456409856 (345619422382581 / 100000)
      (345632532359917 / 100000) := by
  exact
    packedTile65536 3456278784 3456409856 14 5969 58790 32 _ _ (274543 / 12500) (2196347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456409856 :
    ThetaLowerSegment 3456409856 3456540928 (345632532359917 / 100000)
      (345645717036961 / 100000) := by
  exact
    packedTile65536 3456409856 3456540928 14 6003 58791 32 _ _ (549087 / 25000) (2196351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456540928 :
    ThetaLowerSegment 3456540928 3456672000 (345645717036961 / 100000)
      (345658934683297 / 100000) := by
  exact
    packedTile65536 3456540928 3456672000 14 6018 58792 32 _ _ (68636 / 3125) (439271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456672000 :
    ThetaLowerSegment 3456672000 3456803072 (345658934683297 / 100000)
      (345672158942773 / 100000) := by
  exact
    packedTile65536 3456672000 3456803072 14 6021 58793 32 _ _ (549089 / 25000) (2196359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456803072 :
    ThetaLowerSegment 3456803072 3456934144 (345672158942773 / 100000)
      (345685295371933 / 100000) := by
  exact
    packedTile65536 3456803072 3456934144 14 5981 58794 32 _ _ (54909 / 2500) (2196363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3456934144 :
    ThetaLowerSegment 3456934144 3457065216 (345685295371933 / 100000)
      (172849156607717 / 50000) := by
  exact
    packedTile65536 3456934144 3457065216 14 5927 58795 32 _ _ (2196363 / 100000) (1098183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457065216 :
    ThetaLowerSegment 3457065216 3457196288 (172849156607717 / 50000)
      (345711401366387 / 100000) := by
  exact
    packedTile65536 3457065216 3457196288 14 5959 58796 32 _ _ (2196367 / 100000) (219637 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457196288 :
    ThetaLowerSegment 3457196288 3457327360 (345711401366387 / 100000)
      (345724474166579 / 100000) := by
  exact
    packedTile65536 3457196288 3457327360 14 5952 58797 32 _ _ (2196371 / 100000) (1098187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457327360 :
    ThetaLowerSegment 3457327360 3457458432 (345724474166579 / 100000)
      (345737450350079 / 100000) := by
  exact
    packedTile65536 3457327360 3457458432 14 5908 58799 32 _ _ (17571 / 800) (1098189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457458432 :
    ThetaLowerSegment 3457458432 3457589504 (345737450350079 / 100000)
      (69150087067363 / 20000) := by
  exact
    packedTile65536 3457458432 3457589504 14 5912 58800 32 _ _ (1098189 / 50000) (2196381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457589504 :
    ThetaLowerSegment 3457589504 3457720576 (69150087067363 / 20000)
      (345763442311019 / 100000) := by
  exact
    packedTile65536 3457589504 3457720576 14 5922 58801 32 _ _ (1098191 / 50000) (439277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457720576 :
    ThetaLowerSegment 3457720576 3457851648 (345763442311019 / 100000)
      (345776482254701 / 100000) := by
  exact
    packedTile65536 3457720576 3457851648 14 5937 58802 32 _ _ (1098193 / 50000) (2196389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457851648 :
    ThetaLowerSegment 3457851648 3457982720 (345776482254701 / 100000)
      (345789700129721 / 100000) := by
  exact
    packedTile65536 3457851648 3457982720 14 6018 58803 32 _ _ (219639 / 10000) (2196393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3457982720 :
    ThetaLowerSegment 3457982720 3458113792 (345789700129721 / 100000)
      (345802816994689 / 100000) := by
  exact
    packedTile65536 3457982720 3458113792 14 5972 58804 32 _ _ (1098197 / 50000) (2196397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458113792 :
    ThetaLowerSegment 3458113792 3458244864 (345802816994689 / 100000)
      (172907941680221 / 50000) := by
  exact
    packedTile65536 3458113792 3458244864 14 5949 58805 32 _ _ (2196397 / 100000) (5491 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458244864 :
    ThetaLowerSegment 3458244864 3458375936 (172907941680221 / 50000) (34582881576953 / 10000) := by
  exact
    packedTile65536 3458244864 3458375936 14 5888 58806 32 _ _ (2196401 / 100000) (549101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458375936 :
    ThetaLowerSegment 3458375936 3458507008 (34582881576953 / 10000) (34584209962697 / 10000) := by
  exact
    packedTile65536 3458375936 3458507008 14 6048 58807 32 _ _ (439281 / 20000) (274551 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458507008 :
    ThetaLowerSegment 3458507008 3458638080 (34584209962697 / 10000)
      (345855174849747 / 100000) := by
  exact
    packedTile65536 3458507008 3458638080 14 5953 58809 32 _ _ (2196409 / 100000) (549103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458638080 :
    ThetaLowerSegment 3458638080 3458769152 (345855174849747 / 100000)
      (172934021816757 / 50000) := by
  exact
    packedTile65536 3458638080 3458769152 14 5859 58810 32 _ _ (2196413 / 100000) (68638 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458769152 :
    ThetaLowerSegment 3458769152 3458900224 (172934021816757 / 50000) (6917624266877 / 2000) := by
  exact
    packedTile65536 3458769152 3458900224 14 5996 58811 32 _ _ (68638 / 3125) (2196419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3458900224 :
    ThetaLowerSegment 3458900224 3459031296 (6917624266877 / 2000) (34589435452471 / 10000) := by
  exact
    packedTile65536 3458900224 3459031296 14 5983 58812 32 _ _ (109821 / 5000) (2196423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459031296 :
    ThetaLowerSegment 3459031296 3459162368 (34589435452471 / 10000) (172953703936271 / 50000) := by
  exact
    packedTile65536 3459031296 3459162368 14 5943 58813 32 _ _ (274553 / 12500) (2196427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459162368 :
    ThetaLowerSegment 3459162368 3459293440 (172953703936271 / 50000) (6918410015597 / 2000) := by
  exact
    packedTile65536 3459162368 3459293440 14 5961 58814 32 _ _ (549107 / 25000) (2196431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459293440 :
    ThetaLowerSegment 3459293440 3459424512 (6918410015597 / 2000) (172966800150149 / 50000) := by
  exact
    packedTile65536 3459293440 3459424512 14 5964 58815 32 _ _ (137277 / 6250) (439287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459424512 :
    ThetaLowerSegment 3459424512 3459555584 (172966800150149 / 50000)
      (345946662499243 / 100000) := by
  exact
    packedTile65536 3459424512 3459555584 14 5947 58816 32 _ _ (439287 / 20000) (1098219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459555584 :
    ThetaLowerSegment 3459555584 3459686656 (345946662499243 / 100000) (8648989603747 / 2500) := by
  exact
    packedTile65536 3459555584 3459686656 14 5883 58817 32 _ _ (2196439 / 100000) (1098221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459686656 :
    ThetaLowerSegment 3459686656 3459817728 (8648989603747 / 2500) (86493166541097 / 25000) := by
  exact
    packedTile65536 3459686656 3459817728 14 5956 58819 32 _ _ (2196443 / 100000) (1098223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459817728 :
    ThetaLowerSegment 3459817728 3459948800 (86493166541097 / 25000) (172992915833853 / 50000) := by
  exact
    packedTile65536 3459817728 3459948800 14 5994 58820 32 _ _ (2196447 / 100000) (43929 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3459948800 :
    ThetaLowerSegment 3459948800 3460079872 (172992915833853 / 50000)
      (172999571077353 / 50000) := by
  exact
    packedTile65536 3459948800 3460079872 14 6060 58821 32 _ _ (43929 / 2000) (2196453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460079872 :
    ThetaLowerSegment 3460079872 3460210944 (172999571077353 / 50000) (17300612859077 / 5000) := by
  exact
    packedTile65536 3460079872 3460210944 14 5971 58822 32 _ _ (1098227 / 50000) (2196457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460210944 :
    ThetaLowerSegment 3460210944 3460342016 (17300612859077 / 5000) (34602540298267 / 10000) := by
  exact
    packedTile65536 3460210944 3460342016 14 5985 58823 32 _ _ (1098229 / 50000) (2196461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460342016 :
    ThetaLowerSegment 3460342016 3460473088 (34602540298267 / 10000) (86509628416087 / 25000) := by
  exact
    packedTile65536 3460342016 3460473088 14 5969 58824 32 _ _ (1098231 / 50000) (439293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460473088 :
    ThetaLowerSegment 3460473088 3460604160 (86509628416087 / 25000) (86512916525689 / 25000) := by
  exact
    packedTile65536 3460473088 3460604160 14 5988 58825 32 _ _ (1098233 / 50000) (2196469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460604160 :
    ThetaLowerSegment 3460604160 3460735232 (86512916525689 / 25000) (86516211229189 / 25000) := by
  exact
    packedTile65536 3460604160 3460735232 14 6000 58826 32 _ _ (2196469 / 100000) (274559 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460735232 :
    ThetaLowerSegment 3460735232 3460866304 (86516211229189 / 25000)
      (346078034737121 / 100000) := by
  exact
    packedTile65536 3460735232 3460866304 14 6005 58828 32 _ _ (2196473 / 100000) (549119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460866304 :
    ThetaLowerSegment 3460866304 3460997376 (346078034737121 / 100000)
      (173045563968259 / 50000) := by
  exact
    packedTile65536 3460866304 3460997376 14 5961 58829 32 _ _ (2196477 / 100000) (13728 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3460997376 :
    ThetaLowerSegment 3460997376 3461128448 (173045563968259 / 50000)
      (346104128907557 / 100000) := by
  exact
    packedTile65536 3460997376 3461128448 14 5919 58830 32 _ _ (2196481 / 100000) (549121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461128448 :
    ThetaLowerSegment 3461128448 3461259520 (346104128907557 / 100000)
      (86529289065023 / 25000) := by
  exact
    packedTile65536 3461128448 3461259520 14 5931 58831 32 _ _ (439297 / 20000) (274561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461259520 :
    ThetaLowerSegment 3461259520 3461390592 (86529289065023 / 25000) (17306511378009 / 5000) := by
  exact
    packedTile65536 3461259520 3461390592 14 5951 58832 32 _ _ (274561 / 12500) (2196491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461390592 :
    ThetaLowerSegment 3461390592 3461521664 (17306511378009 / 5000) (43267923342969 / 12500) := by
  exact
    packedTile65536 3461390592 3461521664 14 5991 58833 32 _ _ (549123 / 25000) (439299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461521664 :
    ThetaLowerSegment 3461521664 3461652736 (43267923342969 / 12500) (43269553143001 / 12500) := by
  exact
    packedTile65536 3461521664 3461652736 14 5936 58834 32 _ _ (137281 / 6250) (2196499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461652736 :
    ThetaLowerSegment 3461652736 3461783808 (43269553143001 / 12500) (86542392799127 / 25000) := by
  exact
    packedTile65536 3461652736 3461783808 14 5985 58835 32 _ _ (4393 / 200) (2196503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461783808 :
    ThetaLowerSegment 3461783808 3461914880 (86542392799127 / 25000)
      (346182717266963 / 100000) := by
  exact
    packedTile65536 3461783808 3461914880 14 5985 58836 32 _ _ (2196503 / 100000) (1098253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3461914880 :
    ThetaLowerSegment 3461914880 3462045952 (346182717266963 / 100000)
      (346196028099383 / 100000) := by
  exact
    packedTile65536 3461914880 3462045952 14 6060 58838 32 _ _ (2196507 / 100000) (219651 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462045952 :
    ThetaLowerSegment 3462045952 3462177024 (346196028099383 / 100000)
      (346209215951427 / 100000) := by
  exact
    packedTile65536 3462045952 3462177024 14 6004 58839 32 _ _ (2196511 / 100000) (1098257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462177024 :
    ThetaLowerSegment 3462177024 3462308096 (346209215951427 / 100000)
      (43277792516069 / 12500) := by
  exact
    packedTile65536 3462177024 3462308096 14 5975 58840 32 _ _ (439303 / 20000) (1098259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462308096 :
    ThetaLowerSegment 3462308096 3462439168 (43277792516069 / 12500) (13849413477259 / 4000) := by
  exact
    packedTile65536 3462308096 3462439168 14 5917 58841 32 _ _ (2196519 / 100000) (1098261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462439168 :
    ThetaLowerSegment 3462439168 3462570240 (13849413477259 / 4000) (346248432595639 / 100000) := by
  exact
    packedTile65536 3462439168 3462570240 14 5962 58842 32 _ _ (1098261 / 50000) (87861 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462570240 :
    ThetaLowerSegment 3462570240 3462701312 (346248432595639 / 100000)
      (346261761115407 / 100000) := by
  exact
    packedTile65536 3462570240 3462701312 14 6068 58843 32 _ _ (1098263 / 50000) (2196529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462701312 :
    ThetaLowerSegment 3462701312 3462832384 (346261761115407 / 100000)
      (346274907347457 / 100000) := by
  exact
    packedTile65536 3462701312 3462832384 14 5985 58844 32 _ _ (219653 / 10000) (2196533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462832384 :
    ThetaLowerSegment 3462832384 3462963456 (346274907347457 / 100000)
      (346287985510893 / 100000) := by
  exact
    packedTile65536 3462832384 3462963456 14 5954 58845 32 _ _ (1098267 / 50000) (2196537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3462963456 :
    ThetaLowerSegment 3462963456 3463094528 (346287985510893 / 100000)
      (346301204276577 / 100000) := by
  exact
    packedTile65536 3462963456 3463094528 14 6018 58846 32 _ _ (1098269 / 50000) (2196541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463094528 :
    ThetaLowerSegment 3463094528 3463225600 (346301204276577 / 100000)
      (346314343984839 / 100000) := by
  exact
    packedTile65536 3463094528 3463225600 14 5982 58848 32 _ _ (2196541 / 100000) (68642 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463225600 :
    ThetaLowerSegment 3463225600 3463356672 (346314343984839 / 100000)
      (346327593544279 / 100000) := by
  exact
    packedTile65536 3463225600 3463356672 14 6032 58849 32 _ _ (439309 / 20000) (549137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463356672 :
    ThetaLowerSegment 3463356672 3463487744 (346327593544279 / 100000)
      (173170376534669 / 50000) := by
  exact
    packedTile65536 3463356672 3463487744 14 5991 58850 32 _ _ (2196549 / 100000) (274569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463487744 :
    ThetaLowerSegment 3463487744 3463618816 (173170376534669 / 50000)
      (173176913476397 / 50000) := by
  exact
    packedTile65536 3463487744 3463618816 14 5952 58851 32 _ _ (2196553 / 100000) (549139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463618816 :
    ThetaLowerSegment 3463618816 3463749888 (173176913476397 / 50000)
      (173183489965061 / 50000) := by
  exact
    packedTile65536 3463618816 3463749888 14 5988 58852 32 _ _ (549139 / 25000) (2196559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463749888 :
    ThetaLowerSegment 3463749888 3463880960 (173183489965061 / 50000)
      (173190032419021 / 50000) := by
  exact
    packedTile65536 3463749888 3463880960 14 5957 58853 32 _ _ (27457 / 1250) (2196563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3463880960 :
    ThetaLowerSegment 3463880960 3464012032 (173190032419021 / 50000) (34639317173543 / 10000) := by
  exact
    packedTile65536 3463880960 3464012032 14 5967 58854 32 _ _ (549141 / 25000) (2196567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464012032 :
    ThetaLowerSegment 3464012032 3464143104 (34639317173543 / 10000) (173203239272187 / 50000) := by
  exact
    packedTile65536 3464012032 3464143104 14 6058 58855 32 _ _ (274571 / 12500) (2196571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464143104 :
    ThetaLowerSegment 3464143104 3464274176 (173203239272187 / 50000)
      (173209721356159 / 50000) := by
  exact
    packedTile65536 3464143104 3464274176 14 5902 58856 32 _ _ (549143 / 25000) (87863 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464274176 :
    ThetaLowerSegment 3464274176 3464405248 (173209721356159 / 50000)
      (346432685862993 / 100000) := by
  exact
    packedTile65536 3464274176 3464405248 14 6029 58858 32 _ _ (87863 / 4000) (1098289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464405248 :
    ThetaLowerSegment 3464405248 3464536320 (346432685862993 / 100000)
      (346446063029103 / 100000) := by
  exact
    packedTile65536 3464405248 3464536320 14 6090 58859 32 _ _ (2196579 / 100000) (1098291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464536320 :
    ThetaLowerSegment 3464536320 3464667392 (346446063029103 / 100000)
      (43307387468651 / 12500) := by
  exact
    packedTile65536 3464536320 3464667392 14 5935 58860 32 _ _ (2196583 / 100000) (1098293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464667392 :
    ThetaLowerSegment 3464667392 3464798464 (43307387468651 / 12500) (173236111079973 / 50000) := by
  exact
    packedTile65536 3464667392 3464798464 14 5974 58861 32 _ _ (2196587 / 100000) (219659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464798464 :
    ThetaLowerSegment 3464798464 3464929536 (173236111079973 / 50000) (86621287823643 / 25000) := by
  exact
    packedTile65536 3464798464 3464929536 14 5886 58862 32 _ _ (2196591 / 100000) (1098297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3464929536 :
    ThetaLowerSegment 3464929536 3465060608 (86621287823643 / 25000) (173249135775267 / 50000) := by
  exact
    packedTile65536 3464929536 3465060608 14 5973 58863 32 _ _ (1098297 / 50000) (2196597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465060608 :
    ThetaLowerSegment 3465060608 3465191680 (173249135775267 / 50000) (43313908053463 / 12500) := by
  exact
    packedTile65536 3465060608 3465191680 14 5915 58864 32 _ _ (1098299 / 50000) (2196601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465191680 :
    ThetaLowerSegment 3465191680 3465322752 (43313908053463 / 12500) (173262190169123 / 50000) := by
  exact
    packedTile65536 3465191680 3465322752 14 5971 58865 32 _ _ (1098301 / 50000) (439321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465322752 :
    ThetaLowerSegment 3465322752 3465339136 (173262190169123 / 50000)
      (173263031469221 / 50000) := by
  exact
    packedTile65536 3465322752 3465339136 11 766 58866 32 _ _ (1098303 / 50000) (2196609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465339136 :
    ThetaLowerSegment 3465339136 3465341184 (173263031469221 / 50000)
      (173263125923279 / 50000) := by
  exact
    packedTile65536 3465339136 3465341184 8 86 58867 32 _ _ (1098303 / 50000) (2196609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3433341184_3465341184 :
    ThetaLowerSegment 3433341184 3465341184 (343324875317073 / 100000)
      (173263125923279 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3433341184 cell3433472256)
                  (ThetaLowerSegment.join cell3433603328 cell3433734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3433865472 cell3433996544)
                  (ThetaLowerSegment.join cell3434127616 cell3434258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3434389760 cell3434520832)
                  (ThetaLowerSegment.join cell3434651904 cell3434782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3434914048 cell3435045120)
                  (ThetaLowerSegment.join cell3435176192 cell3435307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3435438336 cell3435569408)
                  (ThetaLowerSegment.join cell3435700480 cell3435831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3435962624 cell3436093696)
                  (ThetaLowerSegment.join cell3436224768 cell3436355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3436486912 cell3436617984)
                  (ThetaLowerSegment.join cell3436749056 cell3436880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3437011200 cell3437142272)
                  (ThetaLowerSegment.join cell3437273344 cell3437404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3437535488 cell3437666560)
                  (ThetaLowerSegment.join cell3437797632 cell3437928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3438059776 cell3438190848)
                  (ThetaLowerSegment.join cell3438321920 cell3438452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3438584064 cell3438715136)
                  (ThetaLowerSegment.join cell3438846208 cell3438977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3439108352 cell3439239424)
                  (ThetaLowerSegment.join cell3439370496 cell3439501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3439632640 cell3439763712)
                  (ThetaLowerSegment.join cell3439894784 cell3440025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3440156928 cell3440288000)
                  (ThetaLowerSegment.join cell3440419072 cell3440550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3440681216 cell3440812288)
                  (ThetaLowerSegment.join cell3440943360 cell3441074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3441205504 cell3441336576)
                  (ThetaLowerSegment.join cell3441467648 cell3441598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3441729792 cell3441860864)
                  (ThetaLowerSegment.join cell3441991936 cell3442123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3442254080 cell3442385152)
                  (ThetaLowerSegment.join cell3442516224 cell3442647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3442778368 cell3442909440)
                  (ThetaLowerSegment.join cell3443040512 cell3443171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3443302656 cell3443433728)
                  (ThetaLowerSegment.join cell3443564800 cell3443695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3443826944 cell3443958016)
                  (ThetaLowerSegment.join cell3444089088 cell3444220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3444351232 cell3444482304)
                  (ThetaLowerSegment.join cell3444613376 cell3444744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3444875520 cell3445006592)
                  (ThetaLowerSegment.join cell3445137664 cell3445268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3445399808 cell3445530880)
                  (ThetaLowerSegment.join cell3445661952 cell3445793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3445924096 cell3446055168)
                  (ThetaLowerSegment.join cell3446186240 cell3446317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3446448384 cell3446579456)
                  (ThetaLowerSegment.join cell3446710528 cell3446841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3446972672 cell3447103744)
                  (ThetaLowerSegment.join cell3447234816 cell3447365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3447496960 cell3447628032)
                  (ThetaLowerSegment.join cell3447759104 cell3447890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3448021248 cell3448152320)
                  (ThetaLowerSegment.join cell3448283392 cell3448414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3448545536 cell3448676608)
                  (ThetaLowerSegment.join cell3448807680 cell3448938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3449069824 cell3449200896)
                  (ThetaLowerSegment.join cell3449331968 cell3449463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3449594112 cell3449725184)
                  (ThetaLowerSegment.join cell3449856256 cell3449987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3450118400 cell3450249472)
                  (ThetaLowerSegment.join cell3450380544 cell3450511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3450642688 cell3450773760)
                  (ThetaLowerSegment.join cell3450904832 cell3451035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3451166976 cell3451298048)
                  (ThetaLowerSegment.join cell3451429120 cell3451560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3451691264 cell3451822336)
                  (ThetaLowerSegment.join cell3451953408 cell3452084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3452215552 cell3452346624)
                  (ThetaLowerSegment.join cell3452477696 cell3452608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3452739840 cell3452870912)
                  (ThetaLowerSegment.join cell3453001984 cell3453133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3453264128 cell3453395200)
                  (ThetaLowerSegment.join cell3453526272 cell3453657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3453788416 cell3453919488)
                  (ThetaLowerSegment.join cell3454050560 cell3454181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3454312704 cell3454443776)
                  (ThetaLowerSegment.join cell3454574848 cell3454705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3454836992 cell3454968064)
                  (ThetaLowerSegment.join cell3455099136 cell3455230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3455361280 cell3455492352)
                  (ThetaLowerSegment.join cell3455623424 cell3455754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3455885568 cell3456016640)
                  (ThetaLowerSegment.join cell3456147712 cell3456278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3456409856 cell3456540928)
                  (ThetaLowerSegment.join cell3456672000 cell3456803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3456934144 cell3457065216)
                  (ThetaLowerSegment.join cell3457196288 cell3457327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3457458432 cell3457589504)
                  (ThetaLowerSegment.join cell3457720576 cell3457851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3457982720 cell3458113792)
                  (ThetaLowerSegment.join cell3458244864 cell3458375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3458507008 cell3458638080)
                  (ThetaLowerSegment.join cell3458769152 cell3458900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3459031296 cell3459162368)
                  (ThetaLowerSegment.join cell3459293440 cell3459424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3459555584 cell3459686656)
                  (ThetaLowerSegment.join cell3459817728 cell3459948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3460079872 cell3460210944)
                  (ThetaLowerSegment.join cell3460342016 cell3460473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3460604160 cell3460735232)
                  (ThetaLowerSegment.join cell3460866304 cell3460997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3461128448 cell3461259520)
                  (ThetaLowerSegment.join cell3461390592 cell3461521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3461652736 cell3461783808)
                  (ThetaLowerSegment.join cell3461914880 cell3462045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3462177024 cell3462308096)
                  (ThetaLowerSegment.join cell3462439168 cell3462570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3462701312 cell3462832384)
                  (ThetaLowerSegment.join cell3462963456 cell3463094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3463225600 cell3463356672)
                  (ThetaLowerSegment.join cell3463487744 cell3463618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3463749888 cell3463880960)
                  (ThetaLowerSegment.join cell3464012032 cell3464143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3464274176 cell3464405248)
                  (ThetaLowerSegment.join cell3464536320 cell3464667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3464798464 cell3464929536)
                (ThetaLowerSegment.join cell3465060608 cell3465191680))
              (ThetaLowerSegment.join cell3465322752 cell3465339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
