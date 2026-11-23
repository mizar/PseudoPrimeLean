/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3017341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2985341184 :
    ThetaLowerSegment 2985341184 2985472256 (298527603773077 / 100000)
      (298540833577621 / 100000) := by
  exact
    packedTile65536 2985341184 2985472256 14 6064 54638 31 _ _ (68178 / 3125) (2181699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985472256 :
    ThetaLowerSegment 2985472256 2985603328 (298540833577621 / 100000)
      (298554137590319 / 100000) := by
  exact
    packedTile65536 2985472256 2985603328 14 6098 54639 31 _ _ (2181701 / 100000) (272713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985603328 :
    ThetaLowerSegment 2985603328 2985734400 (298554137590319 / 100000)
      (298567144915529 / 100000) := by
  exact
    packedTile65536 2985603328 2985734400 14 5962 54640 31 _ _ (436341 / 20000) (545427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985734400 :
    ThetaLowerSegment 2985734400 2985865472 (298567144915529 / 100000)
      (298580232993819 / 100000) := by
  exact
    packedTile65536 2985734400 2985865472 14 5999 54641 31 _ _ (218171 / 10000) (2181713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985865472 :
    ThetaLowerSegment 2985865472 2985996544 (298580232993819 / 100000)
      (59718638038653 / 20000) := by
  exact
    packedTile65536 2985865472 2985996544 14 5939 54643 31 _ _ (1090857 / 50000) (2181717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985996544 :
    ThetaLowerSegment 2985996544 2986127616 (59718638038653 / 20000)
      (298606223776597 / 100000) := by
  exact
    packedTile65536 2985996544 2986127616 14 5974 54644 31 _ _ (1090859 / 50000) (2181721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986127616 :
    ThetaLowerSegment 2986127616 2986258688 (298606223776597 / 100000)
      (149309673420221 / 50000) := by
  exact
    packedTile65536 2986127616 2986258688 14 6015 54645 31 _ _ (2181723 / 100000) (1090863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986258688 :
    ThetaLowerSegment 2986258688 2986389760 (149309673420221 / 50000)
      (298632517926341 / 100000) := by
  exact
    packedTile65536 2986258688 2986389760 14 6037 54646 31 _ _ (2181727 / 100000) (218173 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986389760 :
    ThetaLowerSegment 2986389760 2986520832 (298632517926341 / 100000)
      (59729109445969 / 20000) := by
  exact
    packedTile65536 2986389760 2986520832 14 5972 54647 31 _ _ (545433 / 25000) (436347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986520832 :
    ThetaLowerSegment 2986520832 2986651904 (59729109445969 / 20000) (59731749346529 / 20000) := by
  exact
    packedTile65536 2986520832 2986651904 14 6050 54649 31 _ _ (272717 / 12500) (2181739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986651904 :
    ThetaLowerSegment 2986651904 2986782976 (59731749346529 / 20000) (59734362198353 / 20000) := by
  exact
    packedTile65536 2986651904 2986782976 14 5988 54650 31 _ _ (109087 / 5000) (2181743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986782976 :
    ThetaLowerSegment 2986782976 2986914048 (59734362198353 / 20000) (59737003855199 / 20000) := by
  exact
    packedTile65536 2986782976 2986914048 14 6054 54651 31 _ _ (436349 / 20000) (545437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2986914048 :
    ThetaLowerSegment 2986914048 2987045120 (59737003855199 / 20000) (149349197789557 / 50000) := by
  exact
    packedTile65536 2986914048 2987045120 14 6131 54652 31 _ _ (2181749 / 100000) (272719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987045120 :
    ThetaLowerSegment 2987045120 2987176192 (149349197789557 / 50000) (29871132028981 / 10000) := by
  exact
    packedTile65536 2987045120 2987176192 14 5924 54653 31 _ _ (1090877 / 50000) (2181757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987176192 :
    ThetaLowerSegment 2987176192 2987307264 (29871132028981 / 10000) (74681117436319 / 25000) := by
  exact
    packedTile65536 2987176192 2987307264 14 6027 54655 31 _ _ (1090879 / 50000) (2181761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987307264 :
    ThetaLowerSegment 2987307264 2987438336 (74681117436319 / 25000) (74684455532179 / 25000) := by
  exact
    packedTile65536 2987307264 2987438336 14 6120 54656 31 _ _ (1090881 / 50000) (436353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987438336 :
    ThetaLowerSegment 2987438336 2987569408 (74684455532179 / 25000) (14937549127363 / 5000) := by
  exact
    packedTile65536 2987438336 2987569408 14 6032 54657 31 _ _ (2181767 / 100000) (218177 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987569408 :
    ThetaLowerSegment 2987569408 2987700480 (14937549127363 / 5000) (29876413862639 / 10000) := by
  exact
    packedTile65536 2987569408 2987700480 14 6030 54658 31 _ _ (2181771 / 100000) (1090887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987700480 :
    ThetaLowerSegment 2987700480 2987831552 (29876413862639 / 10000) (29877723800349 / 10000) := by
  exact
    packedTile65536 2987700480 2987831552 14 6004 54659 31 _ _ (87271 / 4000) (1090889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987831552 :
    ThetaLowerSegment 2987831552 2987962624 (29877723800349 / 10000) (29879043777249 / 10000) := by
  exact
    packedTile65536 2987831552 2987962624 14 6050 54661 31 _ _ (109089 / 5000) (2181783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2987962624 :
    ThetaLowerSegment 2987962624 2988093696 (29879043777249 / 10000) (1195214244813 / 400) := by
  exact
    packedTile65536 2987962624 2988093696 14 6015 54662 31 _ _ (272723 / 12500) (2181787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988093696 :
    ThetaLowerSegment 2988093696 2988224768 (1195214244813 / 400) (149408373967983 / 50000) := by
  exact
    packedTile65536 2988093696 2988224768 14 6044 54663 31 _ _ (2181789 / 100000) (68181 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988224768 :
    ThetaLowerSegment 2988224768 2988355840 (149408373967983 / 50000) (59765964684283 / 20000) := by
  exact
    packedTile65536 2988224768 2988355840 14 5993 54664 31 _ _ (2181793 / 100000) (545449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988355840 :
    ThetaLowerSegment 2988355840 2988486912 (59765964684283 / 20000)
      (298842931657791 / 100000) := by
  exact
    packedTile65536 2988355840 2988486912 14 6008 54665 31 _ _ (2181797 / 100000) (10909 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988486912 :
    ThetaLowerSegment 2988486912 2988617984 (298842931657791 / 100000)
      (298855954833929 / 100000) := by
  exact
    packedTile65536 2988486912 2988617984 14 5969 54667 31 _ _ (1090901 / 50000) (436361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988617984 :
    ThetaLowerSegment 2988617984 2988749056 (298855954833929 / 100000)
      (298869093669661 / 100000) := by
  exact
    packedTile65536 2988617984 2988749056 14 6022 54668 31 _ _ (1090903 / 50000) (2181809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988749056 :
    ThetaLowerSegment 2988749056 2988880128 (298869093669661 / 100000)
      (298882066717867 / 100000) := by
  exact
    packedTile65536 2988749056 2988880128 14 5946 54669 31 _ _ (2181811 / 100000) (1090907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2988880128 :
    ThetaLowerSegment 2988880128 2989011200 (298882066717867 / 100000)
      (149447505713131 / 50000) := by
  exact
    packedTile65536 2988880128 2989011200 14 5933 54670 31 _ _ (436363 / 20000) (1090909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989011200 :
    ThetaLowerSegment 2989011200 2989142272 (149447505713131 / 50000) (59781649704427 / 20000) := by
  exact
    packedTile65536 2989011200 2989142272 14 6067 54671 31 _ _ (2181819 / 100000) (1090911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989142272 :
    ThetaLowerSegment 2989142272 2989273344 (59781649704427 / 20000)
      (298921247829527 / 100000) := by
  exact
    packedTile65536 2989142272 2989273344 14 5958 54673 31 _ _ (68182 / 3125) (2181827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989273344 :
    ThetaLowerSegment 2989273344 2989404416 (298921247829527 / 100000)
      (298934397706883 / 100000) := by
  exact
    packedTile65536 2989273344 2989404416 14 6027 54674 31 _ _ (545457 / 25000) (2181831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989404416 :
    ThetaLowerSegment 2989404416 2989535488 (298934397706883 / 100000)
      (149473682170201 / 50000) := by
  exact
    packedTile65536 2989404416 2989535488 14 5943 54675 31 _ _ (2181833 / 100000) (545459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989535488 :
    ThetaLowerSegment 2989535488 2989666560 (149473682170201 / 50000)
      (149480157862417 / 50000) := by
  exact
    packedTile65536 2989535488 2989666560 14 5936 54676 31 _ _ (2181837 / 100000) (27273 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989666560 :
    ThetaLowerSegment 2989666560 2989797632 (149480157862417 / 50000)
      (149486747022237 / 50000) := by
  exact
    packedTile65536 2989666560 2989797632 14 6040 54677 31 _ _ (2181841 / 100000) (545461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989797632 :
    ThetaLowerSegment 2989797632 2989928704 (149486747022237 / 50000) (74746634825427 / 25000) := by
  exact
    packedTile65536 2989797632 2989928704 14 5979 54679 31 _ _ (1090923 / 50000) (2181849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2989928704 :
    ThetaLowerSegment 2989928704 2990059776 (74746634825427 / 25000) (149499940657229 / 50000) := by
  exact
    packedTile65536 2989928704 2990059776 14 6115 54680 31 _ _ (43637 / 2000) (2181853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990059776 :
    ThetaLowerSegment 2990059776 2990190848 (149499940657229 / 50000) (29901288080059 / 10000) := by
  exact
    packedTile65536 2990059776 2990190848 14 5958 54681 31 _ _ (1090927 / 50000) (2181857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990190848 :
    ThetaLowerSegment 2990190848 2990321920 (29901288080059 / 10000) (59805214027649 / 20000) := by
  exact
    packedTile65536 2990190848 2990321920 14 6045 54682 31 _ _ (2181859 / 100000) (1090931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990321920 :
    ThetaLowerSegment 2990321920 2990452992 (59805214027649 / 20000) (14951952065689 / 5000) := by
  exact
    packedTile65536 2990321920 2990452992 14 5945 54683 31 _ _ (2181863 / 100000) (1090933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990452992 :
    ThetaLowerSegment 2990452992 2990584064 (14951952065689 / 5000) (74763066949399 / 25000) := by
  exact
    packedTile65536 2990452992 2990584064 14 6062 54685 31 _ _ (545467 / 25000) (2181871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990584064 :
    ThetaLowerSegment 2990584064 2990715136 (74763066949399 / 25000) (74766380122031 / 25000) := by
  exact
    packedTile65536 2990584064 2990715136 14 6074 54686 31 _ _ (136367 / 6250) (3491 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990715136 :
    ThetaLowerSegment 2990715136 2990846208 (74766380122031 / 25000) (37384825104343 / 12500) := by
  exact
    packedTile65536 2990715136 2990846208 14 5995 54687 31 _ _ (545469 / 25000) (2181879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990846208 :
    ThetaLowerSegment 2990846208 2990977280 (37384825104343 / 12500) (149545887516111 / 50000) := by
  exact
    packedTile65536 2990846208 2990977280 14 6038 54688 31 _ _ (2181881 / 100000) (545471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2990977280 :
    ThetaLowerSegment 2990977280 2991108352 (149545887516111 / 50000) (9347028845976 / 3125) := by
  exact
    packedTile65536 2990977280 2991108352 14 6026 54689 31 _ _ (436377 / 20000) (68184 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991108352 :
    ThetaLowerSegment 2991108352 2991239424 (9347028845976 / 3125) (59823592844357 / 20000) := by
  exact
    packedTile65536 2991108352 2991239424 14 5977 54691 31 _ _ (2181889 / 100000) (545473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991239424 :
    ThetaLowerSegment 2991239424 2991370496 (59823592844357 / 20000)
      (299131134133969 / 100000) := by
  exact
    packedTile65536 2991239424 2991370496 14 6036 54692 31 _ _ (1090947 / 50000) (2181897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991370496 :
    ThetaLowerSegment 2991370496 2991501568 (299131134133969 / 100000)
      (299144336798767 / 100000) := by
  exact
    packedTile65536 2991370496 2991501568 14 6051 54693 31 _ _ (1090949 / 50000) (2181901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991501568 :
    ThetaLowerSegment 2991501568 2991632640 (299144336798767 / 100000)
      (74789402328679 / 25000) := by
  exact
    packedTile65536 2991501568 2991632640 14 6083 54694 31 _ _ (2181903 / 100000) (1090953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991632640 :
    ThetaLowerSegment 2991632640 2991763712 (74789402328679 / 25000) (74792631551039 / 25000) := by
  exact
    packedTile65536 2991632640 2991763712 14 5920 54695 31 _ _ (2181907 / 100000) (218191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991763712 :
    ThetaLowerSegment 2991763712 2991894784 (74792631551039 / 25000) (9349482324676 / 3125) := by
  exact
    packedTile65536 2991763712 2991894784 14 5916 54697 31 _ _ (2181911 / 100000) (1090957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2991894784 :
    ThetaLowerSegment 2991894784 2992025856 (9349482324676 / 3125) (14959822257737 / 5000) := by
  exact
    packedTile65536 2991894784 2992025856 14 5963 54698 31 _ _ (545479 / 25000) (2181919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992025856 :
    ThetaLowerSegment 2992025856 2992156928 (14959822257737 / 5000) (14960492543561 / 5000) := by
  exact
    packedTile65536 2992025856 2992156928 14 6144 54699 31 _ _ (13637 / 625) (2181923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992156928 :
    ThetaLowerSegment 2992156928 2992288000 (14960492543561 / 5000) (29922299042357 / 10000) := by
  exact
    packedTile65536 2992156928 2992288000 14 6022 54700 31 _ _ (87277 / 4000) (272741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992288000 :
    ThetaLowerSegment 2992288000 2992419072 (29922299042357 / 10000)
      (299236302372399 / 100000) := by
  exact
    packedTile65536 2992288000 2992419072 14 6101 54701 31 _ _ (2181929 / 100000) (545483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992419072 :
    ThetaLowerSegment 2992419072 2992550144 (299236302372399 / 100000)
      (59849857847523 / 20000) := by
  exact
    packedTile65536 2992419072 2992550144 14 5952 54703 31 _ _ (2181933 / 100000) (136371 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992550144 :
    ThetaLowerSegment 2992550144 2992681216 (59849857847523 / 20000) (59852478355061 / 20000) := by
  exact
    packedTile65536 2992550144 2992681216 14 6005 54704 31 _ _ (1090969 / 50000) (2181941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992681216 :
    ThetaLowerSegment 2992681216 2992812288 (59852478355061 / 20000)
      (299275389603799 / 100000) := by
  exact
    packedTile65536 2992681216 2992812288 14 5957 54705 31 _ _ (1090971 / 50000) (436389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992812288 :
    ThetaLowerSegment 2992812288 2992943360 (299275389603799 / 100000)
      (299288500917313 / 100000) := by
  exact
    packedTile65536 2992812288 2992943360 14 6009 54706 31 _ _ (1090973 / 50000) (2181949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2992943360 :
    ThetaLowerSegment 2992943360 2993074432 (299288500917313 / 100000) (11972060388367 / 4000) := by
  exact
    packedTile65536 2992943360 2993074432 14 5962 54707 31 _ _ (2181951 / 100000) (1090977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993074432 :
    ThetaLowerSegment 2993074432 2993205504 (11972060388367 / 4000) (59862953453551 / 20000) := by
  exact
    packedTile65536 2993074432 2993205504 14 6076 54708 31 _ _ (436391 / 20000) (1090979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993205504 :
    ThetaLowerSegment 2993205504 2993336576 (59862953453551 / 20000) (59865591006799 / 20000) := by
  exact
    packedTile65536 2993205504 2993336576 14 6044 54710 31 _ _ (54549 / 2500) (2181963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993336576 :
    ThetaLowerSegment 2993336576 2993467648 (59865591006799 / 20000)
      (299340983541039 / 100000) := by
  exact
    packedTile65536 2993336576 2993467648 14 5971 54711 31 _ _ (545491 / 25000) (2181967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993467648 :
    ThetaLowerSegment 2993467648 2993598720 (299340983541039 / 100000)
      (299353953158831 / 100000) := by
  exact
    packedTile65536 2993467648 2993598720 14 5944 54712 31 _ _ (136373 / 6250) (2181971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993598720 :
    ThetaLowerSegment 2993598720 2993729792 (299353953158831 / 100000)
      (149683573774781 / 50000) := by
  exact
    packedTile65536 2993598720 2993729792 14 6047 54713 31 _ _ (2181973 / 100000) (272747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993729792 :
    ThetaLowerSegment 2993729792 2993860864 (149683573774781 / 50000)
      (299380176134229 / 100000) := by
  exact
    packedTile65536 2993729792 2993860864 14 5971 54714 31 _ _ (2181977 / 100000) (109099 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993860864 :
    ThetaLowerSegment 2993860864 2993991936 (299380176134229 / 100000)
      (59878664950347 / 20000) := by
  exact
    packedTile65536 2993860864 2993991936 14 6026 54716 31 _ _ (2181981 / 100000) (68187 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2993991936 :
    ThetaLowerSegment 2993991936 2994123008 (59878664950347 / 20000) (59881283333547 / 20000) := by
  exact
    packedTile65536 2993991936 2994123008 14 6000 54717 31 _ _ (1090993 / 50000) (2181989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994123008 :
    ThetaLowerSegment 2994123008 2994254080 (59881283333547 / 20000) (59883899103159 / 20000) := by
  exact
    packedTile65536 2994123008 2994254080 14 5994 54718 31 _ _ (218199 / 10000) (2181993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994254080 :
    ThetaLowerSegment 2994254080 2994385152 (59883899103159 / 20000) (29943257221183 / 10000) := by
  exact
    packedTile65536 2994254080 2994385152 14 5993 54719 31 _ _ (436399 / 20000) (1090999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994385152 :
    ThetaLowerSegment 2994385152 2994516224 (29943257221183 / 10000) (149722893198887 / 50000) := by
  exact
    packedTile65536 2994385152 2994516224 14 6056 54720 31 _ _ (2181999 / 100000) (1091001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994516224 :
    ThetaLowerSegment 2994516224 2994647296 (149722893198887 / 50000)
      (299458714765549 / 100000) := by
  exact
    packedTile65536 2994516224 2994647296 14 5925 54722 31 _ _ (2182003 / 100000) (1091003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994647296 :
    ThetaLowerSegment 2994647296 2994778368 (299458714765549 / 100000)
      (299471747899333 / 100000) := by
  exact
    packedTile65536 2994647296 2994778368 14 5973 54723 31 _ _ (272751 / 12500) (2182011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994778368 :
    ThetaLowerSegment 2994778368 2994909440 (299471747899333 / 100000)
      (299484835607309 / 100000) := by
  exact
    packedTile65536 2994778368 2994909440 14 5998 54724 31 _ _ (545503 / 25000) (436403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2994909440 :
    ThetaLowerSegment 2994909440 2995040512 (299484835607309 / 100000)
      (299497899337101 / 100000) := by
  exact
    packedTile65536 2994909440 2995040512 14 5987 54725 31 _ _ (68188 / 3125) (2182019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995040512 :
    ThetaLowerSegment 2995040512 2995171584 (299497899337101 / 100000)
      (149755501186603 / 50000) := by
  exact
    packedTile65536 2995040512 2995171584 14 6005 54726 31 _ _ (2182021 / 100000) (272753 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995171584 :
    ThetaLowerSegment 2995171584 2995302656 (149755501186603 / 50000)
      (299524135981681 / 100000) := by
  exact
    packedTile65536 2995171584 2995302656 14 6019 54728 31 _ _ (87281 / 4000) (545507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995302656 :
    ThetaLowerSegment 2995302656 2995433728 (299524135981681 / 100000)
      (299537269620251 / 100000) := by
  exact
    packedTile65536 2995302656 2995433728 14 6019 54729 31 _ _ (218203 / 10000) (2182033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995433728 :
    ThetaLowerSegment 2995433728 2995564800 (299537269620251 / 100000)
      (59910072801257 / 20000) := by
  exact
    packedTile65536 2995433728 2995564800 14 6001 54730 31 _ _ (1091017 / 50000) (2182037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995564800 :
    ThetaLowerSegment 2995564800 2995695872 (59910072801257 / 20000)
      (299563438777981 / 100000) := by
  exact
    packedTile65536 2995564800 2995695872 14 5992 54731 31 _ _ (1091019 / 50000) (2182041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995695872 :
    ThetaLowerSegment 2995695872 2995826944 (299563438777981 / 100000)
      (299576600861357 / 100000) := by
  exact
    packedTile65536 2995695872 2995826944 14 6032 54732 31 _ _ (2182043 / 100000) (1091023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995826944 :
    ThetaLowerSegment 2995826944 2995958016 (299576600861357 / 100000)
      (299589784789331 / 100000) := by
  exact
    packedTile65536 2995826944 2995958016 14 6042 54734 31 _ _ (2182047 / 100000) (43641 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2995958016 :
    ThetaLowerSegment 2995958016 2996089088 (299589784789331 / 100000)
      (299602942556861 / 100000) := by
  exact
    packedTile65536 2995958016 2996089088 14 6030 54735 31 _ _ (2182051 / 100000) (1091027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996089088 :
    ThetaLowerSegment 2996089088 2996220160 (299602942556861 / 100000)
      (59923199995993 / 20000) := by
  exact
    packedTile65536 2996089088 2996220160 14 5984 54736 31 _ _ (272757 / 12500) (2182059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996220160 :
    ThetaLowerSegment 2996220160 2996351232 (59923199995993 / 20000) (59925810612577 / 20000) := by
  exact
    packedTile65536 2996220160 2996351232 14 5982 54737 31 _ _ (109103 / 5000) (2182063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996351232 :
    ThetaLowerSegment 2996351232 2996482304 (59925810612577 / 20000) (1498209538039 / 500) := by
  exact
    packedTile65536 2996351232 2996482304 14 5891 54738 31 _ _ (436413 / 20000) (545517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996482304 :
    ThetaLowerSegment 2996482304 2996613376 (1498209538039 / 500) (299655168041113 / 100000) := by
  exact
    packedTile65536 2996482304 2996613376 14 6077 54740 31 _ _ (2182069 / 100000) (272759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996613376 :
    ThetaLowerSegment 2996613376 2996744448 (299655168041113 / 100000)
      (59933618928313 / 20000) := by
  exact
    packedTile65536 2996613376 2996744448 14 5924 54741 31 _ _ (2182073 / 100000) (545519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996744448 :
    ThetaLowerSegment 2996744448 2996875520 (59933618928313 / 20000)
      (299681075823587 / 100000) := by
  exact
    packedTile65536 2996744448 2996875520 14 5949 54742 31 _ _ (1091039 / 50000) (2182081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2996875520 :
    ThetaLowerSegment 2996875520 2997006592 (299681075823587 / 100000)
      (299694251234703 / 100000) := by
  exact
    packedTile65536 2996875520 2997006592 14 6038 54743 31 _ _ (1091041 / 50000) (436417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997006592 :
    ThetaLowerSegment 2997006592 2997137664 (299694251234703 / 100000)
      (59941484897577 / 20000) := by
  exact
    packedTile65536 2997006592 2997137664 14 6037 54744 31 _ _ (1091043 / 50000) (2182089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997137664 :
    ThetaLowerSegment 2997137664 2997268736 (59941484897577 / 20000)
      (299720469027883 / 100000) := by
  exact
    packedTile65536 2997137664 2997268736 14 5978 54746 31 _ _ (2182091 / 100000) (1091047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997268736 :
    ThetaLowerSegment 2997268736 2997399808 (299720469027883 / 100000)
      (299733487406653 / 100000) := by
  exact
    packedTile65536 2997268736 2997399808 14 5966 54747 31 _ _ (436419 / 20000) (1091049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997399808 :
    ThetaLowerSegment 2997399808 2997530880 (299733487406653 / 100000)
      (299746523272053 / 100000) := by
  exact
    packedTile65536 2997399808 2997530880 14 5974 54748 31 _ _ (21821 / 1000) (2182103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997530880 :
    ThetaLowerSegment 2997530880 2997661952 (299746523272053 / 100000)
      (299759552615037 / 100000) := by
  exact
    packedTile65536 2997530880 2997661952 14 5971 54749 31 _ _ (272763 / 12500) (2182107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997661952 :
    ThetaLowerSegment 2997661952 2997793024 (299759552615037 / 100000)
      (299772485969153 / 100000) := by
  exact
    packedTile65536 2997661952 2997793024 14 5927 54750 31 _ _ (545527 / 25000) (2182111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997793024 :
    ThetaLowerSegment 2997793024 2997924096 (299772485969153 / 100000)
      (149892807871537 / 50000) := by
  exact
    packedTile65536 2997793024 2997924096 14 6017 54752 31 _ _ (2182113 / 100000) (545529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2997924096 :
    ThetaLowerSegment 2997924096 2998055168 (149892807871537 / 50000) (74949695659263 / 25000) := by
  exact
    packedTile65536 2997924096 2998055168 14 6034 54753 31 _ _ (2182117 / 100000) (54553 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998055168 :
    ThetaLowerSegment 2998055168 2998186240 (74949695659263 / 25000) (37476483329321 / 12500) := by
  exact
    packedTile65536 2998055168 2998186240 14 5996 54754 31 _ _ (2182121 / 100000) (545531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998186240 :
    ThetaLowerSegment 2998186240 2998317312 (37476483329321 / 12500) (37478119923821 / 12500) := by
  exact
    packedTile65536 2998186240 2998317312 14 6000 54755 31 _ _ (1091063 / 50000) (2182129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998317312 :
    ThetaLowerSegment 2998317312 2998448384 (37478119923821 / 12500) (149918981351619 / 50000) := by
  exact
    packedTile65536 2998317312 2998448384 14 5959 54756 31 _ _ (218213 / 10000) (2182133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998448384 :
    ThetaLowerSegment 2998448384 2998579456 (149918981351619 / 50000)
      (299850992231323 / 100000) := by
  exact
    packedTile65536 2998448384 2998579456 14 5971 54758 31 _ _ (436427 / 20000) (1091069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998579456 :
    ThetaLowerSegment 2998579456 2998710528 (299850992231323 / 100000)
      (74966031631491 / 25000) := by
  exact
    packedTile65536 2998579456 2998710528 14 6019 54759 31 _ _ (2182139 / 100000) (1091071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998710528 :
    ThetaLowerSegment 2998710528 2998841600 (74966031631491 / 25000)
      (299877160466103 / 100000) := by
  exact
    packedTile65536 2998710528 2998841600 14 5973 54760 31 _ _ (2182143 / 100000) (1091073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998841600 :
    ThetaLowerSegment 2998841600 2998972672 (299877160466103 / 100000)
      (299890194436107 / 100000) := by
  exact
    packedTile65536 2998841600 2998972672 14 5973 54761 31 _ _ (545537 / 25000) (2182151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2998972672 :
    ThetaLowerSegment 2998972672 2999103744 (299890194436107 / 100000)
      (299903167329747 / 100000) := by
  exact
    packedTile65536 2998972672 2999103744 14 5945 54762 31 _ _ (272769 / 12500) (436431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999103744 :
    ThetaLowerSegment 2999103744 2999234816 (299903167329747 / 100000)
      (299916327912583 / 100000) := by
  exact
    packedTile65536 2999103744 2999234816 14 6031 54764 31 _ _ (545539 / 25000) (2182159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999234816 :
    ThetaLowerSegment 2999234816 2999365888 (299916327912583 / 100000)
      (59985841405361 / 20000) := by
  exact
    packedTile65536 2999234816 2999365888 14 5902 54765 31 _ _ (2182161 / 100000) (545541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999365888 :
    ThetaLowerSegment 2999365888 2999496960 (59985841405361 / 20000) (11997696190429 / 4000) := by
  exact
    packedTile65536 2999365888 2999496960 14 6048 54766 31 _ _ (436433 / 20000) (272771 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999496960 :
    ThetaLowerSegment 2999496960 2999628032 (11997696190429 / 4000) (59991111339863 / 20000) := by
  exact
    packedTile65536 2999496960 2999628032 14 6027 54767 31 _ _ (218217 / 10000) (2182173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999628032 :
    ThetaLowerSegment 2999628032 2999759104 (59991111339863 / 20000)
      (299968479533743 / 100000) := by
  exact
    packedTile65536 2999628032 2999759104 14 5922 54768 31 _ _ (1091087 / 50000) (2182177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999759104 :
    ThetaLowerSegment 2999759104 2999890176 (299968479533743 / 100000)
      (299981609698769 / 100000) := by
  exact
    packedTile65536 2999759104 2999890176 14 6017 54770 31 _ _ (1091089 / 50000) (2182181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2999890176 :
    ThetaLowerSegment 2999890176 3000021248 (299981609698769 / 100000)
      (299994855549579 / 100000) := by
  exact
    packedTile65536 2999890176 3000021248 14 6070 54771 31 _ _ (2182183 / 100000) (1091093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000021248 :
    ThetaLowerSegment 3000021248 3000152320 (299994855549579 / 100000)
      (150003957969387 / 50000) := by
  exact
    packedTile65536 3000021248 3000152320 14 5985 54772 31 _ _ (2182187 / 100000) (218219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000152320 :
    ThetaLowerSegment 3000152320 3000283392 (150003957969387 / 50000) (750052991883 / 250) := by
  exact
    packedTile65536 3000152320 3000283392 14 6086 54773 31 _ _ (2182191 / 100000) (1091097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000283392 :
    ThetaLowerSegment 3000283392 3000414464 (750052991883 / 250) (1875214584832 / 625) := by
  exact
    packedTile65536 3000283392 3000414464 14 6020 54774 31 _ _ (545549 / 25000) (2182199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000414464 :
    ThetaLowerSegment 3000414464 3000545536 (1875214584832 / 625) (7501185723883 / 2500) := by
  exact
    packedTile65536 3000414464 3000545536 14 6001 54776 31 _ _ (10911 / 500) (2182203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000545536 :
    ThetaLowerSegment 3000545536 3000676608 (7501185723883 / 2500) (37507555452497 / 12500) := by
  exact
    packedTile65536 3000545536 3000676608 14 5964 54777 31 _ _ (545551 / 25000) (2182207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000676608 :
    ThetaLowerSegment 3000676608 3000807680 (37507555452497 / 12500) (150036770619197 / 50000) := by
  exact
    packedTile65536 3000676608 3000807680 14 6002 54778 31 _ _ (2182209 / 100000) (545553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000807680 :
    ThetaLowerSegment 3000807680 3000938752 (150036770619197 / 50000)
      (150043317258197 / 50000) := by
  exact
    packedTile65536 3000807680 3000938752 14 6000 54779 31 _ _ (2182213 / 100000) (272777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3000938752 :
    ThetaLowerSegment 3000938752 3001069824 (150043317258197 / 50000)
      (150049968658661 / 50000) := by
  exact
    packedTile65536 3000938752 3001069824 14 6096 54780 31 _ _ (1091109 / 50000) (2182221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001069824 :
    ThetaLowerSegment 3001069824 3001200896 (150049968658661 / 50000) (18757058550861 / 6250) := by
  exact
    packedTile65536 3001069824 3001200896 14 5957 54782 31 _ _ (1091111 / 50000) (87289 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001200896 :
    ThetaLowerSegment 3001200896 3001331968 (18757058550861 / 6250) (9378933532797 / 3125) := by
  exact
    packedTile65536 3001200896 3001331968 14 5928 54783 31 _ _ (1091113 / 50000) (2182229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001331968 :
    ThetaLowerSegment 3001331968 3001463040 (9378933532797 / 3125) (12005562236279 / 4000) := by
  exact
    packedTile65536 3001331968 3001463040 14 6041 54784 31 _ _ (2182231 / 100000) (1091117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001463040 :
    ThetaLowerSegment 3001463040 3001594112 (12005562236279 / 4000) (2401217019957 / 800) := by
  exact
    packedTile65536 3001463040 3001594112 14 5990 54785 31 _ _ (436447 / 20000) (1091119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001594112 :
    ThetaLowerSegment 3001594112 3001725184 (2401217019957 / 800) (75041316688911 / 25000) := by
  exact
    packedTile65536 3001594112 3001725184 14 6021 54786 31 _ _ (2182239 / 100000) (1091121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001725184 :
    ThetaLowerSegment 3001725184 3001856256 (75041316688911 / 25000) (15008912991821 / 5000) := by
  exact
    packedTile65536 3001725184 3001856256 14 5954 54788 31 _ _ (545561 / 25000) (2182247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001856256 :
    ThetaLowerSegment 3001856256 3001987328 (15008912991821 / 5000) (75047860699147 / 25000) := by
  exact
    packedTile65536 3001856256 3001987328 14 6041 54789 31 _ _ (272781 / 12500) (2182251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3001987328 :
    ThetaLowerSegment 3001987328 3002118400 (75047860699147 / 25000)
      (300204617057949 / 100000) := by
  exact
    packedTile65536 3001987328 3002118400 14 6037 54790 31 _ _ (2182253 / 100000) (136391 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002118400 :
    ThetaLowerSegment 3002118400 3002249472 (300204617057949 / 100000)
      (300217701870921 / 100000) := by
  exact
    packedTile65536 3002118400 3002249472 14 5996 54791 31 _ _ (2182257 / 100000) (109113 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002249472 :
    ThetaLowerSegment 3002249472 3002380544 (300217701870921 / 100000)
      (60046156468671 / 20000) := by
  exact
    packedTile65536 3002249472 3002380544 14 5994 54792 31 _ _ (2182261 / 100000) (272783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002380544 :
    ThetaLowerSegment 3002380544 3002511616 (60046156468671 / 20000)
      (300243980688123 / 100000) := by
  exact
    packedTile65536 3002380544 3002511616 14 6048 54793 31 _ _ (1091133 / 50000) (2182269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002511616 :
    ThetaLowerSegment 3002511616 3002642688 (300243980688123 / 100000)
      (300257041574073 / 100000) := by
  exact
    packedTile65536 3002511616 3002642688 14 5985 54795 31 _ _ (218227 / 10000) (2182273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002642688 :
    ThetaLowerSegment 3002642688 3002773760 (300257041574073 / 100000)
      (300270146129443 / 100000) := by
  exact
    packedTile65536 3002642688 3002773760 14 6005 54796 31 _ _ (1091137 / 50000) (2182277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002773760 :
    ThetaLowerSegment 3002773760 3002904832 (300270146129443 / 100000)
      (300283209251537 / 100000) := by
  exact
    packedTile65536 3002773760 3002904832 14 5986 54797 31 _ _ (2182279 / 100000) (1091141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3002904832 :
    ThetaLowerSegment 3002904832 3003035904 (300283209251537 / 100000)
      (300296202564519 / 100000) := by
  exact
    packedTile65536 3002904832 3003035904 14 5954 54798 31 _ _ (2182283 / 100000) (1091143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003035904 :
    ThetaLowerSegment 3003035904 3003166976 (300296202564519 / 100000)
      (300309278828223 / 100000) := by
  exact
    packedTile65536 3003035904 3003166976 14 5992 54799 31 _ _ (2182287 / 100000) (218229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003166976 :
    ThetaLowerSegment 3003166976 3003298048 (300309278828223 / 100000)
      (60064446582707 / 20000) := by
  exact
    packedTile65536 3003166976 3003298048 14 5936 54801 31 _ _ (545573 / 25000) (436459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003298048 :
    ThetaLowerSegment 3003298048 3003429120 (60064446582707 / 20000)
      (300335383429231 / 100000) := by
  exact
    packedTile65536 3003298048 3003429120 14 6026 54802 31 _ _ (272787 / 12500) (2182299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003429120 :
    ThetaLowerSegment 3003429120 3003560192 (300335383429231 / 100000)
      (300348416130803 / 100000) := by
  exact
    packedTile65536 3003429120 3003560192 14 5972 54803 31 _ _ (2182301 / 100000) (68197 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003560192 :
    ThetaLowerSegment 3003560192 3003691264 (300348416130803 / 100000)
      (150180723336979 / 50000) := by
  exact
    packedTile65536 3003560192 3003691264 14 5971 54804 31 _ _ (436461 / 20000) (545577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003691264 :
    ThetaLowerSegment 3003691264 3003822336 (150180723336979 / 50000) (7509366677547 / 2500) := by
  exact
    packedTile65536 3003691264 3003822336 14 6058 54805 31 _ _ (2182309 / 100000) (272789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003822336 :
    ThetaLowerSegment 3003822336 3003953408 (7509366677547 / 2500) (6007755437949 / 2000) := by
  exact
    packedTile65536 3003822336 3003953408 14 6005 54807 31 _ _ (1091157 / 50000) (2182317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3003953408 :
    ThetaLowerSegment 3003953408 3004084480 (6007755437949 / 2000) (37550134686287 / 12500) := by
  exact
    packedTile65536 3003953408 3004084480 14 6097 54808 31 _ _ (1091159 / 50000) (2182321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004084480 :
    ThetaLowerSegment 3004084480 3004215552 (37550134686287 / 12500) (150206997327107 / 50000) := by
  exact
    packedTile65536 3004084480 3004215552 14 5919 54809 31 _ _ (1091161 / 50000) (87293 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004215552 :
    ThetaLowerSegment 3004215552 3004346624 (150206997327107 / 50000) (12017082933597 / 4000) := by
  exact
    packedTile65536 3004215552 3004346624 14 5993 54810 31 _ _ (2182327 / 100000) (218233 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004346624 :
    ThetaLowerSegment 3004346624 3004477696 (12017082933597 / 4000) (300440162961263 / 100000) := by
  exact
    packedTile65536 3004346624 3004477696 14 5998 54811 31 _ _ (2182331 / 100000) (1091167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004477696 :
    ThetaLowerSegment 3004477696 3004608768 (300440162961263 / 100000)
      (300453056196443 / 100000) := by
  exact
    packedTile65536 3004477696 3004608768 14 5908 54813 31 _ _ (436467 / 20000) (1091169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004608768 :
    ThetaLowerSegment 3004608768 3004739840 (300453056196443 / 100000)
      (300466370652783 / 100000) := by
  exact
    packedTile65536 3004608768 3004739840 14 6101 54814 31 _ _ (109117 / 5000) (2182343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004739840 :
    ThetaLowerSegment 3004739840 3004870912 (300466370652783 / 100000)
      (300479615298519 / 100000) := by
  exact
    packedTile65536 3004739840 3004870912 14 6069 54815 31 _ _ (272793 / 12500) (2182347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3004870912 :
    ThetaLowerSegment 3004870912 3005001984 (300479615298519 / 100000)
      (75123256458281 / 25000) := by
  exact
    packedTile65536 3004870912 3005001984 14 6145 54816 31 _ _ (2182349 / 100000) (136397 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005001984 :
    ThetaLowerSegment 3005001984 3005133056 (75123256458281 / 25000) (60101218316107 / 20000) := by
  exact
    packedTile65536 3005001984 3005133056 14 5987 54817 31 _ _ (2182353 / 100000) (545589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005133056 :
    ThetaLowerSegment 3005133056 3005264128 (60101218316107 / 20000) (37564906126361 / 12500) := by
  exact
    packedTile65536 3005133056 3005264128 14 6029 54819 31 _ _ (2182357 / 100000) (54559 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005264128 :
    ThetaLowerSegment 3005264128 3005395200 (37564906126361 / 12500) (7513309452517 / 2500) := by
  exact
    packedTile65536 3005264128 3005395200 14 6016 54820 31 _ _ (1091181 / 50000) (436473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005395200 :
    ThetaLowerSegment 3005395200 3005526272 (7513309452517 / 2500) (75136353888791 / 25000) := by
  exact
    packedTile65536 3005395200 3005526272 14 5974 54821 31 _ _ (1091183 / 50000) (2182369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005526272 :
    ThetaLowerSegment 3005526272 3005657344 (75136353888791 / 25000) (150279168683967 / 50000) := by
  exact
    packedTile65536 3005526272 3005657344 14 5921 54822 31 _ _ (218237 / 10000) (2182373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005657344 :
    ThetaLowerSegment 3005657344 3005788416 (150279168683967 / 50000) (75142920102171 / 25000) := by
  exact
    packedTile65536 3005657344 3005788416 14 6114 54823 31 _ _ (17459 / 800) (1091189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005788416 :
    ThetaLowerSegment 3005788416 3005919488 (75142920102171 / 25000)
      (300584676475629 / 100000) := by
  exact
    packedTile65536 3005788416 3005919488 14 5955 54825 31 _ _ (2182379 / 100000) (1091191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3005919488 :
    ThetaLowerSegment 3005919488 3006050560 (300584676475629 / 100000) (6011950483287 / 2000) := by
  exact
    packedTile65536 3005919488 3006050560 14 5887 54826 31 _ _ (2182383 / 100000) (1091193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006050560 :
    ThetaLowerSegment 3006050560 3006181632 (6011950483287 / 2000) (30061068396399 / 10000) := by
  exact
    packedTile65536 3006050560 3006181632 14 6030 54827 31 _ _ (545597 / 25000) (2182391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006181632 :
    ThetaLowerSegment 3006181632 3006312704 (30061068396399 / 10000) (30062375649207 / 10000) := by
  exact
    packedTile65536 3006181632 3006312704 14 5990 54828 31 _ _ (272799 / 12500) (436479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006312704 :
    ThetaLowerSegment 3006312704 3006443776 (30062375649207 / 10000)
      (300636979635493 / 100000) := by
  exact
    packedTile65536 3006312704 3006443776 14 6059 54829 31 _ _ (2182397 / 100000) (2728 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006443776 :
    ThetaLowerSegment 3006443776 3006574848 (300636979635493 / 100000)
      (300650017299067 / 100000) := by
  exact
    packedTile65536 3006443776 3006574848 14 5974 54831 31 _ _ (2182401 / 100000) (545601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006574848 :
    ThetaLowerSegment 3006574848 3006705920 (300650017299067 / 100000)
      (150331624610291 / 50000) := by
  exact
    packedTile65536 3006574848 3006705920 14 6063 54832 31 _ _ (436481 / 20000) (272801 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006705920 :
    ThetaLowerSegment 3006705920 3006836992 (150331624610291 / 50000)
      (150338053990151 / 50000) := by
  exact
    packedTile65536 3006705920 3006836992 14 5892 54833 31 _ _ (218241 / 10000) (2182413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006836992 :
    ThetaLowerSegment 3006836992 3006968064 (150338053990151 / 50000)
      (150344599049737 / 50000) := by
  exact
    packedTile65536 3006836992 3006968064 14 5998 54834 31 _ _ (1091207 / 50000) (2182417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3006968064 :
    ThetaLowerSegment 3006968064 3007099136 (150344599049737 / 50000)
      (150351120114721 / 50000) := by
  exact
    packedTile65536 3006968064 3007099136 14 5976 54835 31 _ _ (1091209 / 50000) (2182421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007099136 :
    ThetaLowerSegment 3007099136 3007230208 (150351120114721 / 50000)
      (150357610640723 / 50000) := by
  exact
    packedTile65536 3007099136 3007230208 14 5948 54837 31 _ _ (2182423 / 100000) (1091213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007230208 :
    ThetaLowerSegment 3007230208 3007361280 (150357610640723 / 50000) (75182093146637 / 25000) := by
  exact
    packedTile65536 3007230208 3007361280 14 6026 54838 31 _ _ (2182427 / 100000) (218243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007361280 :
    ThetaLowerSegment 3007361280 3007492352 (75182093146637 / 25000) (75185388617447 / 25000) := by
  exact
    packedTile65536 3007361280 3007492352 14 6040 54839 31 _ _ (2182431 / 100000) (1091217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007492352 :
    ThetaLowerSegment 3007492352 3007623424 (75185388617447 / 25000) (15037729398879 / 5000) := by
  exact
    packedTile65536 3007492352 3007623424 14 5972 54840 31 _ _ (545609 / 25000) (2182439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007623424 :
    ThetaLowerSegment 3007623424 3007754496 (15037729398879 / 5000) (15038389805223 / 5000) := by
  exact
    packedTile65536 3007623424 3007754496 14 6052 54841 31 _ _ (54561 / 2500) (2182443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007754496 :
    ThetaLowerSegment 3007754496 3007885568 (15038389805223 / 5000) (37597597432977 / 12500) := by
  exact
    packedTile65536 3007754496 3007885568 14 5949 54842 31 _ _ (545611 / 25000) (2182447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3007885568 :
    ThetaLowerSegment 3007885568 3008016640 (37597597432977 / 12500) (150397039654011 / 50000) := by
  exact
    packedTile65536 3007885568 3008016640 14 6094 54844 31 _ _ (2182449 / 100000) (545613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008016640 :
    ThetaLowerSegment 3008016640 3008147712 (150397039654011 / 50000)
      (300807224222441 / 100000) := by
  exact
    packedTile65536 3008016640 3008147712 14 6023 54845 31 _ _ (2182453 / 100000) (272807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008147712 :
    ThetaLowerSegment 3008147712 3008278784 (300807224222441 / 100000)
      (300820177110671 / 100000) := by
  exact
    packedTile65536 3008147712 3008278784 14 5935 54846 31 _ _ (1091229 / 50000) (2182461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008278784 :
    ThetaLowerSegment 3008278784 3008409856 (300820177110671 / 100000)
      (60166631242437 / 20000) := by
  exact
    packedTile65536 3008278784 3008409856 14 5947 54847 31 _ _ (1091231 / 50000) (436493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008409856 :
    ThetaLowerSegment 3008409856 3008540928 (60166631242437 / 20000)
      (300846275015311 / 100000) := by
  exact
    packedTile65536 3008409856 3008540928 14 6011 54848 31 _ _ (1091233 / 50000) (2182469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008540928 :
    ThetaLowerSegment 3008540928 3008672000 (300846275015311 / 100000) (7521479826529 / 2500) := by
  exact
    packedTile65536 3008540928 3008672000 14 5919 54850 31 _ _ (2182471 / 100000) (1091237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008672000 :
    ThetaLowerSegment 3008672000 3008803072 (7521479826529 / 2500) (30087213513791 / 10000) := by
  exact
    packedTile65536 3008672000 3008803072 14 5930 54851 31 _ _ (87299 / 4000) (1091239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008803072 :
    ThetaLowerSegment 3008803072 3008934144 (30087213513791 / 10000)
      (300885315128591 / 100000) := by
  exact
    packedTile65536 3008803072 3008934144 14 6039 54852 31 _ _ (2182479 / 100000) (1091241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3008934144 :
    ThetaLowerSegment 3008934144 3009065216 (300885315128591 / 100000)
      (300898418762527 / 100000) := by
  exact
    packedTile65536 3008934144 3009065216 14 6004 54853 31 _ _ (545621 / 25000) (2182487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009065216 :
    ThetaLowerSegment 3009065216 3009196288 (300898418762527 / 100000)
      (60182314087043 / 20000) := by
  exact
    packedTile65536 3009065216 3009196288 14 6026 54854 31 _ _ (272811 / 12500) (2182491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009196288 :
    ThetaLowerSegment 3009196288 3009327360 (60182314087043 / 20000)
      (300924702489579 / 100000) := by
  exact
    packedTile65536 3009196288 3009327360 14 6017 54856 31 _ _ (545623 / 25000) (436499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009327360 :
    ThetaLowerSegment 3009327360 3009458432 (300924702489579 / 100000)
      (150468875819571 / 50000) := by
  exact
    packedTile65536 3009327360 3009458432 14 5979 54857 31 _ _ (2182497 / 100000) (873 / 40)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009458432 :
    ThetaLowerSegment 3009458432 3009589504 (150468875819571 / 50000) (12038036746707 / 4000) := by
  exact
    packedTile65536 3009458432 3009589504 14 6033 54858 31 _ _ (2182501 / 100000) (272813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009589504 :
    ThetaLowerSegment 3009589504 3009720576 (12038036746707 / 4000) (60192773930469 / 20000) := by
  exact
    packedTile65536 3009589504 3009720576 14 5934 54859 31 _ _ (436501 / 20000) (545627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009720576 :
    ThetaLowerSegment 3009720576 3009851648 (60192773930469 / 20000) (60195410402549 / 20000) := by
  exact
    packedTile65536 3009720576 3009851648 14 6040 54860 31 _ _ (218251 / 10000) (2182513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009851648 :
    ThetaLowerSegment 3009851648 3009982720 (60195410402549 / 20000) (60198057792031 / 20000) := by
  exact
    packedTile65536 3009851648 3009982720 14 6065 54862 31 _ _ (1091257 / 50000) (2182517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3009982720 :
    ThetaLowerSegment 3009982720 3010113792 (60198057792031 / 20000) (12040137981989 / 4000) := by
  exact
    packedTile65536 3009982720 3010113792 14 6030 54863 31 _ _ (2182519 / 100000) (1091261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010113792 :
    ThetaLowerSegment 3010113792 3010244864 (12040137981989 / 4000) (75254082154487 / 25000) := by
  exact
    packedTile65536 3010113792 3010244864 14 5901 54864 31 _ _ (2182523 / 100000) (1091263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010244864 :
    ThetaLowerSegment 3010244864 3010375936 (75254082154487 / 25000) (75257351579933 / 25000) := by
  exact
    packedTile65536 3010244864 3010375936 14 5992 54865 31 _ _ (2182527 / 100000) (218253 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010375936 :
    ThetaLowerSegment 3010375936 3010507008 (75257351579933 / 25000) (37630333695837 / 12500) := by
  exact
    packedTile65536 3010375936 3010507008 14 6077 54866 31 _ _ (545633 / 25000) (436507 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010507008 :
    ThetaLowerSegment 3010507008 3010638080 (37630333695837 / 12500) (37631978782347 / 12500) := by
  exact
    packedTile65536 3010507008 3010638080 14 6030 54868 31 _ _ (272817 / 12500) (2182539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010638080 :
    ThetaLowerSegment 3010638080 3010769152 (37631978782347 / 12500) (37633640786557 / 12500) := by
  exact
    packedTile65536 3010638080 3010769152 14 6092 54869 31 _ _ (109127 / 5000) (2182543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010769152 :
    ThetaLowerSegment 3010769152 3010900224 (37633640786557 / 12500)
      (301082070966851 / 100000) := by
  exact
    packedTile65536 3010769152 3010900224 14 5931 54870 31 _ _ (436509 / 20000) (545637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3010900224 :
    ThetaLowerSegment 3010900224 3011031296 (301082070966851 / 100000)
      (301095240467517 / 100000) := by
  exact
    packedTile65536 3010900224 3011031296 14 6034 54871 31 _ _ (2182549 / 100000) (272819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011031296 :
    ThetaLowerSegment 3011031296 3011162368 (301095240467517 / 100000)
      (301108396897001 / 100000) := by
  exact
    packedTile65536 3011031296 3011162368 14 6028 54872 31 _ _ (2182553 / 100000) (545639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011162368 :
    ThetaLowerSegment 3011162368 3011293440 (301108396897001 / 100000) (2408972426853 / 800) := by
  exact
    packedTile65536 3011162368 3011293440 14 6028 54874 31 _ _ (1091279 / 50000) (2182561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011293440 :
    ThetaLowerSegment 3011293440 3011424512 (2408972426853 / 800) (301134825516147 / 100000) := by
  exact
    packedTile65536 3011293440 3011424512 14 6081 54875 31 _ _ (1091281 / 50000) (436513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011424512 :
    ThetaLowerSegment 3011424512 3011555584 (301134825516147 / 100000)
      (301147859800299 / 100000) := by
  exact
    packedTile65536 3011424512 3011555584 14 5972 54876 31 _ _ (1091283 / 50000) (2182569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011555584 :
    ThetaLowerSegment 3011555584 3011686656 (301147859800299 / 100000)
      (60232211124913 / 20000) := by
  exact
    packedTile65536 3011555584 3011686656 14 6046 54877 31 _ _ (2182571 / 100000) (1091287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011686656 :
    ThetaLowerSegment 3011686656 3011817728 (60232211124913 / 20000) (15058704170737 / 5000) := by
  exact
    packedTile65536 3011686656 3011817728 14 5969 54878 31 _ _ (87303 / 4000) (1091289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011817728 :
    ThetaLowerSegment 3011817728 3011948800 (15058704170737 / 5000) (301187185436477 / 100000) := by
  exact
    packedTile65536 3011817728 3011948800 14 6003 54880 31 _ _ (2182579 / 100000) (1091291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3011948800 :
    ThetaLowerSegment 3011948800 3012079872 (301187185436477 / 100000)
      (301200311496653 / 100000) := by
  exact
    packedTile65536 3011948800 3012079872 14 6014 54881 31 _ _ (272823 / 12500) (2182587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012079872 :
    ThetaLowerSegment 3012079872 3012210944 (301200311496653 / 100000)
      (301213431033121 / 100000) := by
  exact
    packedTile65536 3012079872 3012210944 14 6011 54882 31 _ _ (545647 / 25000) (2182591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012210944 :
    ThetaLowerSegment 3012210944 3012342016 (301213431033121 / 100000) (1882665559294 / 625) := by
  exact
    packedTile65536 3012210944 3012342016 14 5983 54883 31 _ _ (2182593 / 100000) (545649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012342016 :
    ThetaLowerSegment 3012342016 3012473088 (1882665559294 / 625) (60247927926793 / 20000) := by
  exact
    packedTile65536 3012342016 3012473088 14 6025 54884 31 _ _ (2182597 / 100000) (10913 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012473088 :
    ThetaLowerSegment 3012473088 3012604160 (60247927926793 / 20000) (150626429824111 / 50000) := by
  exact
    packedTile65536 3012473088 3012604160 14 6057 54886 31 _ _ (2182601 / 100000) (545651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012604160 :
    ThetaLowerSegment 3012604160 3012735232 (150626429824111 / 50000)
      (150632973276899 / 50000) := by
  exact
    packedTile65536 3012604160 3012735232 14 5996 54887 31 _ _ (1091303 / 50000) (2182609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012735232 :
    ThetaLowerSegment 3012735232 3012866304 (150632973276899 / 50000)
      (150639503646019 / 50000) := by
  exact
    packedTile65536 3012735232 3012866304 14 5984 54888 31 _ _ (218261 / 10000) (2182613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012866304 :
    ThetaLowerSegment 3012866304 3012997376 (150639503646019 / 50000)
      (150646108235983 / 50000) := by
  exact
    packedTile65536 3012866304 3012997376 14 6052 54889 31 _ _ (1091307 / 50000) (2182617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3012997376 :
    ThetaLowerSegment 3012997376 3013128448 (150646108235983 / 50000)
      (301305419134297 / 100000) := by
  exact
    packedTile65536 3012997376 3013128448 14 6049 54890 31 _ _ (2182619 / 100000) (1091311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013128448 :
    ThetaLowerSegment 3013128448 3013259520 (301305419134297 / 100000)
      (60263701228361 / 20000) := by
  exact
    packedTile65536 3013128448 3013259520 14 5996 54891 31 _ _ (2182623 / 100000) (1091313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013259520 :
    ThetaLowerSegment 3013259520 3013390592 (60263701228361 / 20000)
      (301331501502963 / 100000) := by
  exact
    packedTile65536 3013259520 3013390592 14 5954 54893 31 _ _ (2182627 / 100000) (218263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013390592 :
    ThetaLowerSegment 3013390592 3013521664 (301331501502963 / 100000)
      (301344595112331 / 100000) := by
  exact
    packedTile65536 3013390592 3013521664 14 5999 54894 31 _ _ (272829 / 12500) (436527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013521664 :
    ThetaLowerSegment 3013521664 3013652736 (301344595112331 / 100000)
      (301357756407411 / 100000) := by
  exact
    packedTile65536 3013521664 3013652736 14 6030 54895 31 _ _ (545659 / 25000) (2182639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013652736 :
    ThetaLowerSegment 3013652736 3013783808 (301357756407411 / 100000)
      (301370902448131 / 100000) := by
  exact
    packedTile65536 3013652736 3013783808 14 6023 54896 31 _ _ (27283 / 1250) (2182643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013783808 :
    ThetaLowerSegment 3013783808 3013914880 (301370902448131 / 100000)
      (301384002683421 / 100000) := by
  exact
    packedTile65536 3013783808 3013914880 14 6002 54897 31 _ _ (436529 / 20000) (272831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3013914880 :
    ThetaLowerSegment 3013914880 3014045952 (301384002683421 / 100000)
      (301397033097951 / 100000) := by
  exact
    packedTile65536 3013914880 3014045952 14 5970 54899 31 _ _ (2182649 / 100000) (545663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014045952 :
    ThetaLowerSegment 3014045952 3014177024 (301397033097951 / 100000)
      (301410281801661 / 100000) := by
  exact
    packedTile65536 3014045952 3014177024 14 6070 54900 31 _ _ (2182653 / 100000) (68208 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014177024 :
    ThetaLowerSegment 3014177024 3014308096 (301410281801661 / 100000)
      (301423419220163 / 100000) := by
  exact
    packedTile65536 3014177024 3014308096 14 6019 54901 31 _ _ (1091329 / 50000) (2182661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014308096 :
    ThetaLowerSegment 3014308096 3014439168 (301423419220163 / 100000)
      (301436491182881 / 100000) := by
  exact
    packedTile65536 3014308096 3014439168 14 5989 54902 31 _ _ (1091331 / 50000) (436533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014439168 :
    ThetaLowerSegment 3014439168 3014570240 (301436491182881 / 100000)
      (301449580630883 / 100000) := by
  exact
    packedTile65536 3014439168 3014570240 14 5997 54903 31 _ _ (1091333 / 50000) (2182669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014570240 :
    ThetaLowerSegment 3014570240 3014701312 (301449580630883 / 100000)
      (150731396169223 / 50000) := by
  exact
    packedTile65536 3014570240 3014701312 14 6053 54905 31 _ _ (2182671 / 100000) (1091337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014701312 :
    ThetaLowerSegment 3014701312 3014832384 (150731396169223 / 50000)
      (301475842552271 / 100000) := by
  exact
    packedTile65536 3014701312 3014832384 14 5979 54906 31 _ _ (87307 / 4000) (1091339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014832384 :
    ThetaLowerSegment 3014832384 3014963456 (301475842552271 / 100000)
      (301488975737831 / 100000) := by
  exact
    packedTile65536 3014832384 3014963456 14 6017 54907 31 _ _ (54567 / 2500) (2182683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3014963456 :
    ThetaLowerSegment 3014963456 3015094528 (301488975737831 / 100000)
      (60300427901007 / 20000) := by
  exact
    packedTile65536 3014963456 3015094528 14 6031 54908 31 _ _ (545671 / 25000) (2182687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015094528 :
    ThetaLowerSegment 3015094528 3015225600 (60300427901007 / 20000)
      (301515296748299 / 100000) := by
  exact
    packedTile65536 3015094528 3015225600 14 6028 54909 31 _ _ (68209 / 3125) (2182691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015225600 :
    ThetaLowerSegment 3015225600 3015356672 (301515296748299 / 100000) (18845513779597 / 6250) := by
  exact
    packedTile65536 3015225600 3015356672 14 5921 54911 31 _ _ (2182693 / 100000) (272837 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015356672 :
    ThetaLowerSegment 3015356672 3015487744 (18845513779597 / 6250) (7538534226007 / 2500) := by
  exact
    packedTile65536 3015356672 3015487744 14 6024 54912 31 _ _ (2182697 / 100000) (21827 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015487744 :
    ThetaLowerSegment 3015487744 3015618816 (7538534226007 / 2500) (301554524179207 / 100000) := by
  exact
    packedTile65536 3015487744 3015618816 14 6027 54913 31 _ _ (2182701 / 100000) (136419 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015618816 :
    ThetaLowerSegment 3015618816 3015749888 (301554524179207 / 100000)
      (301567611684383 / 100000) := by
  exact
    packedTile65536 3015618816 3015749888 14 5996 54914 31 _ _ (1091353 / 50000) (2182709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015749888 :
    ThetaLowerSegment 3015749888 3015880960 (301567611684383 / 100000)
      (301580653376633 / 100000) := by
  exact
    packedTile65536 3015749888 3015880960 14 5975 54915 31 _ _ (218271 / 10000) (2182713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3015880960 :
    ThetaLowerSegment 3015880960 3016012032 (301580653376633 / 100000)
      (301593732198921 / 100000) := by
  exact
    packedTile65536 3015880960 3016012032 14 5992 54917 31 _ _ (1091357 / 50000) (2182717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016012032 :
    ThetaLowerSegment 3016012032 3016143104 (301593732198921 / 100000)
      (150803465550357 / 50000) := by
  exact
    packedTile65536 3016012032 3016143104 14 6047 54918 31 _ _ (2182719 / 100000) (1091361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016143104 :
    ThetaLowerSegment 3016143104 3016274176 (150803465550357 / 50000) (75404988306533 / 25000) := by
  exact
    packedTile65536 3016143104 3016274176 14 5966 54919 31 _ _ (2182723 / 100000) (1091363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016274176 :
    ThetaLowerSegment 3016274176 3016405248 (75404988306533 / 25000) (603266029329 / 200) := by
  exact
    packedTile65536 3016274176 3016405248 14 5984 54920 31 _ _ (2182727 / 100000) (218273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016405248 :
    ThetaLowerSegment 3016405248 3016536320 (603266029329 / 200) (15082309918289 / 5000) := by
  exact
    packedTile65536 3016405248 3016536320 14 6040 54921 31 _ _ (545683 / 25000) (436547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016536320 :
    ThetaLowerSegment 3016536320 3016667392 (15082309918289 / 5000) (75414796956929 / 25000) := by
  exact
    packedTile65536 3016536320 3016667392 14 5951 54923 31 _ _ (136421 / 6250) (2182739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016667392 :
    ThetaLowerSegment 3016667392 3016798464 (75414796956929 / 25000) (75418093985699 / 25000) := by
  exact
    packedTile65536 3016667392 3016798464 14 6042 54924 31 _ _ (109137 / 5000) (2182743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016798464 :
    ThetaLowerSegment 3016798464 3016929536 (75418093985699 / 25000)
      (301685448402601 / 100000) := by
  exact
    packedTile65536 3016798464 3016929536 14 5989 54925 31 _ _ (436549 / 20000) (545687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3016929536 :
    ThetaLowerSegment 3016929536 3017060608 (301685448402601 / 100000) (12067944065923 / 4000) := by
  exact
    packedTile65536 3016929536 3017060608 14 6026 54926 31 _ _ (2182749 / 100000) (68211 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017060608 :
    ThetaLowerSegment 3017060608 3017191680 (12067944065923 / 4000) (150855834895143 / 50000) := by
  exact
    packedTile65536 3017060608 3017191680 14 5987 54927 31 _ _ (2182753 / 100000) (545689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017191680 :
    ThetaLowerSegment 3017191680 3017322752 (150855834895143 / 50000) (75431157206133 / 25000) := by
  exact
    packedTile65536 3017191680 3017322752 14 5937 54928 31 _ _ (1091379 / 50000) (2182761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017322752 :
    ThetaLowerSegment 3017322752 3017339136 (75431157206133 / 25000) (150863086018633 / 50000) := by
  exact
    packedTile65536 3017322752 3017339136 11 707 54930 31 _ _ (1091381 / 50000) (436553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017339136 :
    ThetaLowerSegment 3017339136 3017341184 (150863086018633 / 50000)
      (301726405592907 / 100000) := by
  exact
    packedTile65536 3017339136 3017341184 8 107 54930 31 _ _ (2182763 / 100000) (1091383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2985341184_3017341184 :
    ThetaLowerSegment 2985341184 3017341184 (298527603773077 / 100000)
      (301726405592907 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2985341184 cell2985472256)
                  (ThetaLowerSegment.join cell2985603328 cell2985734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2985865472 cell2985996544)
                  (ThetaLowerSegment.join cell2986127616 cell2986258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2986389760 cell2986520832)
                  (ThetaLowerSegment.join cell2986651904 cell2986782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2986914048 cell2987045120)
                  (ThetaLowerSegment.join cell2987176192 cell2987307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2987438336 cell2987569408)
                  (ThetaLowerSegment.join cell2987700480 cell2987831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2987962624 cell2988093696)
                  (ThetaLowerSegment.join cell2988224768 cell2988355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2988486912 cell2988617984)
                  (ThetaLowerSegment.join cell2988749056 cell2988880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2989011200 cell2989142272)
                  (ThetaLowerSegment.join cell2989273344 cell2989404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2989535488 cell2989666560)
                  (ThetaLowerSegment.join cell2989797632 cell2989928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2990059776 cell2990190848)
                  (ThetaLowerSegment.join cell2990321920 cell2990452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2990584064 cell2990715136)
                  (ThetaLowerSegment.join cell2990846208 cell2990977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2991108352 cell2991239424)
                  (ThetaLowerSegment.join cell2991370496 cell2991501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2991632640 cell2991763712)
                  (ThetaLowerSegment.join cell2991894784 cell2992025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2992156928 cell2992288000)
                  (ThetaLowerSegment.join cell2992419072 cell2992550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2992681216 cell2992812288)
                  (ThetaLowerSegment.join cell2992943360 cell2993074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2993205504 cell2993336576)
                  (ThetaLowerSegment.join cell2993467648 cell2993598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2993729792 cell2993860864)
                  (ThetaLowerSegment.join cell2993991936 cell2994123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2994254080 cell2994385152)
                  (ThetaLowerSegment.join cell2994516224 cell2994647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2994778368 cell2994909440)
                  (ThetaLowerSegment.join cell2995040512 cell2995171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2995302656 cell2995433728)
                  (ThetaLowerSegment.join cell2995564800 cell2995695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2995826944 cell2995958016)
                  (ThetaLowerSegment.join cell2996089088 cell2996220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2996351232 cell2996482304)
                  (ThetaLowerSegment.join cell2996613376 cell2996744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2996875520 cell2997006592)
                  (ThetaLowerSegment.join cell2997137664 cell2997268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2997399808 cell2997530880)
                  (ThetaLowerSegment.join cell2997661952 cell2997793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2997924096 cell2998055168)
                  (ThetaLowerSegment.join cell2998186240 cell2998317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2998448384 cell2998579456)
                  (ThetaLowerSegment.join cell2998710528 cell2998841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2998972672 cell2999103744)
                  (ThetaLowerSegment.join cell2999234816 cell2999365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2999496960 cell2999628032)
                  (ThetaLowerSegment.join cell2999759104 cell2999890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3000021248 cell3000152320)
                  (ThetaLowerSegment.join cell3000283392 cell3000414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3000545536 cell3000676608)
                  (ThetaLowerSegment.join cell3000807680 cell3000938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3001069824 cell3001200896)
                  (ThetaLowerSegment.join cell3001331968 cell3001463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3001594112 cell3001725184)
                  (ThetaLowerSegment.join cell3001856256 cell3001987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3002118400 cell3002249472)
                  (ThetaLowerSegment.join cell3002380544 cell3002511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3002642688 cell3002773760)
                  (ThetaLowerSegment.join cell3002904832 cell3003035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3003166976 cell3003298048)
                  (ThetaLowerSegment.join cell3003429120 cell3003560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3003691264 cell3003822336)
                  (ThetaLowerSegment.join cell3003953408 cell3004084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3004215552 cell3004346624)
                  (ThetaLowerSegment.join cell3004477696 cell3004608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3004739840 cell3004870912)
                  (ThetaLowerSegment.join cell3005001984 cell3005133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3005264128 cell3005395200)
                  (ThetaLowerSegment.join cell3005526272 cell3005657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3005788416 cell3005919488)
                  (ThetaLowerSegment.join cell3006050560 cell3006181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3006312704 cell3006443776)
                  (ThetaLowerSegment.join cell3006574848 cell3006705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3006836992 cell3006968064)
                  (ThetaLowerSegment.join cell3007099136 cell3007230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3007361280 cell3007492352)
                  (ThetaLowerSegment.join cell3007623424 cell3007754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3007885568 cell3008016640)
                  (ThetaLowerSegment.join cell3008147712 cell3008278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3008409856 cell3008540928)
                  (ThetaLowerSegment.join cell3008672000 cell3008803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3008934144 cell3009065216)
                  (ThetaLowerSegment.join cell3009196288 cell3009327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3009458432 cell3009589504)
                  (ThetaLowerSegment.join cell3009720576 cell3009851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3009982720 cell3010113792)
                  (ThetaLowerSegment.join cell3010244864 cell3010375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3010507008 cell3010638080)
                  (ThetaLowerSegment.join cell3010769152 cell3010900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3011031296 cell3011162368)
                  (ThetaLowerSegment.join cell3011293440 cell3011424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3011555584 cell3011686656)
                  (ThetaLowerSegment.join cell3011817728 cell3011948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3012079872 cell3012210944)
                  (ThetaLowerSegment.join cell3012342016 cell3012473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3012604160 cell3012735232)
                  (ThetaLowerSegment.join cell3012866304 cell3012997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3013128448 cell3013259520)
                  (ThetaLowerSegment.join cell3013390592 cell3013521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3013652736 cell3013783808)
                  (ThetaLowerSegment.join cell3013914880 cell3014045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3014177024 cell3014308096)
                  (ThetaLowerSegment.join cell3014439168 cell3014570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3014701312 cell3014832384)
                  (ThetaLowerSegment.join cell3014963456 cell3015094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3015225600 cell3015356672)
                  (ThetaLowerSegment.join cell3015487744 cell3015618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3015749888 cell3015880960)
                  (ThetaLowerSegment.join cell3016012032 cell3016143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3016274176 cell3016405248)
                  (ThetaLowerSegment.join cell3016536320 cell3016667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3016798464 cell3016929536)
                (ThetaLowerSegment.join cell3017060608 cell3017191680))
              (ThetaLowerSegment.join cell3017322752 cell3017339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
