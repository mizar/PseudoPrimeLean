/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2313341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2281341184 :
    ThetaLowerSegment 2281341184 2281472256 (228129339424997 / 100000) (4562847648709 / 2000) := by
  exact
    packedTile65536 2281341184 2281472256 14 6053 47763 31 _ _ (2154801 / 100000) (538701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281472256 :
    ThetaLowerSegment 2281472256 2281603328 (4562847648709 / 2000) (7129857383008 / 3125) := by
  exact
    packedTile65536 2281472256 2281603328 14 6058 47764 31 _ _ (2154807 / 100000) (215481 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281603328 :
    ThetaLowerSegment 2281603328 2281734400 (7129857383008 / 3125) (228168505197101 / 100000) := by
  exact
    packedTile65536 2281603328 2281734400 14 6065 47766 31 _ _ (2154813 / 100000) (67338 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281734400 :
    ThetaLowerSegment 2281734400 2281865472 (228168505197101 / 100000)
      (228181567709879 / 100000) := by
  exact
    packedTile65536 2281734400 2281865472 14 6062 47767 31 _ _ (2154819 / 100000) (1077411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281865472 :
    ThetaLowerSegment 2281865472 2281996544 (228181567709879 / 100000)
      (228194712136279 / 100000) := by
  exact
    packedTile65536 2281865472 2281996544 14 6100 47768 31 _ _ (269353 / 12500) (2154827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2281996544 :
    ThetaLowerSegment 2281996544 2282127616 (228194712136279 / 100000)
      (228207832896149 / 100000) := by
  exact
    packedTile65536 2281996544 2282127616 14 6089 47770 31 _ _ (215483 / 10000) (2154833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282127616 :
    ThetaLowerSegment 2282127616 2282258688 (228207832896149 / 100000)
      (228220805008869 / 100000) := by
  exact
    packedTile65536 2282127616 2282258688 14 6020 47771 31 _ _ (538709 / 25000) (2154839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282258688 :
    ThetaLowerSegment 2282258688 2282389760 (228220805008869 / 100000)
      (228233984022541 / 100000) := by
  exact
    packedTile65536 2282258688 2282389760 14 6116 47772 31 _ _ (1077421 / 50000) (430969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282389760 :
    ThetaLowerSegment 2282389760 2282520832 (228233984022541 / 100000)
      (228246964820869 / 100000) := by
  exact
    packedTile65536 2282389760 2282520832 14 6024 47774 31 _ _ (2154847 / 100000) (43097 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282520832 :
    ThetaLowerSegment 2282520832 2282651904 (228246964820869 / 100000)
      (45652035675893 / 20000) := by
  exact
    packedTile65536 2282520832 2282651904 14 6132 47775 31 _ _ (2154853 / 100000) (269357 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282651904 :
    ThetaLowerSegment 2282651904 2282782976 (45652035675893 / 20000) (114136768175203 / 50000) := by
  exact
    packedTile65536 2282651904 2282782976 14 6199 47777 31 _ _ (2154859 / 100000) (1077431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282782976 :
    ThetaLowerSegment 2282782976 2282914048 (114136768175203 / 50000)
      (228286657323391 / 100000) := by
  exact
    packedTile65536 2282782976 2282914048 14 6089 47778 31 _ _ (430973 / 20000) (538717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2282914048 :
    ThetaLowerSegment 2282914048 2283045120 (228286657323391 / 100000)
      (228299575769041 / 100000) := by
  exact
    packedTile65536 2282914048 2283045120 14 5995 47779 31 _ _ (215487 / 10000) (2154873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283045120 :
    ThetaLowerSegment 2283045120 2283176192 (228299575769041 / 100000)
      (45662575994693 / 20000) := by
  exact
    packedTile65536 2283045120 2283176192 14 6174 47781 31 _ _ (538719 / 25000) (2154879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283176192 :
    ThetaLowerSegment 2283176192 2283307264 (45662575994693 / 20000)
      (228325817884993 / 100000) := by
  exact
    packedTile65536 2283176192 2283307264 14 6004 47782 31 _ _ (1077441 / 50000) (430977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283307264 :
    ThetaLowerSegment 2283307264 2283438336 (228325817884993 / 100000)
      (228338661017473 / 100000) := by
  exact
    packedTile65536 2283307264 2283438336 14 5960 47783 31 _ _ (269361 / 12500) (2154891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283438336 :
    ThetaLowerSegment 2283438336 2283569408 (228338661017473 / 100000)
      (28543979773521 / 12500) := by
  exact
    packedTile65536 2283438336 2283569408 14 6115 47785 31 _ _ (2154893 / 100000) (134681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283569408 :
    ThetaLowerSegment 2283569408 2283700480 (28543979773521 / 12500) (45672980668161 / 20000) := by
  exact
    packedTile65536 2283569408 2283700480 14 6063 47786 31 _ _ (2154899 / 100000) (1077451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283700480 :
    ThetaLowerSegment 2283700480 2283831552 (45672980668161 / 20000) (22837803317697 / 10000) := by
  exact
    packedTile65536 2283700480 2283831552 14 6093 47788 31 _ _ (430981 / 20000) (538727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283831552 :
    ThetaLowerSegment 2283831552 2283962624 (22837803317697 / 10000)
      (228391262175599 / 100000) := by
  exact
    packedTile65536 2283831552 2283962624 14 6139 47789 31 _ _ (2154911 / 100000) (1077457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2283962624 :
    ThetaLowerSegment 2283962624 2284093696 (228391262175599 / 100000)
      (228404340360803 / 100000) := by
  exact
    packedTile65536 2283962624 2284093696 14 6069 47790 31 _ _ (538729 / 25000) (2154919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284093696 :
    ThetaLowerSegment 2284093696 2284224768 (228404340360803 / 100000)
      (228417429357031 / 100000) := by
  exact
    packedTile65536 2284093696 2284224768 14 6074 47792 31 _ _ (1077461 / 50000) (86197 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284224768 :
    ThetaLowerSegment 2284224768 2284355840 (228417429357031 / 100000)
      (228430619671319 / 100000) := by
  exact
    packedTile65536 2284224768 2284355840 14 6121 47793 31 _ _ (134683 / 6250) (2154931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284355840 :
    ThetaLowerSegment 2284355840 2284486912 (228430619671319 / 100000)
      (228443579438381 / 100000) := by
  exact
    packedTile65536 2284355840 2284486912 14 6014 47794 31 _ _ (2154933 / 100000) (269367 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284486912 :
    ThetaLowerSegment 2284486912 2284617984 (228443579438381 / 100000)
      (228456612509453 / 100000) := by
  exact
    packedTile65536 2284486912 2284617984 14 6048 47796 31 _ _ (2154939 / 100000) (1077471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284617984 :
    ThetaLowerSegment 2284617984 2284749056 (228456612509453 / 100000)
      (228469710265163 / 100000) := by
  exact
    packedTile65536 2284617984 2284749056 14 6078 47797 31 _ _ (430989 / 20000) (538737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284749056 :
    ThetaLowerSegment 2284749056 2284880128 (228469710265163 / 100000)
      (228482605491947 / 100000) := by
  exact
    packedTile65536 2284749056 2284880128 14 5984 47799 31 _ _ (2154951 / 100000) (1077477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2284880128 :
    ThetaLowerSegment 2284880128 2285011200 (228482605491947 / 100000)
      (228495653750527 / 100000) := by
  exact
    packedTile65536 2284880128 2285011200 14 6055 47800 31 _ _ (538739 / 25000) (2154959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285011200 :
    ThetaLowerSegment 2285011200 2285142272 (228495653750527 / 100000)
      (228509027444699 / 100000) := by
  exact
    packedTile65536 2285011200 2285142272 14 6206 47801 31 _ _ (1077481 / 50000) (430993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285142272 :
    ThetaLowerSegment 2285142272 2285273344 (228509027444699 / 100000)
      (228522243863443 / 100000) := by
  exact
    packedTile65536 2285142272 2285273344 14 6133 47803 31 _ _ (269371 / 12500) (2154971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285273344 :
    ThetaLowerSegment 2285273344 2285404416 (228522243863443 / 100000) (9141410654853 / 4000) := by
  exact
    packedTile65536 2285273344 2285404416 14 6043 47804 31 _ _ (1077487 / 50000) (2154977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285404416 :
    ThetaLowerSegment 2285404416 2285535488 (9141410654853 / 4000) (45709665108813 / 20000) := by
  exact
    packedTile65536 2285404416 2285535488 14 6060 47805 31 _ _ (2154979 / 100000) (1077491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285535488 :
    ThetaLowerSegment 2285535488 2285666560 (45709665108813 / 20000) (45712277812627 / 20000) := by
  exact
    packedTile65536 2285535488 2285666560 14 6062 47807 31 _ _ (430997 / 20000) (538747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285666560 :
    ThetaLowerSegment 2285666560 2285797632 (45712277812627 / 20000)
      (228574637947803 / 100000) := by
  exact
    packedTile65536 2285666560 2285797632 14 6148 47808 31 _ _ (2154991 / 100000) (1077497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285797632 :
    ThetaLowerSegment 2285797632 2285928704 (228574637947803 / 100000)
      (228587809289467 / 100000) := by
  exact
    packedTile65536 2285797632 2285928704 14 6112 47810 31 _ _ (2154997 / 100000) (431 / 20)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2285928704 :
    ThetaLowerSegment 2285928704 2286059776 (228587809289467 / 100000)
      (228600903081619 / 100000) := by
  exact
    packedTile65536 2285928704 2286059776 14 6076 47811 31 _ _ (1077501 / 50000) (431001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286059776 :
    ThetaLowerSegment 2286059776 2286190848 (228600903081619 / 100000)
      (45722786882999 / 20000) := by
  exact
    packedTile65536 2286059776 2286190848 14 6047 47812 31 _ _ (67344 / 3125) (2155011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286190848 :
    ThetaLowerSegment 2286190848 2286321920 (45722786882999 / 20000)
      (228627233006389 / 100000) := by
  exact
    packedTile65536 2286190848 2286321920 14 6171 47814 31 _ _ (1077507 / 50000) (2155017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286321920 :
    ThetaLowerSegment 2286321920 2286452992 (228627233006389 / 100000)
      (228640469139229 / 100000) := by
  exact
    packedTile65536 2286321920 2286452992 14 6142 47815 31 _ _ (107751 / 5000) (2155023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286452992 :
    ThetaLowerSegment 2286452992 2286584064 (228640469139229 / 100000)
      (228653683752529 / 100000) := by
  exact
    packedTile65536 2286452992 2286584064 14 6132 47816 31 _ _ (86201 / 4000) (538757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286584064 :
    ThetaLowerSegment 2286584064 2286715136 (228653683752529 / 100000)
      (45733359854239 / 20000) := by
  exact
    packedTile65536 2286584064 2286715136 14 6086 47818 31 _ _ (2155031 / 100000) (1077517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286715136 :
    ThetaLowerSegment 2286715136 2286846208 (45733359854239 / 20000) (22867993422171 / 10000) := by
  exact
    packedTile65536 2286715136 2286846208 14 6095 47819 31 _ _ (2155037 / 100000) (13469 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286846208 :
    ThetaLowerSegment 2286846208 2286977280 (22867993422171 / 10000) (114346598175089 / 50000) := by
  exact
    packedTile65536 2286846208 2286977280 14 6154 47820 31 _ _ (1077521 / 50000) (431009 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2286977280 :
    ThetaLowerSegment 2286977280 2287108352 (114346598175089 / 50000)
      (114353173226537 / 50000) := by
  exact
    packedTile65536 2286977280 2287108352 14 6102 47822 31 _ _ (269381 / 12500) (2155051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287108352 :
    ThetaLowerSegment 2287108352 2287239424 (114353173226537 / 50000) (57179891927341 / 25000) := by
  exact
    packedTile65536 2287108352 2287239424 14 6135 47823 31 _ _ (1077527 / 50000) (2155057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287239424 :
    ThetaLowerSegment 2287239424 2287370496 (57179891927341 / 25000) (57183161153361 / 25000) := by
  exact
    packedTile65536 2287239424 2287370496 14 6068 47825 31 _ _ (107753 / 5000) (2155063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287370496 :
    ThetaLowerSegment 2287370496 2287501568 (57183161153361 / 25000) (114372862928997 / 50000) := by
  exact
    packedTile65536 2287370496 2287501568 14 6070 47826 31 _ _ (431013 / 20000) (538767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287501568 :
    ThetaLowerSegment 2287501568 2287632640 (114372862928997 / 50000) (22875860456229 / 10000) := by
  exact
    packedTile65536 2287501568 2287632640 14 5976 47827 31 _ _ (2155071 / 100000) (1077537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287632640 :
    ThetaLowerSegment 2287632640 2287763712 (22875860456229 / 10000)
      (228771765617529 / 100000) := by
  exact
    packedTile65536 2287632640 2287763712 14 6107 47829 31 _ _ (2155077 / 100000) (53877 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287763712 :
    ThetaLowerSegment 2287763712 2287894784 (228771765617529 / 100000)
      (228784907313663 / 100000) := by
  exact
    packedTile65536 2287763712 2287894784 14 6098 47830 31 _ _ (2155083 / 100000) (1077543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2287894784 :
    ThetaLowerSegment 2287894784 2288025856 (228784907313663 / 100000)
      (228797956371503 / 100000) := by
  exact
    packedTile65536 2287894784 2288025856 14 6055 47831 31 _ _ (134693 / 6250) (2155091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288025856 :
    ThetaLowerSegment 2288025856 2288156928 (228797956371503 / 100000)
      (228810970984169 / 100000) := by
  exact
    packedTile65536 2288025856 2288156928 14 6039 47833 31 _ _ (1077547 / 50000) (2155097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288156928 :
    ThetaLowerSegment 2288156928 2288288000 (228810970984169 / 100000)
      (228824295967469 / 100000) := by
  exact
    packedTile65536 2288156928 2288288000 14 6183 47834 31 _ _ (21551 / 1000) (2155103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288288000 :
    ThetaLowerSegment 2288288000 2288419072 (228824295967469 / 100000)
      (114418722131537 / 50000) := by
  exact
    packedTile65536 2288288000 2288419072 14 6101 47836 31 _ _ (431021 / 20000) (538777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288419072 :
    ThetaLowerSegment 2288419072 2288550144 (114418722131537 / 50000) (7151574351228 / 3125) := by
  exact
    packedTile65536 2288419072 2288550144 14 6002 47837 31 _ _ (2155111 / 100000) (1077557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288550144 :
    ThetaLowerSegment 2288550144 2288681216 (7151574351228 / 3125) (228863544849049 / 100000) := by
  exact
    packedTile65536 2288550144 2288681216 14 6109 47838 31 _ _ (2155117 / 100000) (26939 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288681216 :
    ThetaLowerSegment 2288681216 2288812288 (228863544849049 / 100000)
      (57219162538003 / 25000) := by
  exact
    packedTile65536 2288681216 2288812288 14 6081 47840 31 _ _ (2155123 / 100000) (1077563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288812288 :
    ThetaLowerSegment 2288812288 2288943360 (57219162538003 / 25000) (57222474969739 / 25000) := by
  exact
    packedTile65536 2288812288 2288943360 14 6148 47841 31 _ _ (269391 / 12500) (2155131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2288943360 :
    ThetaLowerSegment 2288943360 2289074432 (57222474969739 / 25000) (57225785255563 / 25000) := by
  exact
    packedTile65536 2288943360 2289074432 14 6144 47842 31 _ _ (1077567 / 50000) (2155137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289074432 :
    ThetaLowerSegment 2289074432 2289205504 (57225785255563 / 25000) (57229064301073 / 25000) := by
  exact
    packedTile65536 2289074432 2289205504 14 6086 47844 31 _ _ (107757 / 5000) (2155143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289205504 :
    ThetaLowerSegment 2289205504 2289336576 (57229064301073 / 25000) (14308082606209 / 6250) := by
  exact
    packedTile65536 2289205504 2289336576 14 6062 47845 31 _ _ (1077573 / 50000) (2155149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289336576 :
    ThetaLowerSegment 2289336576 2289467648 (14308082606209 / 6250) (114471253456581 / 50000) := by
  exact
    packedTile65536 2289336576 2289467648 14 6118 47847 31 _ _ (2155151 / 100000) (1077577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289467648 :
    ThetaLowerSegment 2289467648 2289598720 (114471253456581 / 50000)
      (228955595181623 / 100000) := by
  exact
    packedTile65536 2289467648 2289598720 14 6073 47848 31 _ _ (2155157 / 100000) (53879 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289598720 :
    ThetaLowerSegment 2289598720 2289729792 (228955595181623 / 100000)
      (45793724197359 / 20000) := by
  exact
    packedTile65536 2289598720 2289729792 14 6044 47849 31 _ _ (2155163 / 100000) (1077583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289729792 :
    ThetaLowerSegment 2289729792 2289860864 (45793724197359 / 20000)
      (228981698546219 / 100000) := by
  exact
    packedTile65536 2289729792 2289860864 14 6068 47851 31 _ _ (67349 / 3125) (2155171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289860864 :
    ThetaLowerSegment 2289860864 2289991936 (228981698546219 / 100000)
      (228994748124789 / 100000) := by
  exact
    packedTile65536 2289860864 2289991936 14 6055 47852 31 _ _ (1077587 / 50000) (2155177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2289991936 :
    ThetaLowerSegment 2289991936 2290123008 (228994748124789 / 100000)
      (229007784808609 / 100000) := by
  exact
    packedTile65536 2289991936 2290123008 14 6049 47853 31 _ _ (107759 / 5000) (2155183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290123008 :
    ThetaLowerSegment 2290123008 2290254080 (229007784808609 / 100000)
      (229020907736163 / 100000) := by
  exact
    packedTile65536 2290123008 2290254080 14 6089 47855 31 _ _ (1077593 / 50000) (2155189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290254080 :
    ThetaLowerSegment 2290254080 2290385152 (229020907736163 / 100000)
      (229033748364141 / 100000) := by
  exact
    packedTile65536 2290254080 2290385152 14 5958 47856 31 _ _ (2155191 / 100000) (1077597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290385152 :
    ThetaLowerSegment 2290385152 2290516224 (229033748364141 / 100000)
      (229046800237173 / 100000) := by
  exact
    packedTile65536 2290385152 2290516224 14 6056 47857 31 _ _ (2155197 / 100000) (2694 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290516224 :
    ThetaLowerSegment 2290516224 2290647296 (229046800237173 / 100000)
      (45812021292099 / 20000) := by
  exact
    packedTile65536 2290516224 2290647296 14 6174 47859 31 _ _ (2155203 / 100000) (1077603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290647296 :
    ThetaLowerSegment 2290647296 2290778368 (45812021292099 / 20000)
      (229073192889543 / 100000) := by
  exact
    packedTile65536 2290647296 2290778368 14 6072 47860 31 _ _ (2155209 / 100000) (538803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290778368 :
    ThetaLowerSegment 2290778368 2290909440 (229073192889543 / 100000)
      (229086305211519 / 100000) := by
  exact
    packedTile65536 2290778368 2290909440 14 6084 47862 31 _ _ (1077607 / 50000) (2155217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2290909440 :
    ThetaLowerSegment 2290909440 2291040512 (229086305211519 / 100000)
      (229099374465599 / 100000) := by
  exact
    packedTile65536 2290909440 2291040512 14 6064 47863 31 _ _ (107761 / 5000) (2155223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291040512 :
    ThetaLowerSegment 2291040512 2291171584 (229099374465599 / 100000)
      (229112454532193 / 100000) := by
  exact
    packedTile65536 2291040512 2291171584 14 6069 47864 31 _ _ (1077613 / 50000) (2155229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291171584 :
    ThetaLowerSegment 2291171584 2291302656 (229112454532193 / 100000)
      (229125635924989 / 100000) := by
  exact
    packedTile65536 2291171584 2291302656 14 6116 47866 31 _ _ (2155231 / 100000) (1077617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291302656 :
    ThetaLowerSegment 2291302656 2291433728 (229125635924989 / 100000)
      (57284673626493 / 25000) := by
  exact
    packedTile65536 2291302656 2291433728 14 6059 47867 31 _ _ (2155237 / 100000) (53881 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291433728 :
    ThetaLowerSegment 2291433728 2291564800 (57284673626493 / 25000)
      (229151891058861 / 100000) := by
  exact
    packedTile65536 2291433728 2291564800 14 6123 47868 31 _ _ (2155243 / 100000) (1077623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291564800 :
    ThetaLowerSegment 2291564800 2291695872 (229151891058861 / 100000)
      (45833014512349 / 20000) := by
  exact
    packedTile65536 2291564800 2291695872 14 6116 47870 31 _ _ (2155249 / 100000) (538813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291695872 :
    ThetaLowerSegment 2291695872 2291826944 (45833014512349 / 20000)
      (229178286424019 / 100000) := by
  exact
    packedTile65536 2291695872 2291826944 14 6131 47871 31 _ _ (1077627 / 50000) (2155257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291826944 :
    ThetaLowerSegment 2291826944 2291958016 (229178286424019 / 100000)
      (229191478770479 / 100000) := by
  exact
    packedTile65536 2291826944 2291958016 14 6121 47873 31 _ _ (107763 / 5000) (2155263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2291958016 :
    ThetaLowerSegment 2291958016 2292089088 (229191478770479 / 100000)
      (229204459937597 / 100000) := by
  exact
    packedTile65536 2291958016 2292089088 14 6023 47874 31 _ _ (1077633 / 50000) (2155269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292089088 :
    ThetaLowerSegment 2292089088 2292220160 (229204459937597 / 100000)
      (45843524866573 / 20000) := by
  exact
    packedTile65536 2292089088 2292220160 14 6108 47875 31 _ _ (2155271 / 100000) (1077637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292220160 :
    ThetaLowerSegment 2292220160 2292351232 (45843524866573 / 20000) (57307724670977 / 25000) := by
  exact
    packedTile65536 2292220160 2292351232 14 6159 47877 31 _ _ (2155277 / 100000) (26941 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292351232 :
    ThetaLowerSegment 2292351232 2292482304 (57307724670977 / 25000)
      (229243810984361 / 100000) := by
  exact
    packedTile65536 2292351232 2292482304 14 5991 47878 31 _ _ (2155283 / 100000) (1077643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292482304 :
    ThetaLowerSegment 2292482304 2292613376 (229243810984361 / 100000)
      (57314204538369 / 25000) := by
  exact
    packedTile65536 2292482304 2292613376 14 6035 47879 31 _ _ (2155289 / 100000) (538823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292613376 :
    ThetaLowerSegment 2292613376 2292744448 (57314204538369 / 25000) (7164687363156 / 3125) := by
  exact
    packedTile65536 2292613376 2292744448 14 6114 47881 31 _ _ (1077647 / 50000) (2155297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292744448 :
    ThetaLowerSegment 2292744448 2292875520 (7164687363156 / 3125) (14330195356787 / 6250) := by
  exact
    packedTile65536 2292744448 2292875520 14 6092 47882 31 _ _ (21553 / 1000) (2155303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2292875520 :
    ThetaLowerSegment 2292875520 2293006592 (14330195356787 / 6250) (114648131149331 / 50000) := by
  exact
    packedTile65536 2292875520 2293006592 14 6095 47883 31 _ _ (1077653 / 50000) (2155309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293006592 :
    ThetaLowerSegment 2293006592 2293137664 (114648131149331 / 50000)
      (229309347191743 / 100000) := by
  exact
    packedTile65536 2293006592 2293137664 14 6071 47885 31 _ _ (2155311 / 100000) (1077657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293137664 :
    ThetaLowerSegment 2293137664 2293268736 (229309347191743 / 100000)
      (57330609107971 / 25000) := by
  exact
    packedTile65536 2293137664 2293268736 14 6073 47886 31 _ _ (2155317 / 100000) (53883 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293268736 :
    ThetaLowerSegment 2293268736 2293399808 (57330609107971 / 25000) (114667832902229 / 50000) := by
  exact
    packedTile65536 2293268736 2293399808 14 6138 47888 31 _ _ (2155323 / 100000) (1077663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293399808 :
    ThetaLowerSegment 2293399808 2293530880 (114667832902229 / 50000)
      (229348707700237 / 100000) := by
  exact
    packedTile65536 2293399808 2293530880 14 6051 47889 31 _ _ (2155329 / 100000) (538833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293530880 :
    ThetaLowerSegment 2293530880 2293661952 (229348707700237 / 100000)
      (229361947916999 / 100000) := by
  exact
    packedTile65536 2293530880 2293661952 14 6143 47890 31 _ _ (1077667 / 50000) (2155337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293661952 :
    ThetaLowerSegment 2293661952 2293793024 (229361947916999 / 100000)
      (229374834694859 / 100000) := by
  exact
    packedTile65536 2293661952 2293793024 14 5979 47892 31 _ _ (107767 / 5000) (2155343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293793024 :
    ThetaLowerSegment 2293793024 2293924096 (229374834694859 / 100000)
      (229388055587223 / 100000) := by
  exact
    packedTile65536 2293793024 2293924096 14 6134 47893 31 _ _ (1077673 / 50000) (2155349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2293924096 :
    ThetaLowerSegment 2293924096 2294055168 (229388055587223 / 100000) (5735029380219 / 2500) := by
  exact
    packedTile65536 2293924096 2294055168 14 6087 47894 31 _ _ (2155351 / 100000) (1077677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294055168 :
    ThetaLowerSegment 2294055168 2294186240 (5735029380219 / 2500) (14338391408529 / 6250) := by
  exact
    packedTile65536 2294055168 2294186240 14 6072 47896 31 _ _ (2155357 / 100000) (13471 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294186240 :
    ThetaLowerSegment 2294186240 2294317312 (14338391408529 / 6250) (114713733145101 / 50000) := by
  exact
    packedTile65536 2294186240 2294317312 14 6126 47897 31 _ _ (2155363 / 100000) (1077683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294317312 :
    ThetaLowerSegment 2294317312 2294448384 (114713733145101 / 50000)
      (229440581710567 / 100000) := by
  exact
    packedTile65536 2294317312 2294448384 14 6085 47899 31 _ _ (2155369 / 100000) (538843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294448384 :
    ThetaLowerSegment 2294448384 2294579456 (229440581710567 / 100000)
      (229453684229113 / 100000) := by
  exact
    packedTile65536 2294448384 2294579456 14 6079 47900 31 _ _ (1077687 / 50000) (2155377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294579456 :
    ThetaLowerSegment 2294579456 2294710528 (229453684229113 / 100000)
      (229466821270213 / 100000) := by
  exact
    packedTile65536 2294579456 2294710528 14 6095 47901 31 _ _ (107769 / 5000) (2155383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294710528 :
    ThetaLowerSegment 2294710528 2294841600 (229466821270213 / 100000)
      (229479921706321 / 100000) := by
  exact
    packedTile65536 2294710528 2294841600 14 6078 47903 31 _ _ (1077693 / 50000) (2155389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294841600 :
    ThetaLowerSegment 2294841600 2294972672 (229479921706321 / 100000)
      (229493134253151 / 100000) := by
  exact
    packedTile65536 2294841600 2294972672 14 6130 47904 31 _ _ (2155391 / 100000) (1077697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2294972672 :
    ThetaLowerSegment 2294972672 2295103744 (229493134253151 / 100000)
      (22950629726263 / 10000) := by
  exact
    packedTile65536 2294972672 2295103744 14 6107 47905 31 _ _ (2155397 / 100000) (10777 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295103744 :
    ThetaLowerSegment 2295103744 2295234816 (22950629726263 / 10000)
      (229519236146839 / 100000) := by
  exact
    packedTile65536 2295103744 2295234816 14 6003 47907 31 _ _ (2155403 / 100000) (1077703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295234816 :
    ThetaLowerSegment 2295234816 2295365888 (229519236146839 / 100000)
      (229532358276831 / 100000) := by
  exact
    packedTile65536 2295234816 2295365888 14 6088 47908 31 _ _ (2155409 / 100000) (538853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295365888 :
    ThetaLowerSegment 2295365888 2295496960 (229532358276831 / 100000)
      (229545441639811 / 100000) := by
  exact
    packedTile65536 2295365888 2295496960 14 6070 47909 31 _ _ (1077707 / 50000) (2155417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295496960 :
    ThetaLowerSegment 2295496960 2295628032 (229545441639811 / 100000)
      (229558507795851 / 100000) := by
  exact
    packedTile65536 2295496960 2295628032 14 6062 47911 31 _ _ (107771 / 5000) (2155423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295628032 :
    ThetaLowerSegment 2295628032 2295759104 (229558507795851 / 100000)
      (229571634340191 / 100000) := by
  exact
    packedTile65536 2295628032 2295759104 14 6090 47912 31 _ _ (1077713 / 50000) (2155429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295759104 :
    ThetaLowerSegment 2295759104 2295890176 (229571634340191 / 100000)
      (229584730738947 / 100000) := by
  exact
    packedTile65536 2295759104 2295890176 14 6076 47914 31 _ _ (2155431 / 100000) (1077717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2295890176 :
    ThetaLowerSegment 2295890176 2296021248 (229584730738947 / 100000)
      (57399504752013 / 25000) := by
  exact
    packedTile65536 2295890176 2296021248 14 6165 47915 31 _ _ (2155437 / 100000) (26943 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296021248 :
    ThetaLowerSegment 2296021248 2296152320 (57399504752013 / 25000)
      (229611173676681 / 100000) := by
  exact
    packedTile65536 2296021248 2296152320 14 6103 47916 31 _ _ (2155443 / 100000) (1077723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296152320 :
    ThetaLowerSegment 2296152320 2296283392 (229611173676681 / 100000)
      (114812127548331 / 50000) := by
  exact
    packedTile65536 2296152320 2296283392 14 6069 47918 31 _ _ (2155449 / 100000) (538863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296283392 :
    ThetaLowerSegment 2296283392 2296414464 (114812127548331 / 50000) (57409396644913 / 25000) := by
  exact
    packedTile65536 2296283392 2296414464 14 6185 47919 31 _ _ (1077727 / 50000) (2155457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296414464 :
    ThetaLowerSegment 2296414464 2296545536 (57409396644913 / 25000) (28706346441059 / 12500) := by
  exact
    packedTile65536 2296414464 2296545536 14 6117 47920 31 _ _ (107773 / 5000) (2155463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296545536 :
    ThetaLowerSegment 2296545536 2296676608 (28706346441059 / 12500) (114831971790599 / 50000) := by
  exact
    packedTile65536 2296545536 2296676608 14 6111 47922 31 _ _ (1077733 / 50000) (2155469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296676608 :
    ThetaLowerSegment 2296676608 2296807680 (114831971790599 / 50000)
      (229677025134697 / 100000) := by
  exact
    packedTile65536 2296676608 2296807680 14 6069 47923 31 _ _ (2155471 / 100000) (1077737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296807680 :
    ThetaLowerSegment 2296807680 2296938752 (229677025134697 / 100000)
      (114845018874673 / 50000) := by
  exact
    packedTile65536 2296807680 2296938752 14 6037 47925 31 _ _ (2155477 / 100000) (53887 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2296938752 :
    ThetaLowerSegment 2296938752 2297069824 (114845018874673 / 50000)
      (229703222838857 / 100000) := by
  exact
    packedTile65536 2296938752 2297069824 14 6117 47926 31 _ _ (2155483 / 100000) (1077743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297069824 :
    ThetaLowerSegment 2297069824 2297200896 (229703222838857 / 100000)
      (57429079358633 / 25000) := by
  exact
    packedTile65536 2297069824 2297200896 14 6075 47927 31 _ _ (2155489 / 100000) (538873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297200896 :
    ThetaLowerSegment 2297200896 2297331968 (57429079358633 / 25000) (2297291900447 / 1000) := by
  exact
    packedTile65536 2297200896 2297331968 14 5972 47929 31 _ _ (1077747 / 50000) (2155497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297331968 :
    ThetaLowerSegment 2297331968 2297463040 (2297291900447 / 1000) (2297422480637 / 1000) := by
  exact
    packedTile65536 2297331968 2297463040 14 6058 47930 31 _ _ (4311 / 200) (2155503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297463040 :
    ThetaLowerSegment 2297463040 2297594112 (2297422480637 / 1000) (9190211555 / 4) := by
  exact
    packedTile65536 2297463040 2297594112 14 6050 47931 31 _ _ (1077753 / 50000) (2155509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297594112 :
    ThetaLowerSegment 2297594112 2297725184 (9190211555 / 4) (229768590533381 / 100000) := by
  exact
    packedTile65536 2297594112 2297725184 14 6171 47933 31 _ _ (2155511 / 100000) (1077757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297725184 :
    ThetaLowerSegment 2297725184 2297856256 (229768590533381 / 100000)
      (229781450347803 / 100000) := by
  exact
    packedTile65536 2297725184 2297856256 14 5966 47934 31 _ _ (2155517 / 100000) (13472 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297856256 :
    ThetaLowerSegment 2297856256 2297987328 (229781450347803 / 100000)
      (229794525750321 / 100000) := by
  exact
    packedTile65536 2297856256 2297987328 14 6066 47935 31 _ _ (2155523 / 100000) (1077763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2297987328 :
    ThetaLowerSegment 2297987328 2298118400 (229794525750321 / 100000)
      (229807474007017 / 100000) := by
  exact
    packedTile65536 2297987328 2298118400 14 6007 47937 31 _ _ (269441 / 12500) (2155531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298118400 :
    ThetaLowerSegment 2298118400 2298249472 (229807474007017 / 100000)
      (229820672341699 / 100000) := by
  exact
    packedTile65536 2298118400 2298249472 14 6123 47938 31 _ _ (1077767 / 50000) (2155537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298249472 :
    ThetaLowerSegment 2298249472 2298380544 (229820672341699 / 100000)
      (229833961245799 / 100000) := by
  exact
    packedTile65536 2298249472 2298380544 14 6165 47940 31 _ _ (107777 / 5000) (2155543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298380544 :
    ThetaLowerSegment 2298380544 2298511616 (229833961245799 / 100000) (1838776121859 / 800) := by
  exact
    packedTile65536 2298380544 2298511616 14 6056 47941 31 _ _ (1077773 / 50000) (2155549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298511616 :
    ThetaLowerSegment 2298511616 2298642688 (1838776121859 / 800) (229860159782373 / 100000) := by
  exact
    packedTile65536 2298511616 2298642688 14 6098 47942 31 _ _ (2155551 / 100000) (1077777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298642688 :
    ThetaLowerSegment 2298642688 2298773760 (229860159782373 / 100000) (5746831154223 / 2500) := by
  exact
    packedTile65536 2298642688 2298773760 14 6071 47944 31 _ _ (2155557 / 100000) (53889 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298773760 :
    ThetaLowerSegment 2298773760 2298904832 (5746831154223 / 2500) (229886392947657 / 100000) := by
  exact
    packedTile65536 2298773760 2298904832 14 6099 47945 31 _ _ (2155563 / 100000) (1077783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2298904832 :
    ThetaLowerSegment 2298904832 2299035904 (229886392947657 / 100000)
      (229899408267241 / 100000) := by
  exact
    packedTile65536 2298904832 2299035904 14 6038 47946 31 _ _ (134723 / 6250) (2155571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299035904 :
    ThetaLowerSegment 2299035904 2299166976 (229899408267241 / 100000)
      (229912404222887 / 100000) := by
  exact
    packedTile65536 2299035904 2299166976 14 6029 47948 31 _ _ (1077787 / 50000) (2155577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299166976 :
    ThetaLowerSegment 2299166976 2299298048 (229912404222887 / 100000)
      (229925568349947 / 100000) := by
  exact
    packedTile65536 2299166976 2299298048 14 6107 47949 31 _ _ (107779 / 5000) (2155583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299298048 :
    ThetaLowerSegment 2299298048 2299429120 (229925568349947 / 100000)
      (229938807953017 / 100000) := by
  exact
    packedTile65536 2299298048 2299429120 14 6142 47950 31 _ _ (431117 / 20000) (538897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299429120 :
    ThetaLowerSegment 2299429120 2299560192 (229938807953017 / 100000)
      (114975942961807 / 50000) := by
  exact
    packedTile65536 2299429120 2299560192 14 6067 47952 31 _ _ (2155591 / 100000) (1077797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299560192 :
    ThetaLowerSegment 2299560192 2299691264 (114975942961807 / 50000)
      (114982521843851 / 50000) := by
  exact
    packedTile65536 2299560192 2299691264 14 6104 47953 31 _ _ (2155597 / 100000) (5389 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299691264 :
    ThetaLowerSegment 2299691264 2299822336 (114982521843851 / 50000) (45995669182763 / 20000) := by
  exact
    packedTile65536 2299691264 2299822336 14 6171 47955 31 _ _ (2155603 / 100000) (1077803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299822336 :
    ThetaLowerSegment 2299822336 2299953408 (45995669182763 / 20000)
      (229991367941743 / 100000) := by
  exact
    packedTile65536 2299822336 2299953408 14 6041 47956 31 _ _ (269451 / 12500) (2155611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2299953408 :
    ThetaLowerSegment 2299953408 2300084480 (229991367941743 / 100000)
      (230004489164161 / 100000) := by
  exact
    packedTile65536 2299953408 2300084480 14 6087 47957 31 _ _ (1077807 / 50000) (2155617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300084480 :
    ThetaLowerSegment 2300084480 2300215552 (230004489164161 / 100000)
      (230017504797721 / 100000) := by
  exact
    packedTile65536 2300084480 2300215552 14 6038 47959 31 _ _ (107781 / 5000) (2155623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300215552 :
    ThetaLowerSegment 2300215552 2300346624 (230017504797721 / 100000)
      (57507684544899 / 25000) := by
  exact
    packedTile65536 2300215552 2300346624 14 6139 47960 31 _ _ (3449 / 160) (538907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300346624 :
    ThetaLowerSegment 2300346624 2300477696 (57507684544899 / 25000)
      (230043997465877 / 100000) := by
  exact
    packedTile65536 2300346624 2300477696 14 6151 47961 31 _ _ (2155631 / 100000) (1077817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300477696 :
    ThetaLowerSegment 2300477696 2300608768 (230043997465877 / 100000)
      (230057082182467 / 100000) := by
  exact
    packedTile65536 2300477696 2300608768 14 6070 47963 31 _ _ (2155637 / 100000) (53891 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300608768 :
    ThetaLowerSegment 2300608768 2300739840 (230057082182467 / 100000)
      (230070011723183 / 100000) := by
  exact
    packedTile65536 2300608768 2300739840 14 5998 47964 31 _ _ (1077821 / 50000) (431129 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300739840 :
    ThetaLowerSegment 2300739840 2300870912 (230070011723183 / 100000)
      (230083102973487 / 100000) := by
  exact
    packedTile65536 2300739840 2300870912 14 6073 47966 31 _ _ (67364 / 3125) (2155651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2300870912 :
    ThetaLowerSegment 2300870912 2301001984 (230083102973487 / 100000)
      (230096207194153 / 100000) := by
  exact
    packedTile65536 2300870912 2301001984 14 6079 47967 31 _ _ (1077827 / 50000) (2155657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301001984 :
    ThetaLowerSegment 2301001984 2301133056 (230096207194153 / 100000)
      (230109391210713 / 100000) := by
  exact
    packedTile65536 2301001984 2301133056 14 6116 47968 31 _ _ (107783 / 5000) (2155663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301133056 :
    ThetaLowerSegment 2301133056 2301264128 (230109391210713 / 100000)
      (57530561360277 / 25000) := by
  exact
    packedTile65536 2301133056 2301264128 14 5963 47970 31 _ _ (431133 / 20000) (538917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301264128 :
    ThetaLowerSegment 2301264128 2301395200 (57530561360277 / 25000)
      (230135254915593 / 100000) := by
  exact
    packedTile65536 2301264128 2301395200 14 6035 47971 31 _ _ (2155671 / 100000) (1077837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301395200 :
    ThetaLowerSegment 2301395200 2301526272 (230135254915593 / 100000)
      (230148477838311 / 100000) := by
  exact
    packedTile65536 2301395200 2301526272 14 6134 47972 31 _ _ (2155677 / 100000) (13473 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301526272 :
    ThetaLowerSegment 2301526272 2301657344 (230148477838311 / 100000)
      (230161623187147 / 100000) := by
  exact
    packedTile65536 2301526272 2301657344 14 6098 47974 31 _ _ (1077841 / 50000) (431137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301657344 :
    ThetaLowerSegment 2301657344 2301788416 (230161623187147 / 100000)
      (230174729770187 / 100000) := by
  exact
    packedTile65536 2301657344 2301788416 14 6080 47975 31 _ _ (269461 / 12500) (2155691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301788416 :
    ThetaLowerSegment 2301788416 2301919488 (230174729770187 / 100000)
      (46037553050361 / 20000) := by
  exact
    packedTile65536 2301788416 2301919488 14 6047 47976 31 _ _ (1077847 / 50000) (2155697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2301919488 :
    ThetaLowerSegment 2301919488 2302050560 (46037553050361 / 20000) (115100469364197 / 50000) := by
  exact
    packedTile65536 2301919488 2302050560 14 6111 47978 31 _ _ (2155699 / 100000) (1077851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302050560 :
    ThetaLowerSegment 2302050560 2302181632 (115100469364197 / 50000)
      (230214021702039 / 100000) := by
  exact
    packedTile65536 2302050560 2302181632 14 6069 47979 31 _ _ (431141 / 20000) (538927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302181632 :
    ThetaLowerSegment 2302181632 2302312704 (230214021702039 / 100000)
      (230227020639369 / 100000) := by
  exact
    packedTile65536 2302181632 2302312704 14 6030 47981 31 _ _ (2155711 / 100000) (1077857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302312704 :
    ThetaLowerSegment 2302312704 2302443776 (230227020639369 / 100000)
      (230239995893973 / 100000) := by
  exact
    packedTile65536 2302312704 2302443776 14 6019 47982 31 _ _ (538929 / 25000) (2155719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302443776 :
    ThetaLowerSegment 2302443776 2302574848 (230239995893973 / 100000)
      (230253038012073 / 100000) := by
  exact
    packedTile65536 2302443776 2302574848 14 6050 47983 31 _ _ (1077861 / 50000) (86229 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302574848 :
    ThetaLowerSegment 2302574848 2302705920 (230253038012073 / 100000)
      (230266198731513 / 100000) := by
  exact
    packedTile65536 2302574848 2302705920 14 6105 47985 31 _ _ (134733 / 6250) (2155731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302705920 :
    ThetaLowerSegment 2302705920 2302836992 (230266198731513 / 100000)
      (230279372421987 / 100000) := by
  exact
    packedTile65536 2302705920 2302836992 14 6111 47986 31 _ _ (1077867 / 50000) (2155737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302836992 :
    ThetaLowerSegment 2302836992 2302968064 (230279372421987 / 100000)
      (230292410331459 / 100000) := by
  exact
    packedTile65536 2302836992 2302968064 14 6048 47987 31 _ _ (2155739 / 100000) (1077871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2302968064 :
    ThetaLowerSegment 2302968064 2303099136 (230292410331459 / 100000)
      (230305616425329 / 100000) := by
  exact
    packedTile65536 2302968064 2303099136 14 6126 47989 31 _ _ (431149 / 20000) (538937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303099136 :
    ThetaLowerSegment 2303099136 2303230208 (230305616425329 / 100000)
      (230318658718879 / 100000) := by
  exact
    packedTile65536 2303099136 2303230208 14 6050 47990 31 _ _ (2155751 / 100000) (1077877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303230208 :
    ThetaLowerSegment 2303230208 2303361280 (230318658718879 / 100000)
      (230331772182627 / 100000) := by
  exact
    packedTile65536 2303230208 2303361280 14 6083 47991 31 _ _ (538939 / 25000) (2155759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303361280 :
    ThetaLowerSegment 2303361280 2303492352 (230331772182627 / 100000)
      (230344874904063 / 100000) := by
  exact
    packedTile65536 2303361280 2303492352 14 6078 47993 31 _ _ (1077881 / 50000) (431153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303492352 :
    ThetaLowerSegment 2303492352 2303623424 (230344874904063 / 100000)
      (46071583028939 / 20000) := by
  exact
    packedTile65536 2303492352 2303623424 14 6049 47994 31 _ _ (269471 / 12500) (2155771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303623424 :
    ThetaLowerSegment 2303623424 2303754496 (46071583028939 / 20000) (23037118392751 / 10000) := by
  exact
    packedTile65536 2303623424 2303754496 14 6155 47996 31 _ _ (2155773 / 100000) (67368 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303754496 :
    ThetaLowerSegment 2303754496 2303885568 (23037118392751 / 10000) (115192136908799 / 50000) := by
  exact
    packedTile65536 2303754496 2303885568 14 6072 47997 31 _ _ (2155779 / 100000) (1077891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2303885568 :
    ThetaLowerSegment 2303885568 2304016640 (115192136908799 / 50000)
      (230397331407343 / 100000) := by
  exact
    packedTile65536 2303885568 2304016640 14 6057 47998 31 _ _ (431157 / 20000) (538947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304016640 :
    ThetaLowerSegment 2304016640 2304147712 (230397331407343 / 100000)
      (230410300639983 / 100000) := by
  exact
    packedTile65536 2304016640 2304147712 14 6016 48000 31 _ _ (215579 / 10000) (2155793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304147712 :
    ThetaLowerSegment 2304147712 2304278784 (230410300639983 / 100000)
      (230423569564363 / 100000) := by
  exact
    packedTile65536 2304147712 2304278784 14 6155 48001 31 _ _ (538949 / 25000) (2155799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304278784 :
    ThetaLowerSegment 2304278784 2304409856 (230423569564363 / 100000)
      (230436672528919 / 100000) := by
  exact
    packedTile65536 2304278784 2304409856 14 6078 48002 31 _ _ (1077901 / 50000) (431161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304409856 :
    ThetaLowerSegment 2304409856 2304540928 (230436672528919 / 100000)
      (230449738881207 / 100000) := by
  exact
    packedTile65536 2304409856 2304540928 14 6061 48004 31 _ _ (67369 / 3125) (2155811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304540928 :
    ThetaLowerSegment 2304540928 2304672000 (230449738881207 / 100000)
      (230462798796361 / 100000) := by
  exact
    packedTile65536 2304540928 2304672000 14 6058 48005 31 _ _ (2155813 / 100000) (269477 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304672000 :
    ThetaLowerSegment 2304672000 2304803072 (230462798796361 / 100000)
      (230475966538813 / 100000) := by
  exact
    packedTile65536 2304672000 2304803072 14 6108 48006 31 _ _ (2155819 / 100000) (1077911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304803072 :
    ThetaLowerSegment 2304803072 2304934144 (230475966538813 / 100000)
      (230489108448013 / 100000) := by
  exact
    packedTile65536 2304803072 2304934144 14 6096 48008 31 _ _ (86233 / 4000) (538957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2304934144 :
    ThetaLowerSegment 2304934144 2305065216 (230489108448013 / 100000)
      (230502330153403 / 100000) := by
  exact
    packedTile65536 2304934144 2305065216 14 6133 48009 31 _ _ (215583 / 10000) (2155833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305065216 :
    ThetaLowerSegment 2305065216 2305196288 (230502330153403 / 100000)
      (230515260857731 / 100000) := by
  exact
    packedTile65536 2305065216 2305196288 14 5998 48011 31 _ _ (538959 / 25000) (2155839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305196288 :
    ThetaLowerSegment 2305196288 2305327360 (230515260857731 / 100000)
      (46105655135177 / 20000) := by
  exact
    packedTile65536 2305196288 2305327360 14 6037 48012 31 _ _ (1077921 / 50000) (431169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305327360 :
    ThetaLowerSegment 2305327360 2305458432 (46105655135177 / 20000)
      (230541348732093 / 100000) := by
  exact
    packedTile65536 2305327360 2305458432 14 6064 48013 31 _ _ (2155847 / 100000) (43117 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305458432 :
    ThetaLowerSegment 2305458432 2305589504 (230541348732093 / 100000) (4611088652079 / 2000) := by
  exact
    packedTile65536 2305458432 2305589504 14 6069 48015 31 _ _ (2155853 / 100000) (134741 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305589504 :
    ThetaLowerSegment 2305589504 2305720576 (4611088652079 / 2000) (230567451836451 / 100000) := by
  exact
    packedTile65536 2305589504 2305720576 14 6039 48016 31 _ _ (2155859 / 100000) (1077931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305720576 :
    ThetaLowerSegment 2305720576 2305851648 (230567451836451 / 100000) (9223216860571 / 4000) := by
  exact
    packedTile65536 2305720576 2305851648 14 6016 48017 31 _ _ (269483 / 12500) (2155867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305851648 :
    ThetaLowerSegment 2305851648 2305982720 (9223216860571 / 4000) (46118704116079 / 20000) := by
  exact
    packedTile65536 2305851648 2305982720 14 6076 48019 31 _ _ (215587 / 10000) (2155873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2305982720 :
    ThetaLowerSegment 2305982720 2306113792 (46118704116079 / 20000)
      (230606712385639 / 100000) := by
  exact
    packedTile65536 2305982720 2306113792 14 6119 48020 31 _ _ (538969 / 25000) (2155879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306113792 :
    ThetaLowerSegment 2306113792 2306244864 (230606712385639 / 100000)
      (46123962303719 / 20000) := by
  exact
    packedTile65536 2306113792 2306244864 14 6076 48022 31 _ _ (2155881 / 100000) (538971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306244864 :
    ThetaLowerSegment 2306244864 2306375936 (46123962303719 / 20000) (57658289653753 / 25000) := by
  exact
    packedTile65536 2306244864 2306375936 14 6191 48023 31 _ _ (2155887 / 100000) (215589 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306375936 :
    ThetaLowerSegment 2306375936 2306507008 (57658289653753 / 25000) (46129240784711 / 20000) := by
  exact
    packedTile65536 2306375936 2306507008 14 6051 48024 31 _ _ (2155893 / 100000) (269487 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306507008 :
    ThetaLowerSegment 2306507008 2306638080 (46129240784711 / 20000) (57664851123283 / 25000) := by
  exact
    packedTile65536 2306507008 2306638080 14 6123 48026 31 _ _ (2155899 / 100000) (1077951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306638080 :
    ThetaLowerSegment 2306638080 2306769152 (57664851123283 / 25000) (57668092524947 / 25000) := by
  exact
    packedTile65536 2306638080 2306769152 14 6014 48027 31 _ _ (67372 / 3125) (2155907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306769152 :
    ThetaLowerSegment 2306769152 2306900224 (57668092524947 / 25000) (115342705599689 / 50000) := by
  exact
    packedTile65536 2306769152 2306900224 14 6049 48028 31 _ _ (215591 / 10000) (2155913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2306900224 :
    ThetaLowerSegment 2306900224 2307031296 (115342705599689 / 50000) (23069862049671 / 10000) := by
  exact
    packedTile65536 2306900224 2307031296 14 6127 48030 31 _ _ (538979 / 25000) (2155919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307031296 :
    ThetaLowerSegment 2307031296 2307162368 (23069862049671 / 10000)
      (230711713404943 / 100000) := by
  exact
    packedTile65536 2307031296 2307162368 14 6073 48031 31 _ _ (2155921 / 100000) (538981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307162368 :
    ThetaLowerSegment 2307162368 2307293440 (230711713404943 / 100000)
      (230724821441103 / 100000) := by
  exact
    packedTile65536 2307162368 2307293440 14 6080 48032 31 _ _ (2155927 / 100000) (215593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307293440 :
    ThetaLowerSegment 2307293440 2307424512 (230724821441103 / 100000)
      (115368972302637 / 50000) := by
  exact
    packedTile65536 2307293440 2307424512 14 6087 48034 31 _ _ (2155933 / 100000) (67373 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307424512 :
    ThetaLowerSegment 2307424512 2307555584 (115368972302637 / 50000) (57687752936373 / 25000) := by
  exact
    packedTile65536 2307424512 2307555584 14 6061 48035 31 _ _ (1077969 / 50000) (2155941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307555584 :
    ThetaLowerSegment 2307555584 2307686656 (57687752936373 / 25000) (57690970682793 / 25000) := by
  exact
    packedTile65536 2307555584 2307686656 14 5970 48037 31 _ _ (269493 / 12500) (2155947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307686656 :
    ThetaLowerSegment 2307686656 2307817728 (57690970682793 / 25000) (115388466348261 / 50000) := by
  exact
    packedTile65536 2307686656 2307817728 14 6053 48038 31 _ _ (43119 / 2000) (2155953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307817728 :
    ThetaLowerSegment 2307817728 2307948800 (115388466348261 / 50000) (57697504835843 / 25000) := by
  exact
    packedTile65536 2307817728 2307948800 14 6070 48039 31 _ _ (431191 / 20000) (1077979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2307948800 :
    ThetaLowerSegment 2307948800 2308079872 (57697504835843 / 25000) (23080325263199 / 10000) := by
  exact
    packedTile65536 2307948800 2308079872 14 6138 48041 31 _ _ (2155961 / 100000) (538991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308079872 :
    ThetaLowerSegment 2308079872 2308210944 (23080325263199 / 10000) (115408189079543 / 50000) := by
  exact
    packedTile65536 2308079872 2308210944 14 6088 48042 31 _ _ (2155967 / 100000) (215597 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308210944 :
    ThetaLowerSegment 2308210944 2308342016 (115408189079543 / 50000)
      (115414717362759 / 50000) := by
  exact
    packedTile65536 2308210944 2308342016 14 6056 48043 31 _ _ (538993 / 25000) (86239 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308342016 :
    ThetaLowerSegment 2308342016 2308473088 (115414717362759 / 50000)
      (115421252132077 / 50000) := by
  exact
    packedTile65536 2308342016 2308473088 14 6062 48045 31 _ _ (1077989 / 50000) (2155981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308473088 :
    ThetaLowerSegment 2308473088 2308604160 (115421252132077 / 50000)
      (115427834351229 / 50000) := by
  exact
    packedTile65536 2308473088 2308604160 14 6106 48046 31 _ _ (134749 / 6250) (2155987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308604160 :
    ThetaLowerSegment 2308604160 2308735232 (115427834351229 / 50000) (7214645916129 / 3125) := by
  exact
    packedTile65536 2308604160 2308735232 14 6030 48047 31 _ _ (2155989 / 100000) (269499 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308735232 :
    ThetaLowerSegment 2308735232 2308866304 (7214645916129 / 3125) (28860233000691 / 12500) := by
  exact
    packedTile65536 2308735232 2308866304 14 6120 48049 31 _ _ (431199 / 20000) (1077999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308866304 :
    ThetaLowerSegment 2308866304 2308997376 (28860233000691 / 12500) (115447518585819 / 50000) := by
  exact
    packedTile65536 2308866304 2308997376 14 6110 48050 31 _ _ (2156001 / 100000) (539001 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2308997376 :
    ThetaLowerSegment 2308997376 2309128448 (115447518585819 / 50000) (23090812844007 / 10000) := by
  exact
    packedTile65536 2308997376 2309128448 14 6072 48052 31 _ _ (1078003 / 50000) (2156009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309128448 :
    ThetaLowerSegment 2309128448 2309259520 (23090812844007 / 10000) (115460626042557 / 50000) := by
  exact
    packedTile65536 2309128448 2309259520 14 6087 48053 31 _ _ (539003 / 25000) (431203 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309259520 :
    ThetaLowerSegment 2309259520 2309390592 (115460626042557 / 50000)
      (115467238549763 / 50000) := by
  exact
    packedTile65536 2309259520 2309390592 14 6134 48054 31 _ _ (1078009 / 50000) (2156021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309390592 :
    ThetaLowerSegment 2309390592 2309521664 (115467238549763 / 50000) (23094751672663 / 10000) := by
  exact
    packedTile65536 2309390592 2309521664 14 6048 48056 31 _ _ (2156023 / 100000) (1078013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309521664 :
    ThetaLowerSegment 2309521664 2309652736 (23094751672663 / 10000)
      (230960489553123 / 100000) := by
  exact
    packedTile65536 2309521664 2309652736 14 6017 48057 31 _ _ (2156029 / 100000) (67376 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309652736 :
    ThetaLowerSegment 2309652736 2309783808 (230960489553123 / 100000)
      (115486851945819 / 50000) := by
  exact
    packedTile65536 2309652736 2309783808 14 6129 48058 31 _ _ (431207 / 20000) (1078019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309783808 :
    ThetaLowerSegment 2309783808 2309914880 (115486851945819 / 50000)
      (115493315753739 / 50000) := by
  exact
    packedTile65536 2309783808 2309914880 14 5996 48060 31 _ _ (53901 / 2500) (2156043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2309914880 :
    ThetaLowerSegment 2309914880 2310045952 (115493315753739 / 50000) (23099965833741 / 10000) := by
  exact
    packedTile65536 2309914880 2310045952 14 6042 48061 31 _ _ (1078023 / 50000) (2156049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310045952 :
    ThetaLowerSegment 2310045952 2310177024 (23099965833741 / 10000) (23101272401253 / 10000) := by
  exact
    packedTile65536 2310045952 2310177024 14 6060 48062 31 _ _ (539013 / 25000) (431211 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310177024 :
    ThetaLowerSegment 2310177024 2310308096 (23101272401253 / 10000) (288782371901 / 125) := by
  exact
    packedTile65536 2310177024 2310308096 14 6110 48064 31 _ _ (2156057 / 100000) (107803 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310308096 :
    ThetaLowerSegment 2310308096 2310439168 (288782371901 / 125) (115519548469243 / 50000) := by
  exact
    packedTile65536 2310308096 2310439168 14 6122 48065 31 _ _ (2156063 / 100000) (1078033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310439168 :
    ThetaLowerSegment 2310439168 2310570240 (115519548469243 / 50000)
      (115526016676243 / 50000) := by
  exact
    packedTile65536 2310439168 2310570240 14 6000 48067 31 _ _ (2156069 / 100000) (269509 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310570240 :
    ThetaLowerSegment 2310570240 2310701312 (115526016676243 / 50000)
      (231065157381011 / 100000) := by
  exact
    packedTile65536 2310570240 2310701312 14 6087 48068 31 _ _ (86243 / 4000) (1078039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310701312 :
    ThetaLowerSegment 2310701312 2310832384 (231065157381011 / 100000)
      (231078535857411 / 100000) := by
  exact
    packedTile65536 2310701312 2310832384 14 6205 48069 31 _ _ (26951 / 1250) (2156083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310832384 :
    ThetaLowerSegment 2310832384 2310963456 (231078535857411 / 100000)
      (231091769913279 / 100000) := by
  exact
    packedTile65536 2310832384 2310963456 14 6138 48071 31 _ _ (1078043 / 50000) (2156089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2310963456 :
    ThetaLowerSegment 2310963456 2311094528 (231091769913279 / 100000)
      (231104878952639 / 100000) := by
  exact
    packedTile65536 2310963456 2311094528 14 6080 48072 31 _ _ (539023 / 25000) (431219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311094528 :
    ThetaLowerSegment 2311094528 2311225600 (231104878952639 / 100000)
      (57779555759243 / 25000) := by
  exact
    packedTile65536 2311094528 2311225600 14 6189 48073 31 _ _ (2156097 / 100000) (21561 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311225600 :
    ThetaLowerSegment 2311225600 2311356672 (57779555759243 / 25000) (23113151756807 / 10000) := by
  exact
    packedTile65536 2311225600 2311356672 14 6166 48075 31 _ _ (2156103 / 100000) (1078053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311356672 :
    ThetaLowerSegment 2311356672 2311487744 (23113151756807 / 10000)
      (231144684925733 / 100000) := by
  exact
    packedTile65536 2311356672 2311487744 14 6107 48076 31 _ _ (2156109 / 100000) (134757 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311487744 :
    ThetaLowerSegment 2311487744 2311618816 (231144684925733 / 100000)
      (231157830752791 / 100000) := by
  exact
    packedTile65536 2311487744 2311618816 14 6097 48077 31 _ _ (1078057 / 50000) (2156117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311618816 :
    ThetaLowerSegment 2311618816 2311749888 (231157830752791 / 100000)
      (231170799814591 / 100000) := by
  exact
    packedTile65536 2311618816 2311749888 14 6015 48079 31 _ _ (53903 / 2500) (2156123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311749888 :
    ThetaLowerSegment 2311749888 2311880960 (231170799814591 / 100000)
      (231183986681207 / 100000) := by
  exact
    packedTile65536 2311749888 2311880960 14 6116 48080 31 _ _ (1078063 / 50000) (2156129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2311880960 :
    ThetaLowerSegment 2311880960 2312012032 (231183986681207 / 100000)
      (46239405392299 / 20000) := by
  exact
    packedTile65536 2311880960 2312012032 14 6048 48082 31 _ _ (2156131 / 100000) (1078067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312012032 :
    ThetaLowerSegment 2312012032 2312143104 (46239405392299 / 20000)
      (231209981032591 / 100000) := by
  exact
    packedTile65536 2312012032 2312143104 14 6008 48083 31 _ _ (2156137 / 100000) (107807 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312143104 :
    ThetaLowerSegment 2312143104 2312274176 (231209981032591 / 100000)
      (231223099006603 / 100000) := by
  exact
    packedTile65536 2312143104 2312274176 14 6084 48084 31 _ _ (2156143 / 100000) (1078073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312274176 :
    ThetaLowerSegment 2312274176 2312405248 (231223099006603 / 100000)
      (46247232621467 / 20000) := by
  exact
    packedTile65536 2312274176 2312405248 14 6059 48086 31 _ _ (539037 / 25000) (2156151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312405248 :
    ThetaLowerSegment 2312405248 2312536320 (46247232621467 / 20000)
      (231249177652879 / 100000) := by
  exact
    packedTile65536 2312405248 2312536320 14 6036 48087 31 _ _ (1078077 / 50000) (2156157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312536320 :
    ThetaLowerSegment 2312536320 2312667392 (231249177652879 / 100000)
      (231262207327759 / 100000) := by
  exact
    packedTile65536 2312536320 2312667392 14 6043 48088 31 _ _ (13476 / 625) (2156163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312667392 :
    ThetaLowerSegment 2312667392 2312798464 (231262207327759 / 100000)
      (115637674576717 / 50000) := by
  exact
    packedTile65536 2312667392 2312798464 14 6095 48090 31 _ _ (431233 / 20000) (269521 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312798464 :
    ThetaLowerSegment 2312798464 2312929536 (115637674576717 / 50000)
      (115644212087189 / 50000) := by
  exact
    packedTile65536 2312798464 2312929536 14 6064 48091 31 _ _ (2156171 / 100000) (1078087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2312929536 :
    ThetaLowerSegment 2312929536 2313060608 (115644212087189 / 50000)
      (115650801364101 / 50000) := by
  exact
    packedTile65536 2312929536 2313060608 14 6112 48092 31 _ _ (2156177 / 100000) (107809 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313060608 :
    ThetaLowerSegment 2313060608 2313191680 (115650801364101 / 50000) (14457168576343 / 6250) := by
  exact
    packedTile65536 2313060608 2313191680 14 6073 48094 31 _ _ (1078091 / 50000) (431237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313191680 :
    ThetaLowerSegment 2313191680 2313322752 (14457168576343 / 6250) (1156638969537 / 500) := by
  exact
    packedTile65536 2313191680 2313322752 14 6074 48095 31 _ _ (539047 / 25000) (2156191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313322752 :
    ThetaLowerSegment 2313322752 2313339136 (1156638969537 / 500) (11566472708839 / 5000) := by
  exact
    packedTile65536 2313322752 2313339136 11 770 48097 31 _ _ (1078097 / 50000) (2156197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2313339136 :
    ThetaLowerSegment 2313339136 2313341184 (11566472708839 / 5000) (115664835976187 / 50000) := by
  exact
    packedTile65536 2313339136 2313341184 8 101 48097 31 _ _ (1078097 / 50000) (2156197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2281341184_2313341184 :
    ThetaLowerSegment 2281341184 2313341184 (228129339424997 / 100000)
      (115664835976187 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2281341184 cell2281472256)
                  (ThetaLowerSegment.join cell2281603328 cell2281734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2281865472 cell2281996544)
                  (ThetaLowerSegment.join cell2282127616 cell2282258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2282389760 cell2282520832)
                  (ThetaLowerSegment.join cell2282651904 cell2282782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2282914048 cell2283045120)
                  (ThetaLowerSegment.join cell2283176192 cell2283307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2283438336 cell2283569408)
                  (ThetaLowerSegment.join cell2283700480 cell2283831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2283962624 cell2284093696)
                  (ThetaLowerSegment.join cell2284224768 cell2284355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2284486912 cell2284617984)
                  (ThetaLowerSegment.join cell2284749056 cell2284880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2285011200 cell2285142272)
                  (ThetaLowerSegment.join cell2285273344 cell2285404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2285535488 cell2285666560)
                  (ThetaLowerSegment.join cell2285797632 cell2285928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2286059776 cell2286190848)
                  (ThetaLowerSegment.join cell2286321920 cell2286452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2286584064 cell2286715136)
                  (ThetaLowerSegment.join cell2286846208 cell2286977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2287108352 cell2287239424)
                  (ThetaLowerSegment.join cell2287370496 cell2287501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2287632640 cell2287763712)
                  (ThetaLowerSegment.join cell2287894784 cell2288025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2288156928 cell2288288000)
                  (ThetaLowerSegment.join cell2288419072 cell2288550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2288681216 cell2288812288)
                  (ThetaLowerSegment.join cell2288943360 cell2289074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2289205504 cell2289336576)
                  (ThetaLowerSegment.join cell2289467648 cell2289598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2289729792 cell2289860864)
                  (ThetaLowerSegment.join cell2289991936 cell2290123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2290254080 cell2290385152)
                  (ThetaLowerSegment.join cell2290516224 cell2290647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2290778368 cell2290909440)
                  (ThetaLowerSegment.join cell2291040512 cell2291171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2291302656 cell2291433728)
                  (ThetaLowerSegment.join cell2291564800 cell2291695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2291826944 cell2291958016)
                  (ThetaLowerSegment.join cell2292089088 cell2292220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2292351232 cell2292482304)
                  (ThetaLowerSegment.join cell2292613376 cell2292744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2292875520 cell2293006592)
                  (ThetaLowerSegment.join cell2293137664 cell2293268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2293399808 cell2293530880)
                  (ThetaLowerSegment.join cell2293661952 cell2293793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2293924096 cell2294055168)
                  (ThetaLowerSegment.join cell2294186240 cell2294317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2294448384 cell2294579456)
                  (ThetaLowerSegment.join cell2294710528 cell2294841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2294972672 cell2295103744)
                  (ThetaLowerSegment.join cell2295234816 cell2295365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2295496960 cell2295628032)
                  (ThetaLowerSegment.join cell2295759104 cell2295890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2296021248 cell2296152320)
                  (ThetaLowerSegment.join cell2296283392 cell2296414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2296545536 cell2296676608)
                  (ThetaLowerSegment.join cell2296807680 cell2296938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2297069824 cell2297200896)
                  (ThetaLowerSegment.join cell2297331968 cell2297463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2297594112 cell2297725184)
                  (ThetaLowerSegment.join cell2297856256 cell2297987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2298118400 cell2298249472)
                  (ThetaLowerSegment.join cell2298380544 cell2298511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2298642688 cell2298773760)
                  (ThetaLowerSegment.join cell2298904832 cell2299035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2299166976 cell2299298048)
                  (ThetaLowerSegment.join cell2299429120 cell2299560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2299691264 cell2299822336)
                  (ThetaLowerSegment.join cell2299953408 cell2300084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2300215552 cell2300346624)
                  (ThetaLowerSegment.join cell2300477696 cell2300608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2300739840 cell2300870912)
                  (ThetaLowerSegment.join cell2301001984 cell2301133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2301264128 cell2301395200)
                  (ThetaLowerSegment.join cell2301526272 cell2301657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2301788416 cell2301919488)
                  (ThetaLowerSegment.join cell2302050560 cell2302181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2302312704 cell2302443776)
                  (ThetaLowerSegment.join cell2302574848 cell2302705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2302836992 cell2302968064)
                  (ThetaLowerSegment.join cell2303099136 cell2303230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2303361280 cell2303492352)
                  (ThetaLowerSegment.join cell2303623424 cell2303754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2303885568 cell2304016640)
                  (ThetaLowerSegment.join cell2304147712 cell2304278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2304409856 cell2304540928)
                  (ThetaLowerSegment.join cell2304672000 cell2304803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2304934144 cell2305065216)
                  (ThetaLowerSegment.join cell2305196288 cell2305327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2305458432 cell2305589504)
                  (ThetaLowerSegment.join cell2305720576 cell2305851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2305982720 cell2306113792)
                  (ThetaLowerSegment.join cell2306244864 cell2306375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2306507008 cell2306638080)
                  (ThetaLowerSegment.join cell2306769152 cell2306900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2307031296 cell2307162368)
                  (ThetaLowerSegment.join cell2307293440 cell2307424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2307555584 cell2307686656)
                  (ThetaLowerSegment.join cell2307817728 cell2307948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2308079872 cell2308210944)
                  (ThetaLowerSegment.join cell2308342016 cell2308473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2308604160 cell2308735232)
                  (ThetaLowerSegment.join cell2308866304 cell2308997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2309128448 cell2309259520)
                  (ThetaLowerSegment.join cell2309390592 cell2309521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2309652736 cell2309783808)
                  (ThetaLowerSegment.join cell2309914880 cell2310045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2310177024 cell2310308096)
                  (ThetaLowerSegment.join cell2310439168 cell2310570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2310701312 cell2310832384)
                  (ThetaLowerSegment.join cell2310963456 cell2311094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2311225600 cell2311356672)
                  (ThetaLowerSegment.join cell2311487744 cell2311618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2311749888 cell2311880960)
                  (ThetaLowerSegment.join cell2312012032 cell2312143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2312274176 cell2312405248)
                  (ThetaLowerSegment.join cell2312536320 cell2312667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2312798464 cell2312929536)
                (ThetaLowerSegment.join cell2313060608 cell2313191680))
              (ThetaLowerSegment.join cell2313322752 cell2313339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
