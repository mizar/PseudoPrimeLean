/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2153341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2121341184 :
    ThetaLowerSegment 2121341184 2121472256 (212129564250213 / 100000)
      (212142621232613 / 100000) := by
  exact
    packedTile65536 2121341184 2121472256 14 6080 46058 31 _ _ (214753 / 10000) (2147533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121472256 :
    ThetaLowerSegment 2121472256 2121603328 (212142621232613 / 100000)
      (212155534366581 / 100000) := by
  exact
    packedTile65536 2121472256 2121603328 14 6013 46059 31 _ _ (134221 / 6250) (2147539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121603328 :
    ThetaLowerSegment 2121603328 2121734400 (212155534366581 / 100000)
      (212168758930217 / 100000) := by
  exact
    packedTile65536 2121603328 2121734400 14 6158 46060 31 _ _ (1073771 / 50000) (429509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121734400 :
    ThetaLowerSegment 2121734400 2121865472 (212168758930217 / 100000)
      (212181959907773 / 100000) := by
  exact
    packedTile65536 2121734400 2121865472 14 6147 46062 31 _ _ (536887 / 25000) (2147551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121865472 :
    ThetaLowerSegment 2121865472 2121996544 (212181959907773 / 100000)
      (26524379546271 / 12500) := by
  exact
    packedTile65536 2121865472 2121996544 14 6089 46063 31 _ _ (429511 / 20000) (1073779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2121996544 :
    ThetaLowerSegment 2121996544 2122127616 (26524379546271 / 12500)
      (212208263198367 / 100000) := by
  exact
    packedTile65536 2121996544 2122127616 14 6159 46065 31 _ _ (2147561 / 100000) (536891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122127616 :
    ThetaLowerSegment 2122127616 2122258688 (212208263198367 / 100000)
      (212221444964613 / 100000) := by
  exact
    packedTile65536 2122127616 2122258688 14 6138 46066 31 _ _ (2147567 / 100000) (214757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122258688 :
    ThetaLowerSegment 2122258688 2122389760 (212221444964613 / 100000)
      (42446923635479 / 20000) := by
  exact
    packedTile65536 2122258688 2122389760 14 6134 46067 31 _ _ (2147573 / 100000) (268447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122389760 :
    ThetaLowerSegment 2122389760 2122520832 (42446923635479 / 20000) (53061907589639 / 25000) := by
  exact
    packedTile65536 2122389760 2122520832 14 6059 46069 31 _ _ (2147579 / 100000) (1073791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122520832 :
    ThetaLowerSegment 2122520832 2122651904 (53061907589639 / 25000) (106130336324167 / 50000) := by
  exact
    packedTile65536 2122520832 2122651904 14 6073 46070 31 _ _ (1073793 / 50000) (2147589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122651904 :
    ThetaLowerSegment 2122651904 2122782976 (106130336324167 / 50000)
      (106136804871271 / 50000) := by
  exact
    packedTile65536 2122651904 2122782976 14 6024 46072 31 _ _ (268449 / 12500) (429519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122782976 :
    ThetaLowerSegment 2122782976 2122914048 (106136804871271 / 50000) (13267906897733 / 6250) := by
  exact
    packedTile65536 2122782976 2122914048 14 6007 46073 31 _ _ (1073799 / 50000) (2147601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2122914048 :
    ThetaLowerSegment 2122914048 2123045120 (13267906897733 / 6250) (13268716544441 / 6250) := by
  exact
    packedTile65536 2122914048 2123045120 14 6032 46075 31 _ _ (536901 / 25000) (2147607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123045120 :
    ThetaLowerSegment 2123045120 2123176192 (13268716544441 / 6250) (106156311558763 / 50000) := by
  exact
    packedTile65536 2123045120 2123176192 14 6127 46076 31 _ _ (214761 / 10000) (2147613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123176192 :
    ThetaLowerSegment 2123176192 2123307264 (106156311558763 / 50000)
      (106162863935179 / 50000) := by
  exact
    packedTile65536 2123176192 2123307264 14 6102 46077 31 _ _ (67113 / 3125) (2147619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123307264 :
    ThetaLowerSegment 2123307264 2123438336 (106162863935179 / 50000)
      (106169422775821 / 50000) := by
  exact
    packedTile65536 2123307264 2123438336 14 6108 46079 31 _ _ (2147623 / 100000) (1073813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123438336 :
    ThetaLowerSegment 2123438336 2123569408 (106169422775821 / 50000)
      (106175947272723 / 50000) := by
  exact
    packedTile65536 2123438336 2123569408 14 6076 46080 31 _ _ (2147629 / 100000) (134227 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123569408 :
    ThetaLowerSegment 2123569408 2123700480 (106175947272723 / 50000)
      (212364962904421 / 100000) := by
  exact
    packedTile65536 2123569408 2123700480 14 6085 46082 31 _ _ (429527 / 20000) (1073819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123700480 :
    ThetaLowerSegment 2123700480 2123831552 (212364962904421 / 100000)
      (212378020561701 / 100000) := by
  exact
    packedTile65536 2123700480 2123831552 14 6080 46083 31 _ _ (2147641 / 100000) (536911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123831552 :
    ThetaLowerSegment 2123831552 2123962624 (212378020561701 / 100000)
      (53097761510189 / 25000) := by
  exact
    packedTile65536 2123831552 2123962624 14 6065 46085 31 _ _ (2147647 / 100000) (42953 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2123962624 :
    ThetaLowerSegment 2123962624 2124093696 (53097761510189 / 25000)
      (212404273435583 / 100000) := by
  exact
    packedTile65536 2123962624 2124093696 14 6159 46086 31 _ _ (2147653 / 100000) (268457 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124093696 :
    ThetaLowerSegment 2124093696 2124224768 (212404273435583 / 100000)
      (212417434296063 / 100000) := by
  exact
    packedTile65536 2124093696 2124224768 14 6128 46087 31 _ _ (107383 / 5000) (2147663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124224768 :
    ThetaLowerSegment 2124224768 2124355840 (212417434296063 / 100000)
      (212430620965303 / 100000) := by
  exact
    packedTile65536 2124224768 2124355840 14 6140 46089 31 _ _ (1073833 / 50000) (2147669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124355840 :
    ThetaLowerSegment 2124355840 2124486912 (212430620965303 / 100000)
      (212443779751647 / 100000) := by
  exact
    packedTile65536 2124355840 2124486912 14 6127 46090 31 _ _ (268459 / 12500) (85907 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124486912 :
    ThetaLowerSegment 2124486912 2124617984 (212443779751647 / 100000)
      (212456865553701 / 100000) := by
  exact
    packedTile65536 2124486912 2124617984 14 6093 46092 31 _ _ (1073839 / 50000) (2147681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124617984 :
    ThetaLowerSegment 2124617984 2124749056 (212456865553701 / 100000)
      (212470030856621 / 100000) := by
  exact
    packedTile65536 2124617984 2124749056 14 6130 46093 31 _ _ (536921 / 25000) (2147687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124749056 :
    ThetaLowerSegment 2124749056 2124880128 (212470030856621 / 100000)
      (212482944916591 / 100000) := by
  exact
    packedTile65536 2124749056 2124880128 14 6013 46095 31 _ _ (214769 / 10000) (2147693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2124880128 :
    ThetaLowerSegment 2124880128 2125011200 (212482944916591 / 100000)
      (106248043337267 / 50000) := by
  exact
    packedTile65536 2124880128 2125011200 14 6119 46096 31 _ _ (2147697 / 100000) (21477 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125011200 :
    ThetaLowerSegment 2125011200 2125142272 (106248043337267 / 50000)
      (212509129674853 / 100000) := by
  exact
    packedTile65536 2125011200 2125142272 14 6073 46097 31 _ _ (2147703 / 100000) (1073853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125142272 :
    ThetaLowerSegment 2125142272 2125273344 (212509129674853 / 100000)
      (212522239290589 / 100000) := by
  exact
    packedTile65536 2125142272 2125273344 14 6104 46099 31 _ _ (2147709 / 100000) (67116 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125273344 :
    ThetaLowerSegment 2125273344 2125404416 (212522239290589 / 100000)
      (212535288806929 / 100000) := by
  exact
    packedTile65536 2125273344 2125404416 14 6076 46100 31 _ _ (429543 / 20000) (1073859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125404416 :
    ThetaLowerSegment 2125404416 2125535488 (212535288806929 / 100000)
      (42509719217249 / 20000) := by
  exact
    packedTile65536 2125404416 2125535488 14 6196 46102 31 _ _ (2147721 / 100000) (536931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125535488 :
    ThetaLowerSegment 2125535488 2125666560 (42509719217249 / 20000) (6642555252998 / 3125) := by
  exact
    packedTile65536 2125535488 2125666560 14 6133 46103 31 _ _ (2147727 / 100000) (214773 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125666560 :
    ThetaLowerSegment 2125666560 2125797632 (6642555252998 / 3125) (106287300403293 / 50000) := by
  exact
    packedTile65536 2125666560 2125797632 14 5975 46104 31 _ _ (1073867 / 50000) (2147737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125797632 :
    ThetaLowerSegment 2125797632 2125928704 (106287300403293 / 50000)
      (106293869266083 / 50000) := by
  exact
    packedTile65536 2125797632 2125928704 14 6117 46106 31 _ _ (107387 / 5000) (2147743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2125928704 :
    ThetaLowerSegment 2125928704 2126059776 (106293869266083 / 50000)
      (106300439221097 / 50000) := by
  exact
    packedTile65536 2125928704 2126059776 14 6118 46107 31 _ _ (1073873 / 50000) (2147749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126059776 :
    ThetaLowerSegment 2126059776 2126190848 (106300439221097 / 50000)
      (106306975904309 / 50000) := by
  exact
    packedTile65536 2126059776 2126190848 14 6087 46109 31 _ _ (268469 / 12500) (429551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126190848 :
    ThetaLowerSegment 2126190848 2126321920 (106306975904309 / 50000)
      (106313500793113 / 50000) := by
  exact
    packedTile65536 2126190848 2126321920 14 6076 46110 31 _ _ (1073879 / 50000) (2147761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126321920 :
    ThetaLowerSegment 2126321920 2126452992 (106313500793113 / 50000)
      (106319969858281 / 50000) := by
  exact
    packedTile65536 2126321920 2126452992 14 6024 46112 31 _ _ (536941 / 25000) (2147767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126452992 :
    ThetaLowerSegment 2126452992 2126584064 (106319969858281 / 50000) (26581642489641 / 12500) := by
  exact
    packedTile65536 2126452992 2126584064 14 6146 46113 31 _ _ (2147771 / 100000) (1073887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126584064 :
    ThetaLowerSegment 2126584064 2126715136 (26581642489641 / 12500) (42533248700921 / 20000) := by
  exact
    packedTile65536 2126584064 2126715136 14 6101 46114 31 _ _ (2147777 / 100000) (107389 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126715136 :
    ThetaLowerSegment 2126715136 2126846208 (42533248700921 / 20000)
      (212679246182887 / 100000) := by
  exact
    packedTile65536 2126715136 2126846208 14 6054 46116 31 _ _ (2147783 / 100000) (1073893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126846208 :
    ThetaLowerSegment 2126846208 2126977280 (212679246182887 / 100000)
      (212692304740007 / 100000) := by
  exact
    packedTile65536 2126846208 2126977280 14 6080 46117 31 _ _ (2147789 / 100000) (134237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2126977280 :
    ThetaLowerSegment 2126977280 2127108352 (212692304740007 / 100000)
      (212705367629197 / 100000) := by
  exact
    packedTile65536 2126977280 2127108352 14 6082 46119 31 _ _ (429559 / 20000) (1073899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127108352 :
    ThetaLowerSegment 2127108352 2127239424 (212705367629197 / 100000)
      (212718482102103 / 100000) := by
  exact
    packedTile65536 2127108352 2127239424 14 6106 46120 31 _ _ (2147801 / 100000) (536951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127239424 :
    ThetaLowerSegment 2127239424 2127370496 (212718482102103 / 100000)
      (212731590174327 / 100000) := by
  exact
    packedTile65536 2127239424 2127370496 14 6103 46122 31 _ _ (67119 / 3125) (2147811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127370496 :
    ThetaLowerSegment 2127370496 2127501568 (212731590174327 / 100000)
      (212744730500379 / 100000) := by
  exact
    packedTile65536 2127370496 2127501568 14 6118 46123 31 _ _ (1073907 / 50000) (2147817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127501568 :
    ThetaLowerSegment 2127501568 2127632640 (212744730500379 / 100000)
      (212757692594079 / 100000) := by
  exact
    packedTile65536 2127501568 2127632640 14 6035 46124 31 _ _ (107391 / 5000) (2147823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127632640 :
    ThetaLowerSegment 2127632640 2127763712 (212757692594079 / 100000)
      (42554195809143 / 20000) := by
  exact
    packedTile65536 2127632640 2127763712 14 6186 46126 31 _ _ (1073913 / 50000) (2147829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127763712 :
    ThetaLowerSegment 2127763712 2127894784 (42554195809143 / 20000)
      (212783982020643 / 100000) := by
  exact
    packedTile65536 2127763712 2127894784 14 6054 46127 31 _ _ (268479 / 12500) (429567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2127894784 :
    ThetaLowerSegment 2127894784 2128025856 (212783982020643 / 100000)
      (212797238476779 / 100000) := by
  exact
    packedTile65536 2127894784 2128025856 14 6172 46129 31 _ _ (1073919 / 50000) (2147841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128025856 :
    ThetaLowerSegment 2128025856 2128156928 (212797238476779 / 100000)
      (26601315362263 / 12500) := by
  exact
    packedTile65536 2128025856 2128156928 14 6185 46130 31 _ _ (429569 / 20000) (268481 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128156928 :
    ThetaLowerSegment 2128156928 2128288000 (26601315362263 / 12500)
      (212823579684333 / 100000) := by
  exact
    packedTile65536 2128156928 2128288000 14 6079 46131 31 _ _ (2147851 / 100000) (1073927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128288000 :
    ThetaLowerSegment 2128288000 2128419072 (212823579684333 / 100000) (532091870489 / 250) := by
  exact
    packedTile65536 2128288000 2128419072 14 6131 46133 31 _ _ (2147857 / 100000) (107393 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128419072 :
    ThetaLowerSegment 2128419072 2128550144 (532091870489 / 250) (53212475427153 / 25000) := by
  exact
    packedTile65536 2128419072 2128550144 14 6124 46134 31 _ _ (2147863 / 100000) (1073933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128550144 :
    ThetaLowerSegment 2128550144 2128681216 (53212475427153 / 25000)
      (212862855506551 / 100000) := by
  exact
    packedTile65536 2128550144 2128681216 14 6031 46136 31 _ _ (2147869 / 100000) (67121 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128681216 :
    ThetaLowerSegment 2128681216 2128812288 (212862855506551 / 100000)
      (106437915409713 / 50000) := by
  exact
    packedTile65536 2128681216 2128812288 14 6041 46137 31 _ _ (17183 / 800) (1073939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128812288 :
    ThetaLowerSegment 2128812288 2128943360 (106437915409713 / 50000) (13305546358633 / 6250) := by
  exact
    packedTile65536 2128812288 2128943360 14 6011 46139 31 _ _ (1073941 / 50000) (429577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2128943360 :
    ThetaLowerSegment 2128943360 2129074432 (13305546358633 / 6250) (6653181747887 / 3125) := by
  exact
    packedTile65536 2128943360 2129074432 14 6087 46140 31 _ _ (134243 / 6250) (2147891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129074432 :
    ThetaLowerSegment 2129074432 2129205504 (6653181747887 / 3125) (53228771405379 / 25000) := by
  exact
    packedTile65536 2129074432 2129205504 14 6178 46141 31 _ _ (1073947 / 50000) (2147897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129205504 :
    ThetaLowerSegment 2129205504 2129336576 (53228771405379 / 25000) (53232014734379 / 25000) := by
  exact
    packedTile65536 2129205504 2129336576 14 6040 46143 31 _ _ (21479 / 1000) (2147903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129336576 :
    ThetaLowerSegment 2129336576 2129467648 (53232014734379 / 25000) (106470570916481 / 50000) := by
  exact
    packedTile65536 2129336576 2129467648 14 6091 46144 31 _ _ (1073953 / 50000) (2147909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129467648 :
    ThetaLowerSegment 2129467648 2129598720 (106470570916481 / 50000)
      (106477141379289 / 50000) := by
  exact
    packedTile65536 2129467648 2129598720 14 6118 46146 31 _ _ (268489 / 12500) (429583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129598720 :
    ThetaLowerSegment 2129598720 2129729792 (106477141379289 / 50000) (26620921252869 / 12500) := by
  exact
    packedTile65536 2129598720 2129729792 14 6093 46147 31 _ _ (1073959 / 50000) (2147921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129729792 :
    ThetaLowerSegment 2129729792 2129860864 (26620921252869 / 12500)
      (212980405779777 / 100000) := by
  exact
    packedTile65536 2129729792 2129860864 14 6069 46148 31 _ _ (85917 / 4000) (268491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129860864 :
    ThetaLowerSegment 2129860864 2129991936 (212980405779777 / 100000)
      (212993585484393 / 100000) := by
  exact
    packedTile65536 2129860864 2129991936 14 6136 46150 31 _ _ (2147931 / 100000) (1073967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2129991936 :
    ThetaLowerSegment 2129991936 2130123008 (212993585484393 / 100000) (1704052403457 / 800) := by
  exact
    packedTile65536 2129991936 2130123008 14 6036 46151 31 _ _ (2147937 / 100000) (107397 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130123008 :
    ThetaLowerSegment 2130123008 2130254080 (1704052403457 / 800) (2130194917887 / 1000) := by
  exact
    packedTile65536 2130123008 2130254080 14 6025 46153 31 _ _ (2147943 / 100000) (1073973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130254080 :
    ThetaLowerSegment 2130254080 2130385152 (2130194917887 / 1000) (53258185084533 / 25000) := by
  exact
    packedTile65536 2130254080 2130385152 14 6168 46154 31 _ _ (2147949 / 100000) (134247 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130385152 :
    ThetaLowerSegment 2130385152 2130516224 (53258185084533 / 25000) (53261488639323 / 25000) := by
  exact
    packedTile65536 2130385152 2130516224 14 6152 46156 31 _ _ (429591 / 20000) (1073979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130516224 :
    ThetaLowerSegment 2130516224 2130647296 (53261488639323 / 25000) (6658095400924 / 3125) := by
  exact
    packedTile65536 2130516224 2130647296 14 6098 46157 31 _ _ (1073981 / 50000) (429593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130647296 :
    ThetaLowerSegment 2130647296 2130778368 (6658095400924 / 3125) (6658507408036 / 3125) := by
  exact
    packedTile65536 2130647296 2130778368 14 6138 46158 31 _ _ (67124 / 3125) (2147971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130778368 :
    ThetaLowerSegment 2130778368 2130909440 (6658507408036 / 3125) (26635663166371 / 12500) := by
  exact
    packedTile65536 2130778368 2130909440 14 6084 46160 31 _ _ (1073987 / 50000) (2147977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2130909440 :
    ThetaLowerSegment 2130909440 2131040512 (26635663166371 / 12500) (53274578911457 / 25000) := by
  exact
    packedTile65536 2130909440 2131040512 14 6057 46161 31 _ _ (107399 / 5000) (2147983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131040512 :
    ThetaLowerSegment 2131040512 2131171584 (53274578911457 / 25000) (21311128303731 / 10000) := by
  exact
    packedTile65536 2131040512 2131171584 14 6037 46163 31 _ _ (1073993 / 50000) (2147989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131171584 :
    ThetaLowerSegment 2131171584 2131302656 (21311128303731 / 10000) (106562137046463 / 50000) := by
  exact
    packedTile65536 2131171584 2131302656 14 6048 46164 31 _ _ (268499 / 12500) (429599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131302656 :
    ThetaLowerSegment 2131302656 2131433728 (106562137046463 / 50000)
      (106568645480403 / 50000) := by
  exact
    packedTile65536 2131302656 2131433728 14 6060 46166 31 _ _ (1073999 / 50000) (2148001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131433728 :
    ThetaLowerSegment 2131433728 2131564800 (106568645480403 / 50000)
      (106575235559743 / 50000) := by
  exact
    packedTile65536 2131433728 2131564800 14 6136 46167 31 _ _ (429601 / 20000) (268501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131564800 :
    ThetaLowerSegment 2131564800 2131695872 (106575235559743 / 50000)
      (213163473030069 / 100000) := by
  exact
    packedTile65536 2131564800 2131695872 14 6053 46168 31 _ _ (2148011 / 100000) (1074007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131695872 :
    ThetaLowerSegment 2131695872 2131826944 (213163473030069 / 100000) (13323530491567 / 6250) := by
  exact
    packedTile65536 2131695872 2131826944 14 6059 46170 31 _ _ (2148017 / 100000) (107401 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131826944 :
    ThetaLowerSegment 2131826944 2131958016 (13323530491567 / 6250) (213189494144337 / 100000) := by
  exact
    packedTile65536 2131826944 2131958016 14 6055 46171 31 _ _ (2148023 / 100000) (1074013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2131958016 :
    ThetaLowerSegment 2131958016 2132089088 (213189494144337 / 100000)
      (213202635785759 / 100000) := by
  exact
    packedTile65536 2131958016 2132089088 14 6118 46173 31 _ _ (2148029 / 100000) (67126 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132089088 :
    ThetaLowerSegment 2132089088 2132220160 (213202635785759 / 100000)
      (106607896250067 / 50000) := by
  exact
    packedTile65536 2132089088 2132220160 14 6125 46174 31 _ _ (429607 / 20000) (1074019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132220160 :
    ThetaLowerSegment 2132220160 2132351232 (106607896250067 / 50000)
      (213228867625701 / 100000) := by
  exact
    packedTile65536 2132220160 2132351232 14 6087 46175 31 _ _ (2148041 / 100000) (537011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132351232 :
    ThetaLowerSegment 2132351232 2132482304 (213228867625701 / 100000)
      (213241861168053 / 100000) := by
  exact
    packedTile65536 2132351232 2132482304 14 6049 46177 31 _ _ (134253 / 6250) (2148051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132482304 :
    ThetaLowerSegment 2132482304 2132613376 (213241861168053 / 100000)
      (213255086736531 / 100000) := by
  exact
    packedTile65536 2132482304 2132613376 14 6157 46178 31 _ _ (1074027 / 50000) (2148057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132613376 :
    ThetaLowerSegment 2132613376 2132744448 (213255086736531 / 100000)
      (213268187754471 / 100000) := by
  exact
    packedTile65536 2132613376 2132744448 14 6099 46180 31 _ _ (107403 / 5000) (2148063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132744448 :
    ThetaLowerSegment 2132744448 2132875520 (213268187754471 / 100000)
      (213281252291883 / 100000) := by
  exact
    packedTile65536 2132744448 2132875520 14 6082 46181 31 _ _ (1074033 / 50000) (2148069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2132875520 :
    ThetaLowerSegment 2132875520 2133006592 (213281252291883 / 100000)
      (213294439305891 / 100000) := by
  exact
    packedTile65536 2132875520 2133006592 14 6139 46183 31 _ _ (268509 / 12500) (85923 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133006592 :
    ThetaLowerSegment 2133006592 2133137664 (213294439305891 / 100000)
      (213307458806649 / 100000) := by
  exact
    packedTile65536 2133006592 2133137664 14 6061 46184 31 _ _ (1074039 / 50000) (2148081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133137664 :
    ThetaLowerSegment 2133137664 2133268736 (213307458806649 / 100000) (8532819391521 / 4000) := by
  exact
    packedTile65536 2133137664 2133268736 14 6064 46185 31 _ _ (537021 / 25000) (2148087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133268736 :
    ThetaLowerSegment 2133268736 2133399808 (8532819391521 / 4000) (26666692342129 / 12500) := by
  exact
    packedTile65536 2133268736 2133399808 14 6077 46187 31 _ _ (2148091 / 100000) (1074047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133399808 :
    ThetaLowerSegment 2133399808 2133530880 (26666692342129 / 12500) (26668324895849 / 12500) := by
  exact
    packedTile65536 2133399808 2133530880 14 6080 46188 31 _ _ (2148097 / 100000) (21481 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133530880 :
    ThetaLowerSegment 2133530880 2133661952 (26668324895849 / 12500) (10667982552031 / 5000) := by
  exact
    packedTile65536 2133530880 2133661952 14 6076 46190 31 _ _ (2148103 / 100000) (1074053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133661952 :
    ThetaLowerSegment 2133661952 2133793024 (10667982552031 / 5000) (4267458097463 / 2000) := by
  exact
    packedTile65536 2133661952 2133793024 14 6170 46191 31 _ _ (2148109 / 100000) (134257 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133793024 :
    ThetaLowerSegment 2133793024 2133924096 (4267458097463 / 2000) (5334649887149 / 2500) := by
  exact
    packedTile65536 2133793024 2133924096 14 6094 46192 31 _ _ (429623 / 20000) (1074059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2133924096 :
    ThetaLowerSegment 2133924096 2134055168 (5334649887149 / 2500) (213399071098487 / 100000) := by
  exact
    packedTile65536 2133924096 2134055168 14 6087 46194 31 _ _ (2148121 / 100000) (537031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134055168 :
    ThetaLowerSegment 2134055168 2134186240 (213399071098487 / 100000)
      (53353008761233 / 25000) := by
  exact
    packedTile65536 2134055168 2134186240 14 6035 46195 31 _ _ (2148127 / 100000) (214813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134186240 :
    ThetaLowerSegment 2134186240 2134317312 (53353008761233 / 25000) (53356265332377 / 25000) := by
  exact
    packedTile65536 2134186240 2134317312 14 6064 46197 31 _ _ (1074067 / 50000) (2148137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134317312 :
    ThetaLowerSegment 2134317312 2134448384 (53356265332377 / 25000) (26679777872911 / 12500) := by
  exact
    packedTile65536 2134317312 2134448384 14 6127 46198 31 _ _ (107407 / 5000) (2148143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134448384 :
    ThetaLowerSegment 2134448384 2134579456 (26679777872911 / 12500) (10672566548509 / 5000) := by
  exact
    packedTile65536 2134448384 2134579456 14 6102 46200 31 _ _ (1074073 / 50000) (2148149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134579456 :
    ThetaLowerSegment 2134579456 2134710528 (10672566548509 / 5000) (53366136600321 / 25000) := by
  exact
    packedTile65536 2134579456 2134710528 14 6152 46201 31 _ _ (268519 / 12500) (429631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134710528 :
    ThetaLowerSegment 2134710528 2134841600 (53366136600321 / 25000) (106738785341619 / 50000) := by
  exact
    packedTile65536 2134710528 2134841600 14 6063 46202 31 _ _ (1074079 / 50000) (2148161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134841600 :
    ThetaLowerSegment 2134841600 2134972672 (106738785341619 / 50000)
      (106745473650233 / 50000) := by
  exact
    packedTile65536 2134841600 2134972672 14 6227 46204 31 _ _ (537041 / 25000) (2148167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2134972672 :
    ThetaLowerSegment 2134972672 2135103744 (106745473650233 / 50000) (53375968209839 / 25000) := by
  exact
    packedTile65536 2134972672 2135103744 14 6017 46205 31 _ _ (214817 / 10000) (2148173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135103744 :
    ThetaLowerSegment 2135103744 2135234816 (53375968209839 / 25000) (26689615645351 / 12500) := by
  exact
    packedTile65536 2135103744 2135234816 14 6076 46207 31 _ _ (2148177 / 100000) (107409 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135234816 :
    ThetaLowerSegment 2135234816 2135365888 (26689615645351 / 12500) (53382502973411 / 25000) := by
  exact
    packedTile65536 2135234816 2135365888 14 6092 46208 31 _ _ (2148183 / 100000) (1074093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135365888 :
    ThetaLowerSegment 2135365888 2135496960 (53382502973411 / 25000) (106771491329413 / 50000) := by
  exact
    packedTile65536 2135365888 2135496960 14 6038 46210 31 _ _ (2148189 / 100000) (67131 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135496960 :
    ThetaLowerSegment 2135496960 2135628032 (106771491329413 / 50000)
      (213556037239841 / 100000) := by
  exact
    packedTile65536 2135496960 2135628032 14 6077 46211 31 _ _ (429639 / 20000) (1074099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135628032 :
    ThetaLowerSegment 2135628032 2135759104 (213556037239841 / 100000)
      (26696141315617 / 12500) := by
  exact
    packedTile65536 2135628032 2135759104 14 6095 46212 31 _ _ (2148201 / 100000) (537051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135759104 :
    ThetaLowerSegment 2135759104 2135890176 (26696141315617 / 12500)
      (213582159400391 / 100000) := by
  exact
    packedTile65536 2135759104 2135890176 14 6065 46214 31 _ _ (2148207 / 100000) (214821 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2135890176 :
    ThetaLowerSegment 2135890176 2136021248 (213582159400391 / 100000)
      (213595272092543 / 100000) := by
  exact
    packedTile65536 2135890176 2136021248 14 6104 46215 31 _ _ (2148213 / 100000) (268527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136021248 :
    ThetaLowerSegment 2136021248 2136152320 (213595272092543 / 100000)
      (213608328973703 / 100000) := by
  exact
    packedTile65536 2136021248 2136152320 14 6078 46217 31 _ _ (107411 / 5000) (2148223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136152320 :
    ThetaLowerSegment 2136152320 2136283392 (213608328973703 / 100000)
      (213621450338111 / 100000) := by
  exact
    packedTile65536 2136152320 2136283392 14 6108 46218 31 _ _ (1074113 / 50000) (2148229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136283392 :
    ThetaLowerSegment 2136283392 2136414464 (213621450338111 / 100000)
      (213634735004799 / 100000) := by
  exact
    packedTile65536 2136283392 2136414464 14 6184 46219 31 _ _ (268529 / 12500) (429647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136414464 :
    ThetaLowerSegment 2136414464 2136545536 (213634735004799 / 100000)
      (213647755475317 / 100000) := by
  exact
    packedTile65536 2136414464 2136545536 14 6061 46221 31 _ _ (1074119 / 50000) (2148241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136545536 :
    ThetaLowerSegment 2136545536 2136676608 (213647755475317 / 100000)
      (213660782426933 / 100000) := by
  exact
    packedTile65536 2136545536 2136676608 14 6064 46222 31 _ _ (537061 / 25000) (2148247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136676608 :
    ThetaLowerSegment 2136676608 2136807680 (213660782426933 / 100000)
      (213674039277683 / 100000) := by
  exact
    packedTile65536 2136676608 2136807680 14 6171 46224 31 _ _ (8593 / 400) (2148253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136807680 :
    ThetaLowerSegment 2136807680 2136938752 (213674039277683 / 100000)
      (213687087784627 / 100000) := by
  exact
    packedTile65536 2136807680 2136938752 14 6074 46225 31 _ _ (67133 / 3125) (2148259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2136938752 :
    ThetaLowerSegment 2136938752 2137069824 (213687087784627 / 100000) (6678132549968 / 3125) := by
  exact
    packedTile65536 2136938752 2137069824 14 6123 46227 31 _ _ (2148263 / 100000) (1074133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137069824 :
    ThetaLowerSegment 2137069824 2137200896 (6678132549968 / 3125) (53428340806507 / 25000) := by
  exact
    packedTile65536 2137069824 2137200896 14 6108 46228 31 _ _ (2148269 / 100000) (134267 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137200896 :
    ThetaLowerSegment 2137200896 2137331968 (53428340806507 / 25000)
      (213726413996653 / 100000) := by
  exact
    packedTile65536 2137200896 2137331968 14 6075 46229 31 _ _ (85931 / 4000) (1074139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137331968 :
    ThetaLowerSegment 2137331968 2137463040 (213726413996653 / 100000)
      (213739462655447 / 100000) := by
  exact
    packedTile65536 2137331968 2137463040 14 6074 46231 31 _ _ (2148281 / 100000) (537071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137463040 :
    ThetaLowerSegment 2137463040 2137594112 (213739462655447 / 100000)
      (106876331939531 / 50000) := by
  exact
    packedTile65536 2137463040 2137594112 14 6145 46232 31 _ _ (2148287 / 100000) (214829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137594112 :
    ThetaLowerSegment 2137594112 2137725184 (106876331939531 / 50000)
      (106882785411703 / 50000) := by
  exact
    packedTile65536 2137594112 2137725184 14 6008 46234 31 _ _ (2148293 / 100000) (268537 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137725184 :
    ThetaLowerSegment 2137725184 2137856256 (106882785411703 / 50000) (26722324226493 / 12500) := by
  exact
    packedTile65536 2137725184 2137856256 14 6062 46235 31 _ _ (2148299 / 100000) (1074151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137856256 :
    ThetaLowerSegment 2137856256 2137987328 (26722324226493 / 12500) (106895855681137 / 50000) := by
  exact
    packedTile65536 2137856256 2137987328 14 6106 46236 31 _ _ (429661 / 20000) (537077 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2137987328 :
    ThetaLowerSegment 2137987328 2138118400 (106895855681137 / 50000) (21380485473509 / 10000) := by
  exact
    packedTile65536 2137987328 2138118400 14 6118 46238 31 _ _ (268539 / 12500) (429663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138118400 :
    ThetaLowerSegment 2138118400 2138249472 (21380485473509 / 10000) (106908996923989 / 50000) := by
  exact
    packedTile65536 2138118400 2138249472 14 6116 46239 31 _ _ (1074159 / 50000) (2148321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138249472 :
    ThetaLowerSegment 2138249472 2138380544 (106908996923989 / 50000)
      (106915598723641 / 50000) := by
  exact
    packedTile65536 2138249472 2138380544 14 6146 46241 31 _ _ (537081 / 25000) (2148327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138380544 :
    ThetaLowerSegment 2138380544 2138511616 (106915598723641 / 50000)
      (106922123201851 / 50000) := by
  exact
    packedTile65536 2138380544 2138511616 14 6074 46242 31 _ _ (214833 / 10000) (2148333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138511616 :
    ThetaLowerSegment 2138511616 2138642688 (106922123201851 / 50000)
      (106928629437427 / 50000) := by
  exact
    packedTile65536 2138511616 2138642688 14 6057 46244 31 _ _ (134271 / 6250) (2148339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138642688 :
    ThetaLowerSegment 2138642688 2138773760 (106928629437427 / 50000) (5346756032639 / 2500) := by
  exact
    packedTile65536 2138642688 2138773760 14 6043 46245 31 _ _ (1074171 / 50000) (429669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138773760 :
    ThetaLowerSegment 2138773760 2138904832 (5346756032639 / 2500) (53470787682173 / 25000) := by
  exact
    packedTile65536 2138773760 2138904832 14 6009 46246 31 _ _ (537087 / 25000) (2148351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2138904832 :
    ThetaLowerSegment 2138904832 2139035904 (53470787682173 / 25000) (6684259198702 / 3125) := by
  exact
    packedTile65536 2138904832 2139035904 14 6118 46248 31 _ _ (1074177 / 50000) (2148357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139035904 :
    ThetaLowerSegment 2139035904 2139166976 (6684259198702 / 3125) (213909345651539 / 100000) := by
  exact
    packedTile65536 2139035904 2139166976 14 6075 46249 31 _ _ (2148361 / 100000) (537091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139166976 :
    ThetaLowerSegment 2139166976 2139298048 (213909345651539 / 100000)
      (213922592482461 / 100000) := by
  exact
    packedTile65536 2139166976 2139298048 14 6166 46251 31 _ _ (2148367 / 100000) (214837 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139298048 :
    ThetaLowerSegment 2139298048 2139429120 (213922592482461 / 100000)
      (213935529984667 / 100000) := by
  exact
    packedTile65536 2139298048 2139429120 14 6022 46252 31 _ _ (2148373 / 100000) (268547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139429120 :
    ThetaLowerSegment 2139429120 2139560192 (213935529984667 / 100000)
      (106974322919231 / 50000) := by
  exact
    packedTile65536 2139429120 2139560192 14 6105 46253 31 _ _ (2148379 / 100000) (1074191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139560192 :
    ThetaLowerSegment 2139560192 2139691264 (106974322919231 / 50000)
      (213961912115837 / 100000) := by
  exact
    packedTile65536 2139560192 2139691264 14 6175 46255 31 _ _ (429677 / 20000) (537097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139691264 :
    ThetaLowerSegment 2139691264 2139822336 (213961912115837 / 100000)
      (21397515264957 / 10000) := by
  exact
    packedTile65536 2139691264 2139822336 14 6163 46256 31 _ _ (2148391 / 100000) (1074197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139822336 :
    ThetaLowerSegment 2139822336 2139953408 (21397515264957 / 10000) (42797645129063 / 20000) := by
  exact
    packedTile65536 2139822336 2139953408 14 6085 46258 31 _ _ (2148397 / 100000) (5371 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2139953408 :
    ThetaLowerSegment 2139953408 2140084480 (42797645129063 / 20000) (21400151351787 / 10000) := by
  exact
    packedTile65536 2139953408 2140084480 14 6185 46259 31 _ _ (2148403 / 100000) (1074203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140084480 :
    ThetaLowerSegment 2140084480 2140215552 (21400151351787 / 10000) (21401451569519 / 10000) := by
  exact
    packedTile65536 2140084480 2140215552 14 6052 46261 31 _ _ (214841 / 10000) (2148413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140215552 :
    ThetaLowerSegment 2140215552 2140346624 (21401451569519 / 10000) (107013761102827 / 50000) := by
  exact
    packedTile65536 2140215552 2140346624 14 6054 46262 31 _ _ (67138 / 3125) (2148419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140346624 :
    ThetaLowerSegment 2140346624 2140477696 (107013761102827 / 50000) (6688771961707 / 3125) := by
  exact
    packedTile65536 2140346624 2140477696 14 6135 46263 31 _ _ (1074211 / 50000) (85937 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140477696 :
    ThetaLowerSegment 2140477696 2140608768 (6688771961707 / 3125) (26756729782927 / 12500) := by
  exact
    packedTile65536 2140477696 2140608768 14 6114 46265 31 _ _ (537107 / 25000) (2148431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140608768 :
    ThetaLowerSegment 2140608768 2140739840 (26756729782927 / 12500) (26758386225541 / 12500) := by
  exact
    packedTile65536 2140608768 2140739840 14 6168 46266 31 _ _ (1074217 / 50000) (2148437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140739840 :
    ThetaLowerSegment 2140739840 2140870912 (26758386225541 / 12500) (13380015831013 / 6250) := by
  exact
    packedTile65536 2140739840 2140870912 14 6127 46268 31 _ _ (53711 / 2500) (2148443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2140870912 :
    ThetaLowerSegment 2140870912 2141001984 (13380015831013 / 6250) (107046710560871 / 50000) := by
  exact
    packedTile65536 2140870912 2141001984 14 6129 46269 31 _ _ (1074223 / 50000) (2148449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141001984 :
    ThetaLowerSegment 2141001984 2141133056 (107046710560871 / 50000)
      (107053271933279 / 50000) := by
  exact
    packedTile65536 2141001984 2141133056 14 6108 46270 31 _ _ (537113 / 25000) (429691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141133056 :
    ThetaLowerSegment 2141133056 2141264128 (107053271933279 / 50000) (53529919886221 / 25000) := by
  exact
    packedTile65536 2141133056 2141264128 14 6114 46272 31 _ _ (2148459 / 100000) (1074231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141264128 :
    ThetaLowerSegment 2141264128 2141395200 (53529919886221 / 25000)
      (214132808814499 / 100000) := by
  exact
    packedTile65536 2141264128 2141395200 14 6111 46273 31 _ _ (429693 / 20000) (537117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141395200 :
    ThetaLowerSegment 2141395200 2141526272 (214132808814499 / 100000)
      (107072966911919 / 50000) := by
  exact
    packedTile65536 2141395200 2141526272 14 6109 46275 31 _ _ (2148471 / 100000) (1074237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141526272 :
    ThetaLowerSegment 2141526272 2141657344 (107072966911919 / 50000)
      (107079524063723 / 50000) := by
  exact
    packedTile65536 2141526272 2141657344 14 6104 46276 31 _ _ (2148477 / 100000) (13428 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141657344 :
    ThetaLowerSegment 2141657344 2141788416 (107079524063723 / 50000)
      (107086038264179 / 50000) := by
  exact
    packedTile65536 2141657344 2141788416 14 6064 46278 31 _ _ (2148483 / 100000) (1074243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141788416 :
    ThetaLowerSegment 2141788416 2141919488 (107086038264179 / 50000)
      (214185248914417 / 100000) := by
  exact
    packedTile65536 2141788416 2141919488 14 6131 46279 31 _ _ (2148489 / 100000) (537123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2141919488 :
    ThetaLowerSegment 2141919488 2142050560 (214185248914417 / 100000)
      (107099219262611 / 50000) := by
  exact
    packedTile65536 2141919488 2142050560 14 6139 46280 31 _ _ (429699 / 20000) (1074249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142050560 :
    ThetaLowerSegment 2142050560 2142181632 (107099219262611 / 50000)
      (214211598093847 / 100000) := by
  exact
    packedTile65536 2142050560 2142181632 14 6125 46282 31 _ _ (2148501 / 100000) (268563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142181632 :
    ThetaLowerSegment 2142181632 2142312704 (214211598093847 / 100000)
      (214224712586679 / 100000) := by
  exact
    packedTile65536 2142181632 2142312704 14 6104 46283 31 _ _ (537127 / 25000) (2148511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142312704 :
    ThetaLowerSegment 2142312704 2142443776 (214224712586679 / 100000)
      (42847535344031 / 20000) := by
  exact
    packedTile65536 2142312704 2142443776 14 6034 46285 31 _ _ (1074257 / 50000) (2148517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142443776 :
    ThetaLowerSegment 2142443776 2142574848 (42847535344031 / 20000) (42850159546359 / 20000) := by
  exact
    packedTile65536 2142443776 2142574848 14 6107 46286 31 _ _ (53713 / 2500) (2148523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142574848 :
    ThetaLowerSegment 2142574848 2142705920 (42850159546359 / 20000)
      (214263998275539 / 100000) := by
  exact
    packedTile65536 2142574848 2142705920 14 6144 46287 31 _ _ (1074263 / 50000) (2148529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142705920 :
    ThetaLowerSegment 2142705920 2142836992 (214263998275539 / 100000)
      (214277063498631 / 100000) := by
  exact
    packedTile65536 2142705920 2142836992 14 6081 46289 31 _ _ (537133 / 25000) (429707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142836992 :
    ThetaLowerSegment 2142836992 2142968064 (214277063498631 / 100000)
      (214290081490373 / 100000) := by
  exact
    packedTile65536 2142836992 2142968064 14 6059 46290 31 _ _ (1074269 / 50000) (2148541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2142968064 :
    ThetaLowerSegment 2142968064 2143099136 (214290081490373 / 100000)
      (214303295035973 / 100000) := by
  exact
    packedTile65536 2142968064 2143099136 14 6150 46292 31 _ _ (67142 / 3125) (2148547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143099136 :
    ThetaLowerSegment 2143099136 2143230208 (214303295035973 / 100000)
      (214316500024273 / 100000) := by
  exact
    packedTile65536 2143099136 2143230208 14 6146 46293 31 _ _ (42971 / 2000) (2148553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143230208 :
    ThetaLowerSegment 2143230208 2143361280 (214316500024273 / 100000)
      (214329765209017 / 100000) := by
  exact
    packedTile65536 2143230208 2143361280 14 6174 46295 31 _ _ (537139 / 25000) (2148559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143361280 :
    ThetaLowerSegment 2143361280 2143492352 (214329765209017 / 100000)
      (214342708152529 / 100000) := by
  exact
    packedTile65536 2143361280 2143492352 14 6024 46296 31 _ _ (2148563 / 100000) (1074283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143492352 :
    ThetaLowerSegment 2143492352 2143623424 (214342708152529 / 100000)
      (107177891097447 / 50000) := by
  exact
    packedTile65536 2143492352 2143623424 14 6085 46297 31 _ _ (2148569 / 100000) (537143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143623424 :
    ThetaLowerSegment 2143623424 2143754496 (107177891097447 / 50000)
      (214368882056669 / 100000) := by
  exact
    packedTile65536 2143623424 2143754496 14 6097 46299 31 _ _ (85943 / 4000) (1074289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143754496 :
    ThetaLowerSegment 2143754496 2143885568 (214368882056669 / 100000)
      (214382031372389 / 100000) := by
  exact
    packedTile65536 2143754496 2143885568 14 6120 46300 31 _ _ (2148581 / 100000) (268573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2143885568 :
    ThetaLowerSegment 2143885568 2144016640 (214382031372389 / 100000)
      (53598793569767 / 25000) := by
  exact
    packedTile65536 2143885568 2144016640 14 6117 46302 31 _ _ (2148587 / 100000) (214859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144016640 :
    ThetaLowerSegment 2144016640 2144147712 (53598793569767 / 25000)
      (214408287142147 / 100000) := by
  exact
    packedTile65536 2144016640 2144147712 14 6103 46303 31 _ _ (2148593 / 100000) (537149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144147712 :
    ThetaLowerSegment 2144147712 2144278784 (214408287142147 / 100000)
      (214421372110057 / 100000) := by
  exact
    packedTile65536 2144147712 2144278784 14 6090 46304 31 _ _ (2148599 / 100000) (1074301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144278784 :
    ThetaLowerSegment 2144278784 2144409856 (214421372110057 / 100000)
      (53608625558803 / 25000) := by
  exact
    packedTile65536 2144278784 2144409856 14 6111 46306 31 _ _ (429721 / 20000) (67144 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144409856 :
    ThetaLowerSegment 2144409856 2144540928 (53608625558803 / 25000) (53611923678223 / 25000) := by
  exact
    packedTile65536 2144409856 2144540928 14 6140 46307 31 _ _ (537153 / 25000) (429723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144540928 :
    ThetaLowerSegment 2144540928 2144672000 (53611923678223 / 25000) (107230371635003 / 50000) := by
  exact
    packedTile65536 2144540928 2144672000 14 6073 46309 31 _ _ (1074309 / 50000) (2148621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144672000 :
    ThetaLowerSegment 2144672000 2144803072 (107230371635003 / 50000)
      (107236944275819 / 50000) := by
  exact
    packedTile65536 2144672000 2144803072 14 6118 46310 31 _ _ (134289 / 6250) (2148627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144803072 :
    ThetaLowerSegment 2144803072 2144934144 (107236944275819 / 50000)
      (107243555610329 / 50000) := by
  exact
    packedTile65536 2144803072 2144934144 14 6154 46312 31 _ _ (214863 / 10000) (2148633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2144934144 :
    ThetaLowerSegment 2144934144 2145065216 (107243555610329 / 50000)
      (107250059531501 / 50000) := by
  exact
    packedTile65536 2144934144 2145065216 14 6054 46313 31 _ _ (537159 / 25000) (2148639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145065216 :
    ThetaLowerSegment 2145065216 2145196288 (107250059531501 / 50000) (2145131591713 / 1000) := by
  exact
    packedTile65536 2145065216 2145196288 14 6069 46314 31 _ _ (1074321 / 50000) (429729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145196288 :
    ThetaLowerSegment 2145196288 2145327360 (2145131591713 / 1000) (53631616974253 / 25000) := by
  exact
    packedTile65536 2145196288 2145327360 14 6194 46316 31 _ _ (268581 / 12500) (2148651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145327360 :
    ThetaLowerSegment 2145327360 2145458432 (53631616974253 / 25000) (6704362111823 / 3125) := by
  exact
    packedTile65536 2145327360 2145458432 14 6106 46317 31 _ _ (1074327 / 50000) (2148657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145458432 :
    ThetaLowerSegment 2145458432 2145589504 (6704362111823 / 3125) (26819097006677 / 12500) := by
  exact
    packedTile65536 2145458432 2145589504 14 6138 46319 31 _ _ (107433 / 5000) (2148663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145589504 :
    ThetaLowerSegment 2145589504 2145720576 (26819097006677 / 12500) (107282913528387 / 50000) := by
  exact
    packedTile65536 2145589504 2145720576 14 6074 46320 31 _ _ (2148667 / 100000) (214867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145720576 :
    ThetaLowerSegment 2145720576 2145851648 (107282913528387 / 50000)
      (214579073625819 / 100000) := by
  exact
    packedTile65536 2145720576 2145851648 14 6165 46321 31 _ _ (2148673 / 100000) (537169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145851648 :
    ThetaLowerSegment 2145851648 2145982720 (214579073625819 / 100000)
      (53648072537587 / 25000) := by
  exact
    packedTile65536 2145851648 2145982720 14 6151 46323 31 _ _ (2148679 / 100000) (1074341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2145982720 :
    ThetaLowerSegment 2145982720 2146113792 (53648072537587 / 25000) (13412841617923 / 6250) := by
  exact
    packedTile65536 2145982720 2146113792 14 6132 46324 31 _ _ (429737 / 20000) (134293 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146113792 :
    ThetaLowerSegment 2146113792 2146244864 (13412841617923 / 6250) (214618497697683 / 100000) := by
  exact
    packedTile65536 2146113792 2146244864 14 6065 46326 31 _ _ (2148691 / 100000) (1074347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146244864 :
    ThetaLowerSegment 2146244864 2146375936 (214618497697683 / 100000)
      (26828957308351 / 12500) := by
  exact
    packedTile65536 2146244864 2146375936 14 6125 46327 31 _ _ (2148697 / 100000) (21487 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146375936 :
    ThetaLowerSegment 2146375936 2146507008 (26828957308351 / 12500)
      (214644488372421 / 100000) := by
  exact
    packedTile65536 2146375936 2146507008 14 5971 46328 31 _ _ (2148703 / 100000) (1074353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146507008 :
    ThetaLowerSegment 2146507008 2146638080 (214644488372421 / 100000)
      (107328871879121 / 50000) := by
  exact
    packedTile65536 2146507008 2146638080 14 6169 46330 31 _ _ (2148709 / 100000) (268589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146638080 :
    ThetaLowerSegment 2146638080 2146769152 (107328871879121 / 50000) (53667709506863 / 25000) := by
  exact
    packedTile65536 2146638080 2146769152 14 6094 46331 31 _ _ (429743 / 20000) (1074359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146769152 :
    ThetaLowerSegment 2146769152 2146900224 (53667709506863 / 25000)
      (214684136461721 / 100000) := by
  exact
    packedTile65536 2146769152 2146900224 14 6189 46333 31 _ _ (2148721 / 100000) (537181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2146900224 :
    ThetaLowerSegment 2146900224 2147031296 (214684136461721 / 100000)
      (214697243702521 / 100000) := by
  exact
    packedTile65536 2146900224 2147031296 14 6100 46334 31 _ _ (268591 / 12500) (2148731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147031296 :
    ThetaLowerSegment 2147031296 2147162368 (214697243702521 / 100000)
      (214710140403989 / 100000) := by
  exact
    packedTile65536 2147031296 2147162368 14 6002 46336 31 _ _ (1074367 / 50000) (2148737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147162368 :
    ThetaLowerSegment 2147162368 2147293440 (214710140403989 / 100000)
      (214723318626409 / 100000) := by
  exact
    packedTile65536 2147162368 2147293440 14 6133 46337 31 _ _ (107437 / 5000) (2148743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147293440 :
    ThetaLowerSegment 2147293440 2147424512 (214723318626409 / 100000)
      (214736537711801 / 100000) := by
  exact
    packedTile65536 2147293440 2147424512 14 6152 46338 31 _ _ (1074373 / 50000) (2148749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147424512 :
    ThetaLowerSegment 2147424512 2147555584 (214736537711801 / 100000)
      (214749544107657 / 100000) := by
  exact
    packedTile65536 2147424512 2147555584 14 6053 46340 31 _ _ (134297 / 6250) (429751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147555584 :
    ThetaLowerSegment 2147555584 2147686656 (214749544107657 / 100000)
      (214762615002571 / 100000) := by
  exact
    packedTile65536 2147555584 2147686656 14 6083 46341 31 _ _ (1074379 / 50000) (2148761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147686656 :
    ThetaLowerSegment 2147686656 2147817728 (214762615002571 / 100000)
      (214775819157351 / 100000) := by
  exact
    packedTile65536 2147686656 2147817728 14 6145 46343 31 _ _ (537191 / 25000) (2148767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147817728 :
    ThetaLowerSegment 2147817728 2147948800 (214775819157351 / 100000)
      (214788963183441 / 100000) := by
  exact
    packedTile65536 2147817728 2147948800 14 6117 46344 31 _ _ (214877 / 10000) (2148773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2147948800 :
    ThetaLowerSegment 2147948800 2148079872 (214788963183441 / 100000) (8592085751017 / 4000) := by
  exact
    packedTile65536 2147948800 2148079872 14 6134 46345 31 _ _ (268597 / 12500) (2148779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148079872 :
    ThetaLowerSegment 2148079872 2148210944 (8592085751017 / 4000) (21481524060781 / 10000) := by
  exact
    packedTile65536 2148079872 2148210944 14 6095 46347 31 _ _ (2148783 / 100000) (1074393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148210944 :
    ThetaLowerSegment 2148210944 2148342016 (21481524060781 / 10000) (107414101051529 / 50000) := by
  exact
    packedTile65536 2148210944 2148342016 14 6032 46348 31 _ _ (2148789 / 100000) (268599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148342016 :
    ThetaLowerSegment 2148342016 2148473088 (107414101051529 / 50000)
      (214841415043513 / 100000) := by
  exact
    packedTile65536 2148342016 2148473088 14 6149 46350 31 _ _ (429759 / 20000) (1074399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148473088 :
    ThetaLowerSegment 2148473088 2148604160 (214841415043513 / 100000)
      (214854694633693 / 100000) := by
  exact
    packedTile65536 2148473088 2148604160 14 6180 46351 31 _ _ (2148801 / 100000) (537201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148604160 :
    ThetaLowerSegment 2148604160 2148735232 (214854694633693 / 100000)
      (214867699213657 / 100000) := by
  exact
    packedTile65536 2148604160 2148735232 14 6052 46353 31 _ _ (2148807 / 100000) (214881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148735232 :
    ThetaLowerSegment 2148735232 2148866304 (214867699213657 / 100000)
      (107440335798869 / 50000) := by
  exact
    packedTile65536 2148735232 2148866304 14 6037 46354 31 _ _ (2148813 / 100000) (134301 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148866304 :
    ThetaLowerSegment 2148866304 2148997376 (107440335798869 / 50000)
      (107446911185009 / 50000) := by
  exact
    packedTile65536 2148866304 2148997376 14 6120 46355 31 _ _ (2148819 / 100000) (1074411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2148997376 :
    ThetaLowerSegment 2148997376 2149128448 (107446911185009 / 50000)
      (107453366255309 / 50000) := by
  exact
    packedTile65536 2148997376 2149128448 14 6008 46357 31 _ _ (85953 / 4000) (537207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149128448 :
    ThetaLowerSegment 2149128448 2149259520 (107453366255309 / 50000) (21491982318907 / 10000) := by
  exact
    packedTile65536 2149128448 2149259520 14 6092 46358 31 _ _ (2148831 / 100000) (1074417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149259520 :
    ThetaLowerSegment 2149259520 2149390592 (21491982318907 / 10000)
      (214932761336647 / 100000) := by
  exact
    packedTile65536 2149259520 2149390592 14 6021 46360 31 _ _ (2148837 / 100000) (53721 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149390592 :
    ThetaLowerSegment 2149390592 2149521664 (214932761336647 / 100000)
      (214945903666551 / 100000) := by
  exact
    packedTile65536 2149390592 2149521664 14 6116 46361 31 _ _ (537211 / 25000) (2148847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149521664 :
    ThetaLowerSegment 2149521664 2149652736 (214945903666551 / 100000)
      (214959213643451 / 100000) := by
  exact
    packedTile65536 2149521664 2149652736 14 6194 46362 31 _ _ (42977 / 2000) (2148853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149652736 :
    ThetaLowerSegment 2149652736 2149783808 (214959213643451 / 100000)
      (214972252901659 / 100000) := by
  exact
    packedTile65536 2149652736 2149783808 14 6068 46364 31 _ _ (268607 / 12500) (2148859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149783808 :
    ThetaLowerSegment 2149783808 2149914880 (214972252901659 / 100000)
      (214985186902037 / 100000) := by
  exact
    packedTile65536 2149783808 2149914880 14 6019 46365 31 _ _ (1074431 / 50000) (429773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2149914880 :
    ThetaLowerSegment 2149914880 2150045952 (214985186902037 / 100000)
      (214998462608541 / 100000) := by
  exact
    packedTile65536 2149914880 2150045952 14 6178 46367 31 _ _ (537217 / 25000) (2148871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150045952 :
    ThetaLowerSegment 2150045952 2150177024 (214998462608541 / 100000)
      (215011587930933 / 100000) := by
  exact
    packedTile65536 2150045952 2150177024 14 6108 46368 31 _ _ (1074437 / 50000) (2148877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150177024 :
    ThetaLowerSegment 2150177024 2150308096 (215011587930933 / 100000)
      (215024930326853 / 100000) := by
  exact
    packedTile65536 2150177024 2150308096 14 6209 46370 31 _ _ (26861 / 1250) (2148883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150308096 :
    ThetaLowerSegment 2150308096 2150439168 (215024930326853 / 100000)
      (215038083658059 / 100000) := by
  exact
    packedTile65536 2150308096 2150439168 14 6121 46371 31 _ _ (1074443 / 50000) (2148889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150439168 :
    ThetaLowerSegment 2150439168 2150570240 (215038083658059 / 100000)
      (215051060816847 / 100000) := by
  exact
    packedTile65536 2150439168 2150570240 14 6039 46372 31 _ _ (537223 / 25000) (429779 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150570240 :
    ThetaLowerSegment 2150570240 2150701312 (215051060816847 / 100000)
      (215064070245339 / 100000) := by
  exact
    packedTile65536 2150570240 2150701312 14 6054 46374 31 _ _ (1074449 / 50000) (2148901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150701312 :
    ThetaLowerSegment 2150701312 2150832384 (215064070245339 / 100000)
      (215077247324667 / 100000) := by
  exact
    packedTile65536 2150701312 2150832384 14 6132 46375 31 _ _ (268613 / 12500) (2148907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150832384 :
    ThetaLowerSegment 2150832384 2150963456 (215077247324667 / 100000)
      (107545114448009 / 50000) := by
  exact
    packedTile65536 2150832384 2150963456 14 6041 46377 31 _ _ (2148911 / 100000) (1074457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2150963456 :
    ThetaLowerSegment 2150963456 2151094528 (107545114448009 / 50000) (43020650696391 / 20000) := by
  exact
    packedTile65536 2150963456 2151094528 14 6061 46378 31 _ _ (2148917 / 100000) (53723 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151094528 :
    ThetaLowerSegment 2151094528 2151225600 (43020650696391 / 20000)
      (215116430677791 / 100000) := by
  exact
    packedTile65536 2151094528 2151225600 14 6132 46379 31 _ _ (2148923 / 100000) (1074463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151225600 :
    ThetaLowerSegment 2151225600 2151356672 (215116430677791 / 100000)
      (215129526251117 / 100000) := by
  exact
    packedTile65536 2151225600 2151356672 14 6094 46381 31 _ _ (2148929 / 100000) (537233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151356672 :
    ThetaLowerSegment 2151356672 2151487744 (215129526251117 / 100000)
      (215142720712017 / 100000) := by
  exact
    packedTile65536 2151356672 2151487744 14 6140 46382 31 _ _ (429787 / 20000) (1074469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151487744 :
    ThetaLowerSegment 2151487744 2151618816 (215142720712017 / 100000)
      (26894486983661 / 12500) := by
  exact
    packedTile65536 2151487744 2151618816 14 6131 46384 31 _ _ (2148941 / 100000) (134309 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151618816 :
    ThetaLowerSegment 2151618816 2151749888 (26894486983661 / 12500) (53792246813603 / 25000) := by
  exact
    packedTile65536 2151618816 2151749888 14 6092 46385 31 _ _ (2148947 / 100000) (42979 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151749888 :
    ThetaLowerSegment 2151749888 2151880960 (53792246813603 / 25000)
      (215182029250169 / 100000) := by
  exact
    packedTile65536 2151749888 2151880960 14 6069 46386 31 _ _ (2148953 / 100000) (537239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2151880960 :
    ThetaLowerSegment 2151880960 2152012032 (215182029250169 / 100000)
      (215195245348019 / 100000) := by
  exact
    packedTile65536 2151880960 2152012032 14 6150 46388 31 _ _ (2148959 / 100000) (1074481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152012032 :
    ThetaLowerSegment 2152012032 2152143104 (215195245348019 / 100000)
      (215208332544869 / 100000) := by
  exact
    packedTile65536 2152012032 2152143104 14 6090 46389 31 _ _ (429793 / 20000) (268621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152143104 :
    ThetaLowerSegment 2152143104 2152274176 (215208332544869 / 100000)
      (215221501439157 / 100000) := by
  exact
    packedTile65536 2152143104 2152274176 14 6128 46391 31 _ _ (2148971 / 100000) (1074487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152274176 :
    ThetaLowerSegment 2152274176 2152405248 (215221501439157 / 100000)
      (43046907427941 / 20000) := by
  exact
    packedTile65536 2152274176 2152405248 14 6066 46392 31 _ _ (1074489 / 50000) (2148981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152405248 :
    ThetaLowerSegment 2152405248 2152536320 (43046907427941 / 20000)
      (215247605111409 / 100000) := by
  exact
    packedTile65536 2152405248 2152536320 14 6081 46394 31 _ _ (268623 / 12500) (2148987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152536320 :
    ThetaLowerSegment 2152536320 2152667392 (215247605111409 / 100000)
      (215261055639819 / 100000) := by
  exact
    packedTile65536 2152536320 2152667392 14 6259 46395 31 _ _ (214899 / 10000) (2148993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152667392 :
    ThetaLowerSegment 2152667392 2152798464 (215261055639819 / 100000)
      (215274149472447 / 100000) := by
  exact
    packedTile65536 2152667392 2152798464 14 6093 46396 31 _ _ (537249 / 25000) (2148999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152798464 :
    ThetaLowerSegment 2152798464 2152929536 (215274149472447 / 100000)
      (215287157381553 / 100000) := by
  exact
    packedTile65536 2152798464 2152929536 14 6053 46398 31 _ _ (1074501 / 50000) (429801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2152929536 :
    ThetaLowerSegment 2152929536 2153060608 (215287157381553 / 100000)
      (43060042091229 / 20000) := by
  exact
    packedTile65536 2152929536 2153060608 14 6074 46399 31 _ _ (134313 / 6250) (2149011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153060608 :
    ThetaLowerSegment 2153060608 2153191680 (43060042091229 / 20000)
      (215313194798733 / 100000) := by
  exact
    packedTile65536 2153060608 2153191680 14 6042 46401 31 _ _ (1074507 / 50000) (2149017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153191680 :
    ThetaLowerSegment 2153191680 2153322752 (215313194798733 / 100000)
      (215326295224653 / 100000) := by
  exact
    packedTile65536 2153191680 2153322752 14 6096 46402 31 _ _ (107451 / 5000) (2149023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153322752 :
    ThetaLowerSegment 2153322752 2153339136 (215326295224653 / 100000)
      (215327883354867 / 100000) := by
  exact
    packedTile65536 2153322752 2153339136 11 739 46403 31 _ _ (1074513 / 50000) (2149029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153339136 :
    ThetaLowerSegment 2153339136 2153341184 (215327883354867 / 100000)
      (215328072469243 / 100000) := by
  exact
    packedTile65536 2153339136 2153341184 8 88 46404 31 _ _ (2149027 / 100000) (214903 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2121341184_2153341184 :
    ThetaLowerSegment 2121341184 2153341184 (212129564250213 / 100000)
      (215328072469243 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2121341184 cell2121472256)
                  (ThetaLowerSegment.join cell2121603328 cell2121734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2121865472 cell2121996544)
                  (ThetaLowerSegment.join cell2122127616 cell2122258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2122389760 cell2122520832)
                  (ThetaLowerSegment.join cell2122651904 cell2122782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2122914048 cell2123045120)
                  (ThetaLowerSegment.join cell2123176192 cell2123307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2123438336 cell2123569408)
                  (ThetaLowerSegment.join cell2123700480 cell2123831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2123962624 cell2124093696)
                  (ThetaLowerSegment.join cell2124224768 cell2124355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2124486912 cell2124617984)
                  (ThetaLowerSegment.join cell2124749056 cell2124880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2125011200 cell2125142272)
                  (ThetaLowerSegment.join cell2125273344 cell2125404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2125535488 cell2125666560)
                  (ThetaLowerSegment.join cell2125797632 cell2125928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2126059776 cell2126190848)
                  (ThetaLowerSegment.join cell2126321920 cell2126452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2126584064 cell2126715136)
                  (ThetaLowerSegment.join cell2126846208 cell2126977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2127108352 cell2127239424)
                  (ThetaLowerSegment.join cell2127370496 cell2127501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2127632640 cell2127763712)
                  (ThetaLowerSegment.join cell2127894784 cell2128025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2128156928 cell2128288000)
                  (ThetaLowerSegment.join cell2128419072 cell2128550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2128681216 cell2128812288)
                  (ThetaLowerSegment.join cell2128943360 cell2129074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2129205504 cell2129336576)
                  (ThetaLowerSegment.join cell2129467648 cell2129598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2129729792 cell2129860864)
                  (ThetaLowerSegment.join cell2129991936 cell2130123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2130254080 cell2130385152)
                  (ThetaLowerSegment.join cell2130516224 cell2130647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2130778368 cell2130909440)
                  (ThetaLowerSegment.join cell2131040512 cell2131171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2131302656 cell2131433728)
                  (ThetaLowerSegment.join cell2131564800 cell2131695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2131826944 cell2131958016)
                  (ThetaLowerSegment.join cell2132089088 cell2132220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2132351232 cell2132482304)
                  (ThetaLowerSegment.join cell2132613376 cell2132744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2132875520 cell2133006592)
                  (ThetaLowerSegment.join cell2133137664 cell2133268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2133399808 cell2133530880)
                  (ThetaLowerSegment.join cell2133661952 cell2133793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2133924096 cell2134055168)
                  (ThetaLowerSegment.join cell2134186240 cell2134317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2134448384 cell2134579456)
                  (ThetaLowerSegment.join cell2134710528 cell2134841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2134972672 cell2135103744)
                  (ThetaLowerSegment.join cell2135234816 cell2135365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2135496960 cell2135628032)
                  (ThetaLowerSegment.join cell2135759104 cell2135890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2136021248 cell2136152320)
                  (ThetaLowerSegment.join cell2136283392 cell2136414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2136545536 cell2136676608)
                  (ThetaLowerSegment.join cell2136807680 cell2136938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2137069824 cell2137200896)
                  (ThetaLowerSegment.join cell2137331968 cell2137463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2137594112 cell2137725184)
                  (ThetaLowerSegment.join cell2137856256 cell2137987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2138118400 cell2138249472)
                  (ThetaLowerSegment.join cell2138380544 cell2138511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2138642688 cell2138773760)
                  (ThetaLowerSegment.join cell2138904832 cell2139035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2139166976 cell2139298048)
                  (ThetaLowerSegment.join cell2139429120 cell2139560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2139691264 cell2139822336)
                  (ThetaLowerSegment.join cell2139953408 cell2140084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2140215552 cell2140346624)
                  (ThetaLowerSegment.join cell2140477696 cell2140608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2140739840 cell2140870912)
                  (ThetaLowerSegment.join cell2141001984 cell2141133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2141264128 cell2141395200)
                  (ThetaLowerSegment.join cell2141526272 cell2141657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2141788416 cell2141919488)
                  (ThetaLowerSegment.join cell2142050560 cell2142181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2142312704 cell2142443776)
                  (ThetaLowerSegment.join cell2142574848 cell2142705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2142836992 cell2142968064)
                  (ThetaLowerSegment.join cell2143099136 cell2143230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2143361280 cell2143492352)
                  (ThetaLowerSegment.join cell2143623424 cell2143754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2143885568 cell2144016640)
                  (ThetaLowerSegment.join cell2144147712 cell2144278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2144409856 cell2144540928)
                  (ThetaLowerSegment.join cell2144672000 cell2144803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2144934144 cell2145065216)
                  (ThetaLowerSegment.join cell2145196288 cell2145327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2145458432 cell2145589504)
                  (ThetaLowerSegment.join cell2145720576 cell2145851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2145982720 cell2146113792)
                  (ThetaLowerSegment.join cell2146244864 cell2146375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2146507008 cell2146638080)
                  (ThetaLowerSegment.join cell2146769152 cell2146900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2147031296 cell2147162368)
                  (ThetaLowerSegment.join cell2147293440 cell2147424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2147555584 cell2147686656)
                  (ThetaLowerSegment.join cell2147817728 cell2147948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2148079872 cell2148210944)
                  (ThetaLowerSegment.join cell2148342016 cell2148473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2148604160 cell2148735232)
                  (ThetaLowerSegment.join cell2148866304 cell2148997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2149128448 cell2149259520)
                  (ThetaLowerSegment.join cell2149390592 cell2149521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2149652736 cell2149783808)
                  (ThetaLowerSegment.join cell2149914880 cell2150045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2150177024 cell2150308096)
                  (ThetaLowerSegment.join cell2150439168 cell2150570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2150701312 cell2150832384)
                  (ThetaLowerSegment.join cell2150963456 cell2151094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2151225600 cell2151356672)
                  (ThetaLowerSegment.join cell2151487744 cell2151618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2151749888 cell2151880960)
                  (ThetaLowerSegment.join cell2152012032 cell2152143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2152274176 cell2152405248)
                  (ThetaLowerSegment.join cell2152536320 cell2152667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2152798464 cell2152929536)
                (ThetaLowerSegment.join cell2153060608 cell2153191680))
              (ThetaLowerSegment.join cell2153322752 cell2153339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
