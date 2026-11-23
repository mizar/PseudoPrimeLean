/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3497341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3465341184 :
    ThetaLowerSegment 3465341184 3465472256 (173263125923279 / 50000)
      (173269665219341 / 50000) := by
  exact
    packedTile65536 3465341184 3465472256 14 5954 58867 32 _ _ (1098303 / 50000) (2196609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465472256 :
    ThetaLowerSegment 3465472256 3465603328 (173269665219341 / 50000)
      (173276191347651 / 50000) := by
  exact
    packedTile65536 3465472256 3465603328 14 5942 58868 32 _ _ (219661 / 10000) (2196613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465603328 :
    ThetaLowerSegment 3465603328 3465734400 (173276191347651 / 50000) (43320685138073 / 12500) := by
  exact
    packedTile65536 3465603328 3465734400 14 5963 58869 32 _ _ (1098307 / 50000) (2196617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465734400 :
    ThetaLowerSegment 3465734400 3465865472 (43320685138073 / 12500) (43322345781281 / 12500) := by
  exact
    packedTile65536 3465734400 3465865472 14 6048 58870 32 _ _ (1098309 / 50000) (2196621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465865472 :
    ThetaLowerSegment 3465865472 3465996544 (43322345781281 / 12500) (43323966887579 / 12500) := by
  exact
    packedTile65536 3465865472 3465996544 14 5904 58871 32 _ _ (2196621 / 100000) (137289 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3465996544 :
    ThetaLowerSegment 3465996544 3466127616 (43323966887579 / 12500)
      (346604754497007 / 100000) := by
  exact
    packedTile65536 3465996544 3466127616 14 5927 58872 32 _ _ (17573 / 800) (549157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466127616 :
    ThetaLowerSegment 3466127616 3466258688 (346604754497007 / 100000)
      (34661794964741 / 10000) := by
  exact
    packedTile65536 3466127616 3466258688 14 6007 58873 32 _ _ (2196629 / 100000) (274579 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466258688 :
    ThetaLowerSegment 3466258688 3466389760 (34661794964741 / 10000)
      (346631021810393 / 100000) := by
  exact
    packedTile65536 3466258688 3466389760 14 5951 58874 32 _ _ (2196633 / 100000) (549159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466389760 :
    ThetaLowerSegment 3466389760 3466520832 (346631021810393 / 100000)
      (346644181856669 / 100000) := by
  exact
    packedTile65536 3466389760 3466520832 14 5991 58876 32 _ _ (549159 / 25000) (2196639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466520832 :
    ThetaLowerSegment 3466520832 3466651904 (346644181856669 / 100000)
      (346657095903229 / 100000) := by
  exact
    packedTile65536 3466520832 3466651904 14 5879 58877 32 _ _ (13729 / 625) (2196643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466651904 :
    ThetaLowerSegment 3466651904 3466782976 (346657095903229 / 100000) (13866809624837 / 4000) := by
  exact
    packedTile65536 3466651904 3466782976 14 5984 58878 32 _ _ (549161 / 25000) (2196647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466782976 :
    ThetaLowerSegment 3466782976 3466914048 (13866809624837 / 4000) (346683282120101 / 100000) := by
  exact
    packedTile65536 3466782976 3466914048 14 5937 58879 32 _ _ (274581 / 12500) (2196651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3466914048 :
    ThetaLowerSegment 3466914048 3467045120 (346683282120101 / 100000)
      (346696354396153 / 100000) := by
  exact
    packedTile65536 3466914048 3467045120 14 5951 58880 32 _ _ (549163 / 25000) (439331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467045120 :
    ThetaLowerSegment 3467045120 3467176192 (346696354396153 / 100000)
      (86677373147427 / 25000) := by
  exact
    packedTile65536 3467045120 3467176192 14 5981 58881 32 _ _ (439331 / 20000) (1098329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467176192 :
    ThetaLowerSegment 3467176192 3467307264 (86677373147427 / 25000) (17336130112531 / 5000) := by
  exact
    packedTile65536 3467176192 3467307264 14 5968 58882 32 _ _ (2196659 / 100000) (1098331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467307264 :
    ThetaLowerSegment 3467307264 3467438336 (17336130112531 / 5000) (346735885471781 / 100000) := by
  exact
    packedTile65536 3467307264 3467438336 14 6047 58883 32 _ _ (2196663 / 100000) (1098333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467438336 :
    ThetaLowerSegment 3467438336 3467569408 (346735885471781 / 100000)
      (346749039113777 / 100000) := by
  exact
    packedTile65536 3467438336 3467569408 14 5988 58884 32 _ _ (2196667 / 100000) (219667 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467569408 :
    ThetaLowerSegment 3467569408 3467700480 (346749039113777 / 100000)
      (346762159823687 / 100000) := by
  exact
    packedTile65536 3467569408 3467700480 14 5973 58886 32 _ _ (219667 / 10000) (2196673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467700480 :
    ThetaLowerSegment 3467700480 3467831552 (346762159823687 / 100000)
      (346775260787423 / 100000) := by
  exact
    packedTile65536 3467700480 3467831552 14 5964 58887 32 _ _ (1098337 / 50000) (2196677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467831552 :
    ThetaLowerSegment 3467831552 3467962624 (346775260787423 / 100000)
      (346788291481319 / 100000) := by
  exact
    packedTile65536 3467831552 3467962624 14 5932 58888 32 _ _ (1098339 / 50000) (2196681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3467962624 :
    ThetaLowerSegment 3467962624 3468093696 (346788291481319 / 100000)
      (346801464983273 / 100000) := by
  exact
    packedTile65536 3467962624 3468093696 14 5997 58889 32 _ _ (1098341 / 50000) (439337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468093696 :
    ThetaLowerSegment 3468093696 3468224768 (346801464983273 / 100000)
      (346814577002007 / 100000) := by
  exact
    packedTile65536 3468093696 3468224768 14 5969 58890 32 _ _ (1098343 / 50000) (2196689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468224768 :
    ThetaLowerSegment 3468224768 3468355840 (346814577002007 / 100000) (4335344135963 / 1250) := by
  exact
    packedTile65536 3468224768 3468355840 14 5897 58891 32 _ _ (2196689 / 100000) (549173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468355840 :
    ThetaLowerSegment 3468355840 3468486912 (4335344135963 / 1250) (346840577036767 / 100000) := by
  exact
    packedTile65536 3468355840 3468486912 14 5939 58892 32 _ _ (2196693 / 100000) (274587 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468486912 :
    ThetaLowerSegment 3468486912 3468617984 (346840577036767 / 100000)
      (173426807216731 / 50000) := by
  exact
    packedTile65536 3468486912 3468617984 14 5935 58893 32 _ _ (2196697 / 100000) (21967 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468617984 :
    ThetaLowerSegment 3468617984 3468749056 (173426807216731 / 50000) (69373316311893 / 20000) := by
  exact
    packedTile65536 3468617984 3468749056 14 5903 58894 32 _ _ (2196701 / 100000) (68647 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468749056 :
    ThetaLowerSegment 3468749056 3468880128 (69373316311893 / 20000) (69375908422613 / 20000) := by
  exact
    packedTile65536 3468749056 3468880128 14 5900 58896 32 _ _ (68647 / 3125) (2196707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3468880128 :
    ThetaLowerSegment 3468880128 3469011200 (69375908422613 / 20000)
      (346892889310873 / 100000) := by
  exact
    packedTile65536 3468880128 3469011200 14 6076 58897 32 _ _ (549177 / 25000) (2196711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469011200 :
    ThetaLowerSegment 3469011200 3469142272 (346892889310873 / 100000) (13876242431841 / 4000) := by
  exact
    packedTile65536 3469011200 3469142272 14 5996 58898 32 _ _ (274589 / 12500) (439343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469142272 :
    ThetaLowerSegment 3469142272 3469273344 (13876242431841 / 4000) (346919300403357 / 100000) := by
  exact
    packedTile65536 3469142272 3469273344 14 6027 58899 32 _ _ (549179 / 25000) (2196719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469273344 :
    ThetaLowerSegment 3469273344 3469404416 (346919300403357 / 100000)
      (346932359903757 / 100000) := by
  exact
    packedTile65536 3469273344 3469404416 14 5945 58900 32 _ _ (27459 / 1250) (2196723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469404416 :
    ThetaLowerSegment 3469404416 3469535488 (346932359903757 / 100000)
      (346945610536893 / 100000) := by
  exact
    packedTile65536 3469404416 3469535488 14 6032 58901 32 _ _ (2196723 / 100000) (1098363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469535488 :
    ThetaLowerSegment 3469535488 3469666560 (346945610536893 / 100000)
      (346958619554187 / 100000) := by
  exact
    packedTile65536 3469535488 3469666560 14 5922 58902 32 _ _ (2196727 / 100000) (219673 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469666560 :
    ThetaLowerSegment 3469666560 3469797632 (346958619554187 / 100000)
      (346971826300959 / 100000) := by
  exact
    packedTile65536 3469666560 3469797632 14 6012 58903 32 _ _ (2196731 / 100000) (1098367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469797632 :
    ThetaLowerSegment 3469797632 3469928704 (346971826300959 / 100000)
      (346984971563199 / 100000) := by
  exact
    packedTile65536 3469797632 3469928704 14 5984 58904 32 _ _ (439347 / 20000) (1098369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3469928704 :
    ThetaLowerSegment 3469928704 3470059776 (346984971563199 / 100000)
      (346998162974889 / 100000) := by
  exact
    packedTile65536 3469928704 3470059776 14 6005 58906 32 _ _ (1098369 / 50000) (2196741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470059776 :
    ThetaLowerSegment 3470059776 3470190848 (346998162974889 / 100000)
      (347011035883009 / 100000) := by
  exact
    packedTile65536 3470059776 3470190848 14 5860 58907 32 _ _ (1098371 / 50000) (439349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470190848 :
    ThetaLowerSegment 3470190848 3470321920 (347011035883009 / 100000)
      (347024172424089 / 100000) := by
  exact
    packedTile65536 3470190848 3470321920 14 5980 58908 32 _ _ (1098373 / 50000) (2196749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470321920 :
    ThetaLowerSegment 3470321920 3470452992 (347024172424089 / 100000)
      (347037212332089 / 100000) := by
  exact
    packedTile65536 3470321920 3470452992 14 5936 58909 32 _ _ (8787 / 400) (2196753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470452992 :
    ThetaLowerSegment 3470452992 3470584064 (347037212332089 / 100000)
      (69410100099407 / 20000) := by
  exact
    packedTile65536 3470452992 3470584064 14 6049 58910 32 _ _ (1098377 / 50000) (2196757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470584064 :
    ThetaLowerSegment 3470584064 3470715136 (69410100099407 / 20000)
      (347063733761203 / 100000) := by
  exact
    packedTile65536 3470584064 3470715136 14 6024 58911 32 _ _ (2196757 / 100000) (54919 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470715136 :
    ThetaLowerSegment 3470715136 3470846208 (347063733761203 / 100000)
      (347076707831669 / 100000) := by
  exact
    packedTile65536 3470715136 3470846208 14 5906 58912 32 _ _ (2196761 / 100000) (549191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470846208 :
    ThetaLowerSegment 3470846208 3470977280 (347076707831669 / 100000)
      (347089866454019 / 100000) := by
  exact
    packedTile65536 3470846208 3470977280 14 5990 58913 32 _ _ (439353 / 20000) (68649 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3470977280 :
    ThetaLowerSegment 3470977280 3471108352 (347089866454019 / 100000)
      (173551386235947 / 50000) := by
  exact
    packedTile65536 3470977280 3471108352 14 5875 58915 32 _ _ (2196769 / 100000) (549193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471108352 :
    ThetaLowerSegment 3471108352 3471239424 (173551386235947 / 50000)
      (173557866713347 / 50000) := by
  exact
    packedTile65536 3471108352 3471239424 14 5900 58916 32 _ _ (549193 / 25000) (87871 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471239424 :
    ThetaLowerSegment 3471239424 3471370496 (173557866713347 / 50000)
      (173564404318723 / 50000) := by
  exact
    packedTile65536 3471239424 3471370496 14 5952 58917 32 _ _ (274597 / 12500) (2196779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471370496 :
    ThetaLowerSegment 3471370496 3471501568 (173564404318723 / 50000)
      (173570905689133 / 50000) := by
  exact
    packedTile65536 3471370496 3471501568 14 5919 58918 32 _ _ (109839 / 5000) (2196783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471501568 :
    ThetaLowerSegment 3471501568 3471632640 (173570905689133 / 50000)
      (173577402677813 / 50000) := by
  exact
    packedTile65536 3471501568 3471632640 14 5915 58919 32 _ _ (137299 / 6250) (2196787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471632640 :
    ThetaLowerSegment 3471632640 3471763712 (173577402677813 / 50000)
      (173583975467509 / 50000) := by
  exact
    packedTile65536 3471632640 3471763712 14 5984 58920 32 _ _ (549197 / 25000) (2196791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471763712 :
    ThetaLowerSegment 3471763712 3471894784 (173583975467509 / 50000) (86795246673203 / 25000) := by
  exact
    packedTile65536 3471763712 3471894784 14 5934 58921 32 _ _ (2196791 / 100000) (1098397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3471894784 :
    ThetaLowerSegment 3471894784 3472025856 (86795246673203 / 25000) (173596984875631 / 50000) := by
  exact
    packedTile65536 3471894784 3472025856 14 5910 58922 32 _ _ (439359 / 20000) (1098399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472025856 :
    ThetaLowerSegment 3472025856 3472156928 (173596984875631 / 50000) (86801727224343 / 25000) := by
  exact
    packedTile65536 3472025856 3472156928 14 5890 58923 32 _ _ (2196799 / 100000) (1098401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472156928 :
    ThetaLowerSegment 3472156928 3472288000 (86801727224343 / 25000)
      (347219973284813 / 100000) := by
  exact
    packedTile65536 3472156928 3472288000 14 5947 58925 32 _ _ (2196803 / 100000) (1098403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472288000 :
    ThetaLowerSegment 3472288000 3472419072 (347219973284813 / 100000)
      (347232908078541 / 100000) := by
  exact
    packedTile65536 3472288000 3472419072 14 5888 58926 32 _ _ (1098403 / 50000) (2196809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472419072 :
    ThetaLowerSegment 3472419072 3472550144 (347232908078541 / 100000)
      (347246073560871 / 100000) := by
  exact
    packedTile65536 3472419072 3472550144 14 5993 58927 32 _ _ (219681 / 10000) (2196813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472550144 :
    ThetaLowerSegment 3472550144 3472681216 (347246073560871 / 100000)
      (347259210508591 / 100000) := by
  exact
    packedTile65536 3472550144 3472681216 14 5980 58928 32 _ _ (1098407 / 50000) (2196817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472681216 :
    ThetaLowerSegment 3472681216 3472812288 (347259210508591 / 100000)
      (69454490585499 / 20000) := by
  exact
    packedTile65536 3472681216 3472812288 14 6028 58929 32 _ _ (1098409 / 50000) (2196821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472812288 :
    ThetaLowerSegment 3472812288 3472943360 (69454490585499 / 20000)
      (347285550380259 / 100000) := by
  exact
    packedTile65536 3472812288 3472943360 14 5962 58930 32 _ _ (1098411 / 50000) (87873 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3472943360 :
    ThetaLowerSegment 3472943360 3473074432 (347285550380259 / 100000)
      (347298485285859 / 100000) := by
  exact
    packedTile65536 3472943360 3473074432 14 5888 58931 32 _ _ (87873 / 4000) (549207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473074432 :
    ThetaLowerSegment 3473074432 3473205504 (347298485285859 / 100000) (21706983672201 / 6250) := by
  exact
    packedTile65536 3473074432 3473205504 14 6033 58932 32 _ _ (2196829 / 100000) (68651 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473205504 :
    ThetaLowerSegment 3473205504 3473336576 (21706983672201 / 6250) (347325097696689 / 100000) := by
  exact
    packedTile65536 3473205504 3473336576 14 6081 58933 32 _ _ (2196833 / 100000) (549209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473336576 :
    ThetaLowerSegment 3473336576 3473467648 (347325097696689 / 100000)
      (86834569130463 / 25000) := by
  exact
    packedTile65536 3473336576 3473467648 14 5999 58935 32 _ _ (2196837 / 100000) (54921 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473467648 :
    ThetaLowerSegment 3473467648 3473598720 (86834569130463 / 25000) (86837804526573 / 25000) := by
  exact
    packedTile65536 3473467648 3473598720 14 5891 58936 32 _ _ (54921 / 2500) (2196843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473598720 :
    ThetaLowerSegment 3473598720 3473729792 (86837804526573 / 25000) (86841094300463 / 25000) := by
  exact
    packedTile65536 3473598720 3473729792 14 5990 58937 32 _ _ (549211 / 25000) (2196847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473729792 :
    ThetaLowerSegment 3473729792 3473860864 (86841094300463 / 25000) (17368882418031 / 5000) := by
  exact
    packedTile65536 3473729792 3473860864 14 6041 58938 32 _ _ (137303 / 6250) (2196851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473860864 :
    ThetaLowerSegment 3473860864 3473991936 (17368882418031 / 5000) (86847700777599 / 25000) := by
  exact
    packedTile65536 3473860864 3473991936 14 5988 58939 32 _ _ (549213 / 25000) (439371 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3473991936 :
    ThetaLowerSegment 3473991936 3474123008 (86847700777599 / 25000) (86850951026051 / 25000) := by
  exact
    packedTile65536 3473991936 3474123008 14 5918 58940 32 _ _ (274607 / 12500) (2196859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474123008 :
    ThetaLowerSegment 3474123008 3474254080 (86850951026051 / 25000) (21713561029423 / 6250) := by
  exact
    packedTile65536 3474123008 3474254080 14 5996 58941 32 _ _ (2196859 / 100000) (1098431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474254080 :
    ThetaLowerSegment 3474254080 3474385152 (21713561029423 / 6250) (86857484490617 / 25000) := by
  exact
    packedTile65536 3474254080 3474385152 14 5900 58942 32 _ _ (2196863 / 100000) (1098433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474385152 :
    ThetaLowerSegment 3474385152 3474516224 (86857484490617 / 25000)
      (347443064242793 / 100000) := by
  exact
    packedTile65536 3474385152 3474516224 14 5975 58943 32 _ _ (2196867 / 100000) (219687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474516224 :
    ThetaLowerSegment 3474516224 3474647296 (347443064242793 / 100000)
      (347456122444017 / 100000) := by
  exact
    packedTile65536 3474516224 3474647296 14 5944 58945 32 _ _ (2196871 / 100000) (1098437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474647296 :
    ThetaLowerSegment 3474647296 3474778368 (347456122444017 / 100000)
      (347469314672387 / 100000) := by
  exact
    packedTile65536 3474647296 3474778368 14 6005 58946 32 _ _ (1098437 / 50000) (2196877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474778368 :
    ThetaLowerSegment 3474778368 3474909440 (347469314672387 / 100000)
      (347482361930829 / 100000) := by
  exact
    packedTile65536 3474778368 3474909440 14 5939 58947 32 _ _ (1098439 / 50000) (2196881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3474909440 :
    ThetaLowerSegment 3474909440 3475040512 (347482361930829 / 100000)
      (347495444363139 / 100000) := by
  exact
    packedTile65536 3474909440 3475040512 14 5955 58948 32 _ _ (1098441 / 50000) (439377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475040512 :
    ThetaLowerSegment 3475040512 3475171584 (347495444363139 / 100000)
      (347508537803699 / 100000) := by
  exact
    packedTile65536 3475040512 3475171584 14 5960 58949 32 _ _ (1098443 / 50000) (2196889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475171584 :
    ThetaLowerSegment 3475171584 3475302656 (347508537803699 / 100000)
      (86880403970979 / 25000) := by
  exact
    packedTile65536 3475171584 3475302656 14 5953 58950 32 _ _ (2196889 / 100000) (549223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475302656 :
    ThetaLowerSegment 3475302656 3475433728 (86880403970979 / 25000)
      (347534795045023 / 100000) := by
  exact
    packedTile65536 3475302656 3475433728 14 5999 58951 32 _ _ (2196893 / 100000) (68653 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475433728 :
    ThetaLowerSegment 3475433728 3475564800 (347534795045023 / 100000)
      (347547932489083 / 100000) := by
  exact
    packedTile65536 3475433728 3475564800 14 5980 58952 32 _ _ (2196897 / 100000) (21969 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475564800 :
    ThetaLowerSegment 3475564800 3475695872 (347547932489083 / 100000)
      (43445115345587 / 12500) := by
  exact
    packedTile65536 3475564800 3475695872 14 5913 58953 32 _ _ (2196901 / 100000) (274613 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475695872 :
    ThetaLowerSegment 3475695872 3475826944 (43445115345587 / 12500)
      (347574167904941 / 100000) := by
  exact
    packedTile65536 3475695872 3475826944 14 6029 58955 32 _ _ (439381 / 20000) (549227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475826944 :
    ThetaLowerSegment 3475826944 3475958016 (347574167904941 / 100000)
      (69517433841297 / 20000) := by
  exact
    packedTile65536 3475826944 3475958016 14 5918 58956 32 _ _ (549227 / 25000) (2196911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3475958016 :
    ThetaLowerSegment 3475958016 3476089088 (69517433841297 / 20000) (2780804475081 / 800) := by
  exact
    packedTile65536 3475958016 3476089088 14 6095 58957 32 _ _ (137307 / 6250) (439383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476089088 :
    ThetaLowerSegment 3476089088 3476220160 (2780804475081 / 800) (347613628838409 / 100000) := by
  exact
    packedTile65536 3476089088 3476220160 14 5949 58958 32 _ _ (549229 / 25000) (2196919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476220160 :
    ThetaLowerSegment 3476220160 3476351232 (347613628838409 / 100000)
      (347626641195569 / 100000) := by
  exact
    packedTile65536 3476220160 3476351232 14 5923 58959 32 _ _ (54923 / 2500) (2196923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476351232 :
    ThetaLowerSegment 3476351232 3476482304 (347626641195569 / 100000) (695279192901 / 200) := by
  exact
    packedTile65536 3476351232 3476482304 14 5897 58960 32 _ _ (2196923 / 100000) (1098463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476482304 :
    ThetaLowerSegment 3476482304 3476613376 (695279192901 / 200) (173826404384739 / 50000) := by
  exact
    packedTile65536 3476482304 3476613376 14 6014 58961 32 _ _ (2196927 / 100000) (219693 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476613376 :
    ThetaLowerSegment 3476613376 3476744448 (173826404384739 / 50000)
      (347665988158547 / 100000) := by
  exact
    packedTile65536 3476613376 3476744448 14 5999 58962 32 _ _ (2196931 / 100000) (1098467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476744448 :
    ThetaLowerSegment 3476744448 3476875520 (347665988158547 / 100000)
      (86919743560333 / 25000) := by
  exact
    packedTile65536 3476744448 3476875520 14 5911 58963 32 _ _ (439387 / 20000) (1098469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3476875520 :
    ThetaLowerSegment 3476875520 3477006592 (86919743560333 / 25000) (173846061457631 / 50000) := by
  exact
    packedTile65536 3476875520 3477006592 14 5985 58965 32 _ _ (1098469 / 50000) (2196941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477006592 :
    ThetaLowerSegment 3477006592 3477137664 (173846061457631 / 50000) (86926295933863 / 25000) := by
  exact
    packedTile65536 3477006592 3477137664 14 5945 58966 32 _ _ (1098471 / 50000) (439389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477137664 :
    ThetaLowerSegment 3477137664 3477268736 (86926295933863 / 25000) (173859172819469 / 50000) := by
  exact
    packedTile65536 3477137664 3477268736 14 5991 58967 32 _ _ (1098473 / 50000) (2196949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477268736 :
    ThetaLowerSegment 3477268736 3477399808 (173859172819469 / 50000) (86932828558697 / 25000) := by
  exact
    packedTile65536 3477268736 3477399808 14 5903 58968 32 _ _ (43939 / 2000) (2196953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477399808 :
    ThetaLowerSegment 3477399808 3477530880 (86932828558697 / 25000) (695489114947 / 200) := by
  exact
    packedTile65536 3477399808 3477530880 14 6028 58969 32 _ _ (1098477 / 50000) (2196957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477530880 :
    ThetaLowerSegment 3477530880 3477661952 (695489114947 / 200) (173878832259481 / 50000) := by
  exact
    packedTile65536 3477530880 3477661952 14 5966 58970 32 _ _ (2196957 / 100000) (13731 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477661952 :
    ThetaLowerSegment 3477661952 3477793024 (173878832259481 / 50000)
      (173885352839729 / 50000) := by
  exact
    packedTile65536 3477661952 3477793024 14 5936 58971 32 _ _ (2196961 / 100000) (549241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477793024 :
    ThetaLowerSegment 3477793024 3477924096 (173885352839729 / 50000)
      (347783788606033 / 100000) := by
  exact
    packedTile65536 3477793024 3477924096 14 5955 58972 32 _ _ (439393 / 20000) (274621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3477924096 :
    ThetaLowerSegment 3477924096 3478055168 (347783788606033 / 100000)
      (347796847389769 / 100000) := by
  exact
    packedTile65536 3477924096 3478055168 14 5944 58973 32 _ _ (2196969 / 100000) (549243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478055168 :
    ThetaLowerSegment 3478055168 3478186240 (347796847389769 / 100000)
      (69561996177677 / 20000) := by
  exact
    packedTile65536 3478055168 3478186240 14 5978 58975 32 _ _ (549243 / 25000) (87879 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478186240 :
    ThetaLowerSegment 3478186240 3478317312 (69561996177677 / 20000) (13912921237033 / 4000) := by
  exact
    packedTile65536 3478186240 3478317312 14 5940 58976 32 _ _ (137311 / 6250) (2196979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478317312 :
    ThetaLowerSegment 3478317312 3478448384 (13912921237033 / 4000) (69567202136733 / 20000) := by
  exact
    packedTile65536 3478317312 3478448384 14 5908 58977 32 _ _ (109849 / 5000) (2196983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478448384 :
    ThetaLowerSegment 3478448384 3478579456 (69567202136733 / 20000)
      (347849120087193 / 100000) := by
  exact
    packedTile65536 3478448384 3478579456 14 5967 58978 32 _ _ (274623 / 12500) (2196987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478579456 :
    ThetaLowerSegment 3478579456 3478710528 (347849120087193 / 100000)
      (173931149906103 / 50000) := by
  exact
    packedTile65536 3478579456 3478710528 14 5999 58979 32 _ _ (2196987 / 100000) (219699 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478710528 :
    ThetaLowerSegment 3478710528 3478841600 (173931149906103 / 50000) (86968831992209 / 25000) := by
  exact
    packedTile65536 3478710528 3478841600 14 5930 58980 32 _ _ (2196991 / 100000) (1098497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478841600 :
    ThetaLowerSegment 3478841600 3478972672 (86968831992209 / 25000)
      (347888503347851 / 100000) := by
  exact
    packedTile65536 3478841600 3478972672 14 5997 58981 32 _ _ (439399 / 20000) (1098499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3478972672 :
    ThetaLowerSegment 3478972672 3479103744 (347888503347851 / 100000)
      (34790159965889 / 10000) := by
  exact
    packedTile65536 3478972672 3479103744 14 5961 58982 32 _ _ (2196999 / 100000) (1098501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479103744 :
    ThetaLowerSegment 3479103744 3479234816 (34790159965889 / 10000)
      (347914753115851 / 100000) := by
  exact
    packedTile65536 3479103744 3479234816 14 5987 58983 32 _ _ (2197003 / 100000) (1098503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479234816 :
    ThetaLowerSegment 3479234816 3479365888 (347914753115851 / 100000)
      (347927963712929 / 100000) := by
  exact
    packedTile65536 3479234816 3479365888 14 6013 58985 32 _ _ (1098503 / 50000) (2197009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479365888 :
    ThetaLowerSegment 3479365888 3479496960 (347927963712929 / 100000)
      (347940994179239 / 100000) := by
  exact
    packedTile65536 3479365888 3479496960 14 5931 58986 32 _ _ (219701 / 10000) (2197013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479496960 :
    ThetaLowerSegment 3479496960 3479628032 (347940994179239 / 100000)
      (347954167475183 / 100000) := by
  exact
    packedTile65536 3479496960 3479628032 14 5996 58987 32 _ _ (1098507 / 50000) (2197017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479628032 :
    ThetaLowerSegment 3479628032 3479759104 (347954167475183 / 100000)
      (347967360568273 / 100000) := by
  exact
    packedTile65536 3479628032 3479759104 14 6005 58988 32 _ _ (1098509 / 50000) (2197021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479759104 :
    ThetaLowerSegment 3479759104 3479890176 (347967360568273 / 100000)
      (347980687697659 / 100000) := by
  exact
    packedTile65536 3479759104 3479890176 14 6066 58989 32 _ _ (2197021 / 100000) (68657 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3479890176 :
    ThetaLowerSegment 3479890176 3480021248 (347980687697659 / 100000) (10874807677512 / 3125) := by
  exact
    packedTile65536 3479890176 3480021248 14 5989 58990 32 _ _ (87881 / 4000) (549257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480021248 :
    ThetaLowerSegment 3480021248 3480152320 (10874807677512 / 3125) (174003502942047 / 50000) := by
  exact
    packedTile65536 3480021248 3480152320 14 5990 58991 32 _ _ (2197029 / 100000) (274629 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480152320 :
    ThetaLowerSegment 3480152320 3480283392 (174003502942047 / 50000) (69604036298199 / 20000) := by
  exact
    packedTile65536 3480152320 3480283392 14 5997 58992 32 _ _ (2197033 / 100000) (549259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480283392 :
    ThetaLowerSegment 3480283392 3480414464 (69604036298199 / 20000)
      (348033326357383 / 100000) := by
  exact
    packedTile65536 3480283392 3480414464 14 5983 58993 32 _ _ (549259 / 25000) (2197039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480414464 :
    ThetaLowerSegment 3480414464 3480545536 (348033326357383 / 100000)
      (348046460262503 / 100000) := by
  exact
    packedTile65536 3480414464 3480545536 14 5978 58995 32 _ _ (27463 / 1250) (2197043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480545536 :
    ThetaLowerSegment 3480545536 3480676608 (348046460262503 / 100000)
      (348059644723547 / 100000) := by
  exact
    packedTile65536 3480545536 3480676608 14 6001 58996 32 _ _ (549261 / 25000) (2197047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480676608 :
    ThetaLowerSegment 3480676608 3480807680 (348059644723547 / 100000)
      (348072855573171 / 100000) := by
  exact
    packedTile65536 3480676608 3480807680 14 6013 58997 32 _ _ (274631 / 12500) (2197051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480807680 :
    ThetaLowerSegment 3480807680 3480938752 (348072855573171 / 100000)
      (348085989550027 / 100000) := by
  exact
    packedTile65536 3480807680 3480938752 14 5978 58998 32 _ _ (549263 / 25000) (439411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3480938752 :
    ThetaLowerSegment 3480938752 3481069824 (348085989550027 / 100000)
      (87024788026633 / 25000) := by
  exact
    packedTile65536 3480938752 3481069824 14 5991 58999 32 _ _ (439411 / 20000) (1098529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481069824 :
    ThetaLowerSegment 3481069824 3481200896 (87024788026633 / 25000) (10878501938288 / 3125) := by
  exact
    packedTile65536 3481069824 3481200896 14 5876 59000 32 _ _ (2197059 / 100000) (1098531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481200896 :
    ThetaLowerSegment 3481200896 3481331968 (10878501938288 / 3125) (87031278144859 / 25000) := by
  exact
    packedTile65536 3481200896 3481331968 14 5940 59001 32 _ _ (2197063 / 100000) (1098533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481331968 :
    ThetaLowerSegment 3481331968 3481463040 (87031278144859 / 25000)
      (348138525673471 / 100000) := by
  exact
    packedTile65536 3481331968 3481463040 14 6105 59002 32 _ _ (2197067 / 100000) (219707 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481463040 :
    ThetaLowerSegment 3481463040 3481594112 (348138525673471 / 100000)
      (348151655363791 / 100000) := by
  exact
    packedTile65536 3481463040 3481594112 14 5976 59003 32 _ _ (219707 / 10000) (2197073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481594112 :
    ThetaLowerSegment 3481594112 3481725184 (348151655363791 / 100000)
      (348164578553059 / 100000) := by
  exact
    packedTile65536 3481594112 3481725184 14 5882 59005 32 _ _ (1098537 / 50000) (2197077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481725184 :
    ThetaLowerSegment 3481725184 3481856256 (348164578553059 / 100000)
      (348177681926251 / 100000) := by
  exact
    packedTile65536 3481725184 3481856256 14 5964 59006 32 _ _ (1098539 / 50000) (2197081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481856256 :
    ThetaLowerSegment 3481856256 3481987328 (348177681926251 / 100000)
      (348190732593331 / 100000) := by
  exact
    packedTile65536 3481856256 3481987328 14 5940 59007 32 _ _ (1098541 / 50000) (439417 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3481987328 :
    ThetaLowerSegment 3481987328 3482118400 (348190732593331 / 100000)
      (348203730548191 / 100000) := by
  exact
    packedTile65536 3481987328 3482118400 14 5916 59008 32 _ _ (439417 / 20000) (68659 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482118400 :
    ThetaLowerSegment 3482118400 3482249472 (348203730548191 / 100000)
      (174108385135703 / 50000) := by
  exact
    packedTile65536 3482118400 3482249472 14 5935 59009 32 _ _ (2197089 / 100000) (549273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482249472 :
    ThetaLowerSegment 3482249472 3482380544 (174108385135703 / 50000) (87057522262293 / 25000) := by
  exact
    packedTile65536 3482249472 3482380544 14 6062 59010 32 _ _ (2197093 / 100000) (274637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482380544 :
    ThetaLowerSegment 3482380544 3482511616 (87057522262293 / 25000) (174121457850729 / 50000) := by
  exact
    packedTile65536 3482380544 3482511616 14 5838 59011 32 _ _ (2197097 / 100000) (21971 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482511616 :
    ThetaLowerSegment 3482511616 3482642688 (174121457850729 / 50000)
      (174127952478329 / 50000) := by
  exact
    packedTile65536 3482511616 3482642688 14 5912 59012 32 _ _ (21971 / 1000) (2197103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482642688 :
    ThetaLowerSegment 3482642688 3482773760 (174127952478329 / 50000)
      (174134532804809 / 50000) := by
  exact
    packedTile65536 3482642688 3482773760 14 5990 59013 32 _ _ (137319 / 6250) (2197107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482773760 :
    ThetaLowerSegment 3482773760 3482904832 (174134532804809 / 50000)
      (174141083482311 / 50000) := by
  exact
    packedTile65536 3482773760 3482904832 14 5963 59015 32 _ _ (549277 / 25000) (2197111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3482904832 :
    ThetaLowerSegment 3482904832 3483035904 (174141083482311 / 50000)
      (174147722056219 / 50000) := by
  exact
    packedTile65536 3482904832 3483035904 14 6043 59016 32 _ _ (274639 / 12500) (439423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483035904 :
    ThetaLowerSegment 3483035904 3483166976 (174147722056219 / 50000)
      (174154198055629 / 50000) := by
  exact
    packedTile65536 3483035904 3483166976 14 5895 59017 32 _ _ (549279 / 25000) (2197119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483166976 :
    ThetaLowerSegment 3483166976 3483298048 (174154198055629 / 50000) (87080376030803 / 25000) := by
  exact
    packedTile65536 3483166976 3483298048 14 5966 59018 32 _ _ (2197119 / 100000) (1098561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483298048 :
    ThetaLowerSegment 3483298048 3483429120 (87080376030803 / 25000)
      (348334614356153 / 100000) := by
  exact
    packedTile65536 3483298048 3483429120 14 5967 59019 32 _ _ (2197123 / 100000) (1098563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483429120 :
    ThetaLowerSegment 3483429120 3483560192 (348334614356153 / 100000)
      (348347748781359 / 100000) := by
  exact
    packedTile65536 3483429120 3483560192 14 5978 59020 32 _ _ (2197127 / 100000) (219713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483560192 :
    ThetaLowerSegment 3483560192 3483691264 (348347748781359 / 100000)
      (87090179611413 / 25000) := by
  exact
    packedTile65536 3483560192 3483691264 14 5903 59021 32 _ _ (2197131 / 100000) (1098567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483691264 :
    ThetaLowerSegment 3483691264 3483822336 (87090179611413 / 25000) (174186775952673 / 50000) := by
  exact
    packedTile65536 3483691264 3483822336 14 5841 59022 32 _ _ (1098567 / 50000) (2197137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483822336 :
    ThetaLowerSegment 3483822336 3483953408 (174186775952673 / 50000)
      (174193356380983 / 50000) := by
  exact
    packedTile65536 3483822336 3483953408 14 5990 59023 32 _ _ (1098569 / 50000) (2197141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3483953408 :
    ThetaLowerSegment 3483953408 3484084480 (174193356380983 / 50000) (87099978847061 / 25000) := by
  exact
    packedTile65536 3483953408 3484084480 14 6009 59025 32 _ _ (1098571 / 50000) (439429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484084480 :
    ThetaLowerSegment 3484084480 3484215552 (87099978847061 / 25000) (174206537047819 / 50000) := by
  exact
    packedTile65536 3484084480 3484215552 14 5989 59026 32 _ _ (1098573 / 50000) (2197149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484215552 :
    ThetaLowerSegment 3484215552 3484346624 (174206537047819 / 50000) (87106558754537 / 25000) := by
  exact
    packedTile65536 3484215552 3484346624 14 5990 59027 32 _ _ (2197149 / 100000) (68661 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484346624 :
    ThetaLowerSegment 3484346624 3484477696 (87106558754537 / 25000) (174219741925369 / 50000) := by
  exact
    packedTile65536 3484346624 3484477696 14 6030 59028 32 _ _ (2197153 / 100000) (549289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484477696 :
    ThetaLowerSegment 3484477696 3484608768 (174219741925369 / 50000) (69690525009351 / 20000) := by
  exact
    packedTile65536 3484477696 3484608768 14 5981 59029 32 _ _ (2197157 / 100000) (54929 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484608768 :
    ThetaLowerSegment 3484608768 3484739840 (69690525009351 / 20000) (174232858964577 / 50000) := by
  exact
    packedTile65536 3484608768 3484739840 14 5959 59030 32 _ _ (2197161 / 100000) (549291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484739840 :
    ThetaLowerSegment 3484739840 3484870912 (174232858964577 / 50000) (34847896463091 / 10000) := by
  exact
    packedTile65536 3484739840 3484870912 14 6029 59031 32 _ _ (549291 / 25000) (2197167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3484870912 :
    ThetaLowerSegment 3484870912 3485001984 (34847896463091 / 10000) (174246023284591 / 50000) := by
  exact
    packedTile65536 3484870912 3485001984 14 5954 59032 32 _ _ (137323 / 6250) (2197171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485001984 :
    ThetaLowerSegment 3485001984 3485133056 (174246023284591 / 50000)
      (174252651053929 / 50000) := by
  exact
    packedTile65536 3485001984 3485133056 14 6033 59033 32 _ _ (549293 / 25000) (87887 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485133056 :
    ThetaLowerSegment 3485133056 3485264128 (174252651053929 / 50000)
      (174259286525449 / 50000) := by
  exact
    packedTile65536 3485133056 3485264128 14 6040 59035 32 _ _ (274647 / 12500) (2197179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485264128 :
    ThetaLowerSegment 3485264128 3485395200 (174259286525449 / 50000)
      (348531525421103 / 100000) := by
  exact
    packedTile65536 3485264128 3485395200 14 5895 59036 32 _ _ (2197179 / 100000) (1098591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485395200 :
    ThetaLowerSegment 3485395200 3485526272 (348531525421103 / 100000)
      (69708873151711 / 20000) := by
  exact
    packedTile65536 3485395200 3485526272 14 5844 59037 32 _ _ (2197183 / 100000) (1098593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485526272 :
    ThetaLowerSegment 3485526272 3485657344 (69708873151711 / 20000) (174278744778253 / 50000) := by
  exact
    packedTile65536 3485526272 3485657344 14 5973 59038 32 _ _ (2197187 / 100000) (219719 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485657344 :
    ThetaLowerSegment 3485657344 3485788416 (174278744778253 / 50000)
      (174285305590579 / 50000) := by
  exact
    packedTile65536 3485657344 3485788416 14 5972 59039 32 _ _ (2197191 / 100000) (1098597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485788416 :
    ThetaLowerSegment 3485788416 3485919488 (174285305590579 / 50000)
      (348583849281033 / 100000) := by
  exact
    packedTile65536 3485788416 3485919488 14 6025 59040 32 _ _ (439439 / 20000) (1098599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3485919488 :
    ThetaLowerSegment 3485919488 3486050560 (348583849281033 / 100000)
      (348597012694251 / 100000) := by
  exact
    packedTile65536 3485919488 3486050560 14 5991 59041 32 _ _ (1098599 / 50000) (2197201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486050560 :
    ThetaLowerSegment 3486050560 3486181632 (348597012694251 / 100000)
      (348610037707707 / 100000) := by
  exact
    packedTile65536 3486050560 3486181632 14 5928 59042 32 _ _ (1098601 / 50000) (439441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486181632 :
    ThetaLowerSegment 3486181632 3486312704 (348610037707707 / 100000)
      (348623170407969 / 100000) := by
  exact
    packedTile65536 3486181632 3486312704 14 5977 59043 32 _ _ (1098603 / 50000) (2197209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486312704 :
    ThetaLowerSegment 3486312704 3486443776 (348623170407969 / 100000)
      (348636300934929 / 100000) := by
  exact
    packedTile65536 3486312704 3486443776 14 5976 59045 32 _ _ (219721 / 10000) (2197213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486443776 :
    ThetaLowerSegment 3486443776 3486574848 (348636300934929 / 100000)
      (87162388081633 / 25000) := by
  exact
    packedTile65536 3486443776 3486574848 14 6031 59046 32 _ _ (2197213 / 100000) (68663 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486574848 :
    ThetaLowerSegment 3486574848 3486705920 (87162388081633 / 25000) (43582829868873 / 12500) := by
  exact
    packedTile65536 3486574848 3486705920 14 5956 59047 32 _ _ (2197217 / 100000) (109861 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486705920 :
    ThetaLowerSegment 3486705920 3486836992 (43582829868873 / 12500) (34867574757147 / 10000) := by
  exact
    packedTile65536 3486705920 3486836992 14 5966 59048 32 _ _ (2197221 / 100000) (274653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486836992 :
    ThetaLowerSegment 3486836992 3486968064 (34867574757147 / 10000) (69737783108179 / 20000) := by
  exact
    packedTile65536 3486836992 3486968064 14 5993 59049 32 _ _ (87889 / 4000) (549307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3486968064 :
    ThetaLowerSegment 3486968064 3487099136 (69737783108179 / 20000)
      (348701958286303 / 100000) := by
  exact
    packedTile65536 3486968064 3487099136 14 5936 59050 32 _ _ (549307 / 25000) (2197231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487099136 :
    ThetaLowerSegment 3487099136 3487230208 (348701958286303 / 100000)
      (69743041958499 / 20000) := by
  exact
    packedTile65536 3487099136 3487230208 14 6031 59051 32 _ _ (137327 / 6250) (439447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487230208 :
    ThetaLowerSegment 3487230208 3487361280 (69743041958499 / 20000)
      (348728311910763 / 100000) := by
  exact
    packedTile65536 3487230208 3487361280 14 5963 59052 32 _ _ (549309 / 25000) (2197239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487361280 :
    ThetaLowerSegment 3487361280 3487492352 (348728311910763 / 100000)
      (348741291007443 / 100000) := by
  exact
    packedTile65536 3487361280 3487492352 14 5907 59053 32 _ _ (54931 / 2500) (2197243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487492352 :
    ThetaLowerSegment 3487492352 3487623424 (348741291007443 / 100000) (21797157812627 / 6250) := by
  exact
    packedTile65536 3487492352 3487623424 14 6023 59054 32 _ _ (2197243 / 100000) (1098623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487623424 :
    ThetaLowerSegment 3487623424 3487754496 (21797157812627 / 6250) (69753510495899 / 20000) := by
  exact
    packedTile65536 3487623424 3487754496 14 5929 59056 32 _ _ (2197247 / 100000) (8789 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487754496 :
    ThetaLowerSegment 3487754496 3487885568 (69753510495899 / 20000)
      (348780612939439 / 100000) := by
  exact
    packedTile65536 3487754496 3487885568 14 5944 59057 32 _ _ (2197251 / 100000) (1098627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3487885568 :
    ThetaLowerSegment 3487885568 3488016640 (348780612939439 / 100000)
      (87198433187261 / 25000) := by
  exact
    packedTile65536 3487885568 3488016640 14 5971 59058 32 _ _ (439451 / 20000) (1098629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488016640 :
    ThetaLowerSegment 3488016640 3488147712 (87198433187261 / 25000) (43600873875477 / 12500) := by
  exact
    packedTile65536 3488016640 3488147712 14 6034 59059 32 _ _ (1098629 / 50000) (2197261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488147712 :
    ThetaLowerSegment 3488147712 3488278784 (43600873875477 / 12500) (10900627434259 / 3125) := by
  exact
    packedTile65536 3488147712 3488278784 14 5956 59060 32 _ _ (1098631 / 50000) (439453 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488278784 :
    ThetaLowerSegment 3488278784 3488409856 (10900627434259 / 3125) (87208314274439 / 25000) := by
  exact
    packedTile65536 3488278784 3488409856 14 5998 59061 32 _ _ (1098633 / 50000) (2197269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488409856 :
    ThetaLowerSegment 3488409856 3488540928 (87208314274439 / 25000) (174423120383093 / 50000) := by
  exact
    packedTile65536 3488409856 3488540928 14 5909 59062 32 _ _ (219727 / 10000) (2197273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488540928 :
    ThetaLowerSegment 3488540928 3488672000 (174423120383093 / 50000)
      (348859316737809 / 100000) := by
  exact
    packedTile65536 3488540928 3488672000 14 5951 59063 32 _ _ (2197273 / 100000) (549319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488672000 :
    ThetaLowerSegment 3488672000 3488803072 (348859316737809 / 100000) (13954900719121 / 4000) := by
  exact
    packedTile65536 3488672000 3488803072 14 6008 59064 32 _ _ (2197277 / 100000) (13733 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488803072 :
    ThetaLowerSegment 3488803072 3488934144 (13954900719121 / 4000) (174442821168719 / 50000) := by
  exact
    packedTile65536 3488803072 3488934144 14 5973 59066 32 _ _ (2197281 / 100000) (549321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3488934144 :
    ThetaLowerSegment 3488934144 3489065216 (174442821168719 / 50000)
      (348898709591333 / 100000) := by
  exact
    packedTile65536 3488934144 3489065216 14 5947 59067 32 _ _ (439457 / 20000) (274661 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489065216 :
    ThetaLowerSegment 3489065216 3489196288 (348898709591333 / 100000)
      (348911981210853 / 100000) := by
  exact
    packedTile65536 3489065216 3489196288 14 6040 59068 32 _ _ (274661 / 12500) (2197291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489196288 :
    ThetaLowerSegment 3489196288 3489327360 (348911981210853 / 100000)
      (348925026533457 / 100000) := by
  exact
    packedTile65536 3489196288 3489327360 14 5937 59069 32 _ _ (549323 / 25000) (439459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489327360 :
    ThetaLowerSegment 3489327360 3489458432 (348925026533457 / 100000)
      (348937948831233 / 100000) := by
  exact
    packedTile65536 3489327360 3489458432 14 5881 59070 32 _ _ (137331 / 6250) (2197299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489458432 :
    ThetaLowerSegment 3489458432 3489589504 (348937948831233 / 100000)
      (348950950255333 / 100000) := by
  exact
    packedTile65536 3489458432 3489589504 14 5917 59071 32 _ _ (21973 / 1000) (2197303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489589504 :
    ThetaLowerSegment 3489589504 3489720576 (348950950255333 / 100000)
      (348963887975397 / 100000) := by
  exact
    packedTile65536 3489589504 3489720576 14 5888 59072 32 _ _ (2197303 / 100000) (1098653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489720576 :
    ThetaLowerSegment 3489720576 3489851648 (348963887975397 / 100000) (21811053942077 / 6250) := by
  exact
    packedTile65536 3489720576 3489851648 14 5905 59073 32 _ _ (2197307 / 100000) (219731 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489851648 :
    ThetaLowerSegment 3489851648 3489982720 (21811053942077 / 6250) (174495003693817 / 50000) := by
  exact
    packedTile65536 3489851648 3489982720 14 5982 59074 32 _ _ (2197311 / 100000) (1098657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3489982720 :
    ThetaLowerSegment 3489982720 3490113792 (174495003693817 / 50000)
      (349003206658839 / 100000) := by
  exact
    packedTile65536 3489982720 3490113792 14 6007 59076 32 _ _ (439463 / 20000) (1098659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490113792 :
    ThetaLowerSegment 3490113792 3490244864 (349003206658839 / 100000)
      (349016205998043 / 100000) := by
  exact
    packedTile65536 3490113792 3490244864 14 5916 59077 32 _ _ (2197319 / 100000) (1098661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490244864 :
    ThetaLowerSegment 3490244864 3490375936 (349016205998043 / 100000)
      (349029225130893 / 100000) := by
  exact
    packedTile65536 3490244864 3490375936 14 5925 59078 32 _ _ (1098661 / 50000) (87893 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490375936 :
    ThetaLowerSegment 3490375936 3490507008 (349029225130893 / 100000)
      (349042483795977 / 100000) := by
  exact
    packedTile65536 3490375936 3490507008 14 6034 59079 32 _ _ (1098663 / 50000) (2197329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490507008 :
    ThetaLowerSegment 3490507008 3490638080 (349042483795977 / 100000)
      (349055481002927 / 100000) := by
  exact
    packedTile65536 3490507008 3490638080 14 5915 59080 32 _ _ (219733 / 10000) (2197333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490638080 :
    ThetaLowerSegment 3490638080 3490769152 (349055481002927 / 100000)
      (69813738274987 / 20000) := by
  exact
    packedTile65536 3490638080 3490769152 14 6012 59081 32 _ _ (1098667 / 50000) (2197337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490769152 :
    ThetaLowerSegment 3490769152 3490900224 (69813738274987 / 20000)
      (349081805082151 / 100000) := by
  exact
    packedTile65536 3490769152 3490900224 14 5968 59082 32 _ _ (2197337 / 100000) (109867 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3490900224 :
    ThetaLowerSegment 3490900224 3491031296 (349081805082151 / 100000)
      (349094826524917 / 100000) := by
  exact
    packedTile65536 3490900224 3491031296 14 5926 59083 32 _ _ (2197341 / 100000) (68667 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491031296 :
    ThetaLowerSegment 3491031296 3491162368 (349094826524917 / 100000)
      (174553971238611 / 50000) := by
  exact
    packedTile65536 3491031296 3491162368 14 5969 59084 32 _ _ (439469 / 20000) (549337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491162368 :
    ThetaLowerSegment 3491162368 3491293440 (174553971238611 / 50000)
      (174560528128027 / 50000) := by
  exact
    packedTile65536 3491162368 3491293440 14 5968 59086 32 _ _ (2197349 / 100000) (274669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491293440 :
    ThetaLowerSegment 3491293440 3491424512 (174560528128027 / 50000)
      (174567108098591 / 50000) := by
  exact
    packedTile65536 3491293440 3491424512 14 5989 59087 32 _ _ (274669 / 12500) (439471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491424512 :
    ThetaLowerSegment 3491424512 3491555584 (174567108098591 / 50000)
      (174573705659981 / 50000) := by
  exact
    packedTile65536 3491424512 3491555584 14 6005 59088 32 _ _ (549339 / 25000) (2197359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491555584 :
    ThetaLowerSegment 3491555584 3491686656 (174573705659981 / 50000)
      (174580188970661 / 50000) := by
  exact
    packedTile65536 3491555584 3491686656 14 5901 59089 32 _ _ (27467 / 1250) (2197363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491686656 :
    ThetaLowerSegment 3491686656 3491817728 (174580188970661 / 50000)
      (174586831602033 / 50000) := by
  exact
    packedTile65536 3491686656 3491817728 14 6046 59090 32 _ _ (549341 / 25000) (2197367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491817728 :
    ThetaLowerSegment 3491817728 3491948800 (174586831602033 / 50000)
      (349186810050827 / 100000) := by
  exact
    packedTile65536 3491817728 3491948800 14 5983 59091 32 _ _ (2197367 / 100000) (219737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3491948800 :
    ThetaLowerSegment 3491948800 3492079872 (349186810050827 / 100000)
      (174599897158033 / 50000) := by
  exact
    packedTile65536 3491948800 3492079872 14 5909 59092 32 _ _ (2197371 / 100000) (1098687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492079872 :
    ThetaLowerSegment 3492079872 3492210944 (174599897158033 / 50000) (87303225963829 / 25000) := by
  exact
    packedTile65536 3492079872 3492210944 14 5966 59093 32 _ _ (17579 / 800) (1098689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492210944 :
    ThetaLowerSegment 3492210944 3492342016 (87303225963829 / 25000)
      (349226085931937 / 100000) := by
  exact
    packedTile65536 3492210944 3492342016 14 5999 59094 32 _ _ (2197379 / 100000) (1098691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492342016 :
    ThetaLowerSegment 3492342016 3492473088 (349226085931937 / 100000)
      (349239120801961 / 100000) := by
  exact
    packedTile65536 3492342016 3492473088 14 5932 59096 32 _ _ (1098691 / 50000) (439477 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492473088 :
    ThetaLowerSegment 3492473088 3492604160 (349239120801961 / 100000)
      (69850453991957 / 20000) := by
  exact
    packedTile65536 3492473088 3492604160 14 5984 59097 32 _ _ (1098693 / 50000) (2197389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492604160 :
    ThetaLowerSegment 3492604160 3492735232 (69850453991957 / 20000) (69853064051799 / 20000) := by
  exact
    packedTile65536 3492604160 3492735232 14 5939 59098 32 _ _ (219739 / 10000) (2197393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492735232 :
    ThetaLowerSegment 3492735232 3492866304 (69853064051799 / 20000)
      (349278243133109 / 100000) := by
  exact
    packedTile65536 3492735232 3492866304 14 5881 59099 32 _ _ (1098697 / 50000) (2197397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492866304 :
    ThetaLowerSegment 3492866304 3492997376 (349278243133109 / 100000)
      (69858258255299 / 20000) := by
  exact
    packedTile65536 3492866304 3492997376 14 5938 59100 32 _ _ (2197397 / 100000) (10987 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3492997376 :
    ThetaLowerSegment 3492997376 3493128448 (69858258255299 / 20000)
      (349304378996851 / 100000) := by
  exact
    packedTile65536 3492997376 3493128448 14 5956 59101 32 _ _ (2197401 / 100000) (549351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493128448 :
    ThetaLowerSegment 3493128448 3493259520 (349304378996851 / 100000)
      (349317457951411 / 100000) := by
  exact
    packedTile65536 3493128448 3493259520 14 5952 59102 32 _ _ (439481 / 20000) (68669 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493259520 :
    ThetaLowerSegment 3493259520 3493390592 (349317457951411 / 100000)
      (69866095959429 / 20000) := by
  exact
    packedTile65536 3493259520 3493390592 14 5926 59103 32 _ _ (2197409 / 100000) (549353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493390592 :
    ThetaLowerSegment 3493390592 3493521664 (69866095959429 / 20000)
      (349343442330533 / 100000) := by
  exact
    packedTile65536 3493390592 3493521664 14 5899 59104 32 _ _ (549353 / 25000) (439483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493521664 :
    ThetaLowerSegment 3493521664 3493652736 (349343442330533 / 100000)
      (349356545522141 / 100000) := by
  exact
    packedTile65536 3493521664 3493652736 14 5963 59106 32 _ _ (274677 / 12500) (2197419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493652736 :
    ThetaLowerSegment 3493652736 3493783808 (349356545522141 / 100000)
      (349369593802101 / 100000) := by
  exact
    packedTile65536 3493652736 3493783808 14 5938 59107 32 _ _ (109871 / 5000) (2197423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493783808 :
    ThetaLowerSegment 3493783808 3493914880 (349369593802101 / 100000)
      (349382971719413 / 100000) := by
  exact
    packedTile65536 3493783808 3493914880 14 6088 59108 32 _ _ (137339 / 6250) (2197427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3493914880 :
    ThetaLowerSegment 3493914880 3494045952 (349382971719413 / 100000)
      (349396138701997 / 100000) := by
  exact
    packedTile65536 3493914880 3494045952 14 5992 59109 32 _ _ (2197427 / 100000) (219743 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494045952 :
    ThetaLowerSegment 3494045952 3494177024 (349396138701997 / 100000) (2795275254323 / 800) := by
  exact
    packedTile65536 3494045952 3494177024 14 6038 59110 32 _ _ (2197431 / 100000) (1098717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494177024 :
    ThetaLowerSegment 3494177024 3494308096 (2795275254323 / 800) (69884505974439 / 20000) := by
  exact
    packedTile65536 3494177024 3494308096 14 5972 59111 32 _ _ (439487 / 20000) (1098719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494308096 :
    ThetaLowerSegment 3494308096 3494439168 (69884505974439 / 20000) (174717858351817 / 50000) := by
  exact
    packedTile65536 3494308096 3494439168 14 6001 59112 32 _ _ (2197439 / 100000) (1098721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494439168 :
    ThetaLowerSegment 3494439168 3494570240 (174717858351817 / 50000)
      (174724397939209 / 50000) := by
  exact
    packedTile65536 3494439168 3494570240 14 5952 59113 32 _ _ (1098721 / 50000) (439489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494570240 :
    ThetaLowerSegment 3494570240 3494701312 (174724397939209 / 50000) (87365503379027 / 25000) := by
  exact
    packedTile65536 3494570240 3494701312 14 6015 59114 32 _ _ (1098723 / 50000) (2197449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494701312 :
    ThetaLowerSegment 3494701312 3494832384 (87365503379027 / 25000) (43684390437851 / 12500) := by
  exact
    packedTile65536 3494701312 3494832384 14 5966 59115 32 _ _ (43949 / 2000) (2197453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494832384 :
    ThetaLowerSegment 3494832384 3494963456 (43684390437851 / 12500) (174744106868143 / 50000) := by
  exact
    packedTile65536 3494832384 3494963456 14 5957 59117 32 _ _ (1098727 / 50000) (2197457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3494963456 :
    ThetaLowerSegment 3494963456 3495094528 (174744106868143 / 50000)
      (349501229274097 / 100000) := by
  exact
    packedTile65536 3494963456 3495094528 14 5923 59118 32 _ _ (2197457 / 100000) (109873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495094528 :
    ThetaLowerSegment 3495094528 3495225600 (349501229274097 / 100000)
      (349514247033061 / 100000) := by
  exact
    packedTile65536 3495094528 3495225600 14 5924 59119 32 _ _ (2197461 / 100000) (274683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495225600 :
    ThetaLowerSegment 3495225600 3495356672 (349514247033061 / 100000)
      (174763629111663 / 50000) := by
  exact
    packedTile65536 3495225600 3495356672 14 5921 59120 32 _ _ (439493 / 20000) (549367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495356672 :
    ThetaLowerSegment 3495356672 3495487744 (174763629111663 / 50000)
      (174770230308539 / 50000) := by
  exact
    packedTile65536 3495356672 3495487744 14 6008 59121 32 _ _ (2197469 / 100000) (68671 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495487744 :
    ThetaLowerSegment 3495487744 3495618816 (174770230308539 / 50000)
      (174776810638443 / 50000) := by
  exact
    packedTile65536 3495487744 3495618816 14 5989 59122 32 _ _ (68671 / 3125) (87899 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495618816 :
    ThetaLowerSegment 3495618816 3495749888 (174776810638443 / 50000) (34956674899851 / 10000) := by
  exact
    packedTile65536 3495618816 3495749888 14 5974 59123 32 _ _ (549369 / 25000) (2197479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495749888 :
    ThetaLowerSegment 3495749888 3495880960 (34956674899851 / 10000) (34958003056763 / 10000) := by
  exact
    packedTile65536 3495749888 3495880960 14 6044 59124 32 _ _ (54937 / 2500) (2197483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3495880960 :
    ThetaLowerSegment 3495880960 3496012032 (34958003056763 / 10000) (174796615427009 / 50000) := by
  exact
    packedTile65536 3495880960 3496012032 14 6007 59125 32 _ _ (549371 / 25000) (2197487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496012032 :
    ThetaLowerSegment 3496012032 3496143104 (174796615427009 / 50000)
      (349606334468999 / 100000) := by
  exact
    packedTile65536 3496012032 3496143104 14 5963 59127 32 _ _ (2197487 / 100000) (219749 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496143104 :
    ThetaLowerSegment 3496143104 3496274176 (349606334468999 / 100000)
      (174809690486533 / 50000) := by
  exact
    packedTile65536 3496143104 3496274176 14 5937 59128 32 _ _ (2197491 / 100000) (1098747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496274176 :
    ThetaLowerSegment 3496274176 3496405248 (174809690486533 / 50000)
      (349632379155991 / 100000) := by
  exact
    packedTile65536 3496274176 3496405248 14 5915 59129 32 _ _ (439499 / 20000) (1098749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496405248 :
    ThetaLowerSegment 3496405248 3496536320 (349632379155991 / 100000)
      (349645805874881 / 100000) := by
  exact
    packedTile65536 3496405248 3496536320 14 6110 59130 32 _ _ (2197499 / 100000) (1098751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496536320 :
    ThetaLowerSegment 3496536320 3496667392 (349645805874881 / 100000)
      (349658755754167 / 100000) := by
  exact
    packedTile65536 3496536320 3496667392 14 5893 59131 32 _ _ (1098751 / 50000) (439501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496667392 :
    ThetaLowerSegment 3496667392 3496798464 (349658755754167 / 100000)
      (349671808939807 / 100000) := by
  exact
    packedTile65536 3496667392 3496798464 14 5940 59132 32 _ _ (1098753 / 50000) (2197509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496798464 :
    ThetaLowerSegment 3496798464 3496929536 (349671808939807 / 100000)
      (349684857754187 / 100000) := by
  exact
    packedTile65536 3496798464 3496929536 14 5938 59133 32 _ _ (219751 / 10000) (2197513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3496929536 :
    ThetaLowerSegment 3496929536 3497060608 (349684857754187 / 100000)
      (349697954937627 / 100000) := by
  exact
    packedTile65536 3496929536 3497060608 14 5960 59134 32 _ _ (1098757 / 50000) (2197517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497060608 :
    ThetaLowerSegment 3497060608 3497191680 (349697954937627 / 100000)
      (174855577711123 / 50000) := by
  exact
    packedTile65536 3497060608 3497191680 14 6007 59135 32 _ _ (2197517 / 100000) (27469 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497191680 :
    ThetaLowerSegment 3497191680 3497322752 (174855577711123 / 50000)
      (349724303190389 / 100000) := by
  exact
    packedTile65536 3497191680 3497322752 14 5983 59137 32 _ _ (2197521 / 100000) (549381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497322752 :
    ThetaLowerSegment 3497322752 3497339136 (349724303190389 / 100000)
      (87431481790341 / 25000) := by
  exact
    packedTile65536 3497322752 3497339136 11 739 59138 32 _ _ (87901 / 4000) (274691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497339136 :
    ThetaLowerSegment 3497339136 3497341184 (87431481790341 / 25000)
      (349726131531189 / 100000) := by
  exact
    packedTile65536 3497339136 3497341184 8 93 59138 32 _ _ (87901 / 4000) (274691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3465341184_3497341184 :
    ThetaLowerSegment 3465341184 3497341184 (173263125923279 / 50000)
      (349726131531189 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3465341184 cell3465472256)
                  (ThetaLowerSegment.join cell3465603328 cell3465734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3465865472 cell3465996544)
                  (ThetaLowerSegment.join cell3466127616 cell3466258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3466389760 cell3466520832)
                  (ThetaLowerSegment.join cell3466651904 cell3466782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3466914048 cell3467045120)
                  (ThetaLowerSegment.join cell3467176192 cell3467307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3467438336 cell3467569408)
                  (ThetaLowerSegment.join cell3467700480 cell3467831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3467962624 cell3468093696)
                  (ThetaLowerSegment.join cell3468224768 cell3468355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3468486912 cell3468617984)
                  (ThetaLowerSegment.join cell3468749056 cell3468880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3469011200 cell3469142272)
                  (ThetaLowerSegment.join cell3469273344 cell3469404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3469535488 cell3469666560)
                  (ThetaLowerSegment.join cell3469797632 cell3469928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3470059776 cell3470190848)
                  (ThetaLowerSegment.join cell3470321920 cell3470452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3470584064 cell3470715136)
                  (ThetaLowerSegment.join cell3470846208 cell3470977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3471108352 cell3471239424)
                  (ThetaLowerSegment.join cell3471370496 cell3471501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3471632640 cell3471763712)
                  (ThetaLowerSegment.join cell3471894784 cell3472025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3472156928 cell3472288000)
                  (ThetaLowerSegment.join cell3472419072 cell3472550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3472681216 cell3472812288)
                  (ThetaLowerSegment.join cell3472943360 cell3473074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3473205504 cell3473336576)
                  (ThetaLowerSegment.join cell3473467648 cell3473598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3473729792 cell3473860864)
                  (ThetaLowerSegment.join cell3473991936 cell3474123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3474254080 cell3474385152)
                  (ThetaLowerSegment.join cell3474516224 cell3474647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3474778368 cell3474909440)
                  (ThetaLowerSegment.join cell3475040512 cell3475171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3475302656 cell3475433728)
                  (ThetaLowerSegment.join cell3475564800 cell3475695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3475826944 cell3475958016)
                  (ThetaLowerSegment.join cell3476089088 cell3476220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3476351232 cell3476482304)
                  (ThetaLowerSegment.join cell3476613376 cell3476744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3476875520 cell3477006592)
                  (ThetaLowerSegment.join cell3477137664 cell3477268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3477399808 cell3477530880)
                  (ThetaLowerSegment.join cell3477661952 cell3477793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3477924096 cell3478055168)
                  (ThetaLowerSegment.join cell3478186240 cell3478317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3478448384 cell3478579456)
                  (ThetaLowerSegment.join cell3478710528 cell3478841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3478972672 cell3479103744)
                  (ThetaLowerSegment.join cell3479234816 cell3479365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3479496960 cell3479628032)
                  (ThetaLowerSegment.join cell3479759104 cell3479890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3480021248 cell3480152320)
                  (ThetaLowerSegment.join cell3480283392 cell3480414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3480545536 cell3480676608)
                  (ThetaLowerSegment.join cell3480807680 cell3480938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3481069824 cell3481200896)
                  (ThetaLowerSegment.join cell3481331968 cell3481463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3481594112 cell3481725184)
                  (ThetaLowerSegment.join cell3481856256 cell3481987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3482118400 cell3482249472)
                  (ThetaLowerSegment.join cell3482380544 cell3482511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3482642688 cell3482773760)
                  (ThetaLowerSegment.join cell3482904832 cell3483035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3483166976 cell3483298048)
                  (ThetaLowerSegment.join cell3483429120 cell3483560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3483691264 cell3483822336)
                  (ThetaLowerSegment.join cell3483953408 cell3484084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3484215552 cell3484346624)
                  (ThetaLowerSegment.join cell3484477696 cell3484608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3484739840 cell3484870912)
                  (ThetaLowerSegment.join cell3485001984 cell3485133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3485264128 cell3485395200)
                  (ThetaLowerSegment.join cell3485526272 cell3485657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3485788416 cell3485919488)
                  (ThetaLowerSegment.join cell3486050560 cell3486181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3486312704 cell3486443776)
                  (ThetaLowerSegment.join cell3486574848 cell3486705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3486836992 cell3486968064)
                  (ThetaLowerSegment.join cell3487099136 cell3487230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3487361280 cell3487492352)
                  (ThetaLowerSegment.join cell3487623424 cell3487754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3487885568 cell3488016640)
                  (ThetaLowerSegment.join cell3488147712 cell3488278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3488409856 cell3488540928)
                  (ThetaLowerSegment.join cell3488672000 cell3488803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3488934144 cell3489065216)
                  (ThetaLowerSegment.join cell3489196288 cell3489327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3489458432 cell3489589504)
                  (ThetaLowerSegment.join cell3489720576 cell3489851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3489982720 cell3490113792)
                  (ThetaLowerSegment.join cell3490244864 cell3490375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3490507008 cell3490638080)
                  (ThetaLowerSegment.join cell3490769152 cell3490900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3491031296 cell3491162368)
                  (ThetaLowerSegment.join cell3491293440 cell3491424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3491555584 cell3491686656)
                  (ThetaLowerSegment.join cell3491817728 cell3491948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3492079872 cell3492210944)
                  (ThetaLowerSegment.join cell3492342016 cell3492473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3492604160 cell3492735232)
                  (ThetaLowerSegment.join cell3492866304 cell3492997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3493128448 cell3493259520)
                  (ThetaLowerSegment.join cell3493390592 cell3493521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3493652736 cell3493783808)
                  (ThetaLowerSegment.join cell3493914880 cell3494045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3494177024 cell3494308096)
                  (ThetaLowerSegment.join cell3494439168 cell3494570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3494701312 cell3494832384)
                  (ThetaLowerSegment.join cell3494963456 cell3495094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3495225600 cell3495356672)
                  (ThetaLowerSegment.join cell3495487744 cell3495618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3495749888 cell3495880960)
                  (ThetaLowerSegment.join cell3496012032 cell3496143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3496274176 cell3496405248)
                  (ThetaLowerSegment.join cell3496536320 cell3496667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3496798464 cell3496929536)
                (ThetaLowerSegment.join cell3497060608 cell3497191680))
              (ThetaLowerSegment.join cell3497322752 cell3497339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
