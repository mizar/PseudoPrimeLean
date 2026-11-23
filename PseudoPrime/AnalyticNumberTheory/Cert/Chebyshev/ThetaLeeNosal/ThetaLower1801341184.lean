/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1801341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1769341184 :
    ThetaLowerSegment 1769341184 1769472256 (176929258059137 / 100000)
      (176942292030843 / 100000) := by
  exact
    packedTile65536 1769341184 1769472256 14 6121 42063 31 _ _ (1064693 / 50000) (2129389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769472256 :
    ThetaLowerSegment 1769472256 1769603328 (176942292030843 / 100000)
      (35391104815789 / 20000) := by
  exact
    packedTile65536 1769472256 1769603328 14 6214 42065 31 _ _ (2129393 / 100000) (532349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769603328 :
    ThetaLowerSegment 1769603328 1769734400 (35391104815789 / 20000)
      (176968526201451 / 100000) := by
  exact
    packedTile65536 1769603328 1769734400 14 6106 42066 31 _ _ (2129401 / 100000) (532351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769734400 :
    ThetaLowerSegment 1769734400 1769865472 (176968526201451 / 100000)
      (176981598637163 / 100000) := by
  exact
    packedTile65536 1769734400 1769865472 14 6139 42068 31 _ _ (66544 / 3125) (2129411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769865472 :
    ThetaLowerSegment 1769865472 1769996544 (176981598637163 / 100000)
      (88497380275639 / 50000) := by
  exact
    packedTile65536 1769865472 1769996544 14 6181 42069 31 _ _ (425883 / 20000) (1064709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769996544 :
    ThetaLowerSegment 1769996544 1770127616 (88497380275639 / 50000)
      (177007615877929 / 100000) := by
  exact
    packedTile65536 1769996544 1770127616 14 6037 42071 31 _ _ (2129423 / 100000) (1064713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770127616 :
    ThetaLowerSegment 1770127616 1770258688 (177007615877929 / 100000)
      (177020699095849 / 100000) := by
  exact
    packedTile65536 1770127616 1770258688 14 6144 42072 31 _ _ (212943 / 10000) (2129433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770258688 :
    ThetaLowerSegment 1770258688 1770389760 (177020699095849 / 100000)
      (177033761068541 / 100000) := by
  exact
    packedTile65536 1770258688 1770389760 14 6134 42074 31 _ _ (1064719 / 50000) (2129441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770389760 :
    ThetaLowerSegment 1770389760 1770520832 (177033761068541 / 100000)
      (88523372147353 / 50000) := by
  exact
    packedTile65536 1770389760 1770520832 14 6097 42075 31 _ _ (425889 / 20000) (266181 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770520832 :
    ThetaLowerSegment 1770520832 1770651904 (88523372147353 / 50000) (88529984095813 / 50000) := by
  exact
    packedTile65536 1770520832 1770651904 14 6210 42077 31 _ _ (532363 / 25000) (425891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770651904 :
    ThetaLowerSegment 1770651904 1770782976 (88529984095813 / 50000) (88536657823453 / 50000) := by
  exact
    packedTile65536 1770651904 1770782976 14 6268 42079 31 _ _ (106473 / 5000) (2129463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770782976 :
    ThetaLowerSegment 1770782976 1770914048 (88536657823453 / 50000) (35417268319309 / 20000) := by
  exact
    packedTile65536 1770782976 1770914048 14 6117 42080 31 _ _ (2129467 / 100000) (212947 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1770914048 :
    ThetaLowerSegment 1770914048 1771045120 (35417268319309 / 20000) (35419907164729 / 20000) := by
  exact
    packedTile65536 1770914048 1771045120 14 6196 42082 31 _ _ (85179 / 4000) (1064739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771045120 :
    ThetaLowerSegment 1771045120 1771176192 (35419907164729 / 20000)
      (177112723705671 / 100000) := by
  exact
    packedTile65536 1771045120 1771176192 14 6193 42083 31 _ _ (1064741 / 50000) (425897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771176192 :
    ThetaLowerSegment 1771176192 1771307264 (177112723705671 / 100000) (8856294303859 / 5000) := by
  exact
    packedTile65536 1771176192 1771307264 14 6181 42085 31 _ _ (2129489 / 100000) (532373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771307264 :
    ThetaLowerSegment 1771307264 1771438336 (8856294303859 / 5000) (35427756036303 / 20000) := by
  exact
    packedTile65536 1771307264 1771438336 14 6055 42086 31 _ _ (2129497 / 100000) (4259 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771438336 :
    ThetaLowerSegment 1771438336 1771569408 (35427756036303 / 20000) (35430364678703 / 20000) := by
  exact
    packedTile65536 1771438336 1771569408 14 6125 42088 31 _ _ (66547 / 3125) (2129507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771569408 :
    ThetaLowerSegment 1771569408 1771700480 (35430364678703 / 20000)
      (177165034885963 / 100000) := by
  exact
    packedTile65536 1771569408 1771700480 14 6204 42090 31 _ _ (266189 / 12500) (425903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771700480 :
    ThetaLowerSegment 1771700480 1771831552 (177165034885963 / 100000)
      (22147274147983 / 12500) := by
  exact
    packedTile65536 1771700480 1771831552 14 6179 42091 31 _ _ (2129519 / 100000) (1064761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771831552 :
    ThetaLowerSegment 1771831552 1771962624 (22147274147983 / 12500) (44297811794561 / 25000) := by
  exact
    packedTile65536 1771831552 1771962624 14 6130 42093 31 _ _ (1064763 / 50000) (2129529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771962624 :
    ThetaLowerSegment 1771962624 1772093696 (44297811794561 / 25000) (88602187877677 / 50000) := by
  exact
    packedTile65536 1771962624 1772093696 14 6165 42094 31 _ _ (1064767 / 50000) (2129537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772093696 :
    ThetaLowerSegment 1772093696 1772224768 (88602187877677 / 50000)
      (177217593816341 / 100000) := by
  exact
    packedTile65536 1772093696 1772224768 14 6207 42096 31 _ _ (2129541 / 100000) (266193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772224768 :
    ThetaLowerSegment 1772224768 1772355840 (177217593816341 / 100000)
      (44307709370393 / 25000) := by
  exact
    packedTile65536 1772224768 1772355840 14 6219 42097 31 _ _ (2129549 / 100000) (133097 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772355840 :
    ThetaLowerSegment 1772355840 1772486912 (44307709370393 / 25000) (8862192240481 / 5000) := by
  exact
    packedTile65536 1772355840 1772486912 14 6108 42099 31 _ _ (532389 / 25000) (2129559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772486912 :
    ThetaLowerSegment 1772486912 1772617984 (8862192240481 / 5000) (35451364899221 / 20000) := by
  exact
    packedTile65536 1772486912 1772617984 14 6095 42100 31 _ _ (2129563 / 100000) (1064783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772617984 :
    ThetaLowerSegment 1772617984 1772749056 (35451364899221 / 20000) (88634953225379 / 50000) := by
  exact
    packedTile65536 1772617984 1772749056 14 6143 42102 31 _ _ (2129571 / 100000) (1064787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772749056 :
    ThetaLowerSegment 1772749056 1772880128 (88634953225379 / 50000) (17728316094423 / 10000) := by
  exact
    packedTile65536 1772749056 1772880128 14 6224 42104 31 _ _ (1064789 / 50000) (2129581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1772880128 :
    ThetaLowerSegment 1772880128 1773011200 (17728316094423 / 10000) (88648073579829 / 50000) := by
  exact
    packedTile65536 1772880128 1773011200 14 6098 42105 31 _ _ (1064793 / 50000) (2129589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773011200 :
    ThetaLowerSegment 1773011200 1773142272 (88648073579829 / 50000)
      (177309322951549 / 100000) := by
  exact
    packedTile65536 1773011200 1773142272 14 6187 42107 31 _ _ (2129593 / 100000) (532399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773142272 :
    ThetaLowerSegment 1773142272 1773273344 (177309322951549 / 100000)
      (177322283697149 / 100000) := by
  exact
    packedTile65536 1773142272 1773273344 14 6086 42108 31 _ _ (2662 / 125) (2129603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773273344 :
    ThetaLowerSegment 1773273344 1773404416 (177322283697149 / 100000)
      (177335350971837 / 100000) := by
  exact
    packedTile65536 1773273344 1773404416 14 6136 42110 31 _ _ (266201 / 12500) (2129611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773404416 :
    ThetaLowerSegment 1773404416 1773535488 (177335350971837 / 100000)
      (88674174006091 / 50000) := by
  exact
    packedTile65536 1773404416 1773535488 14 6103 42111 31 _ _ (425923 / 20000) (1064809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773535488 :
    ThetaLowerSegment 1773535488 1773666560 (88674174006091 / 50000) (5542545162301 / 3125) := by
  exact
    packedTile65536 1773535488 1773666560 14 6150 42113 31 _ _ (2129623 / 100000) (1064813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773666560 :
    ThetaLowerSegment 1773666560 1773797632 (5542545162301 / 3125) (44343618567493 / 25000) := by
  exact
    packedTile65536 1773666560 1773797632 14 6118 42114 31 _ _ (212963 / 10000) (2129633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773797632 :
    ThetaLowerSegment 1773797632 1773928704 (44343618567493 / 25000) (35477518140851 / 20000) := by
  exact
    packedTile65536 1773797632 1773928704 14 6159 42116 31 _ _ (2129637 / 100000) (53241 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773928704 :
    ThetaLowerSegment 1773928704 1774059776 (35477518140851 / 20000) (35480145270923 / 20000) := by
  exact
    packedTile65536 1773928704 1774059776 14 6168 42118 31 _ _ (425929 / 20000) (133103 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774059776 :
    ThetaLowerSegment 1774059776 1774190848 (35480145270923 / 20000) (35482743446363 / 20000) := by
  exact
    packedTile65536 1774059776 1774190848 14 6100 42119 31 _ _ (532413 / 25000) (425931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774190848 :
    ThetaLowerSegment 1774190848 1774321920 (35482743446363 / 20000) (35485426392031 / 20000) := by
  exact
    packedTile65536 1774190848 1774321920 14 6299 42121 31 _ _ (106483 / 5000) (2129663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774321920 :
    ThetaLowerSegment 1774321920 1774452992 (35485426392031 / 20000) (35488037363773 / 20000) := by
  exact
    packedTile65536 1774321920 1774452992 14 6130 42122 31 _ _ (2129667 / 100000) (212967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774452992 :
    ThetaLowerSegment 1774452992 1774584064 (35488037363773 / 20000)
      (177453324777771 / 100000) := by
  exact
    packedTile65536 1774452992 1774584064 14 6169 42124 31 _ _ (1064837 / 50000) (2129677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774584064 :
    ThetaLowerSegment 1774584064 1774715136 (177453324777771 / 100000)
      (177466392506523 / 100000) := by
  exact
    packedTile65536 1774584064 1774715136 14 6136 42125 31 _ _ (1064841 / 50000) (425937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774715136 :
    ThetaLowerSegment 1774715136 1774846208 (177466392506523 / 100000)
      (177479332496887 / 100000) := by
  exact
    packedTile65536 1774715136 1774846208 14 6076 42127 31 _ _ (2129689 / 100000) (532423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774846208 :
    ThetaLowerSegment 1774846208 1774977280 (177479332496887 / 100000)
      (177492385403671 / 100000) := by
  exact
    packedTile65536 1774846208 1774977280 14 6129 42128 31 _ _ (66553 / 3125) (2129699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1774977280 :
    ThetaLowerSegment 1774977280 1775108352 (177492385403671 / 100000)
      (177505329744583 / 100000) := by
  exact
    packedTile65536 1774977280 1775108352 14 6078 42130 31 _ _ (266213 / 12500) (2129707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775108352 :
    ThetaLowerSegment 1775108352 1775239424 (177505329744583 / 100000)
      (35503690604753 / 20000) := by
  exact
    packedTile65536 1775108352 1775239424 14 6162 42132 31 _ _ (2129711 / 100000) (1064857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775239424 :
    ThetaLowerSegment 1775239424 1775370496 (35503690604753 / 20000)
      (177531478385169 / 100000) := by
  exact
    packedTile65536 1775239424 1775370496 14 6116 42133 31 _ _ (2129719 / 100000) (1064861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775370496 :
    ThetaLowerSegment 1775370496 1775501568 (177531478385169 / 100000)
      (177544550643357 / 100000) := by
  exact
    packedTile65536 1775370496 1775501568 14 6138 42135 31 _ _ (1064863 / 50000) (2129729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775501568 :
    ThetaLowerSegment 1775501568 1775632640 (177544550643357 / 100000)
      (177557835917811 / 100000) := by
  exact
    packedTile65536 1775501568 1775632640 14 6238 42136 31 _ _ (2129733 / 100000) (266217 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775632640 :
    ThetaLowerSegment 1775632640 1775763712 (177557835917811 / 100000)
      (177571040312011 / 100000) := by
  exact
    packedTile65536 1775632640 1775763712 14 6200 42138 31 _ _ (2129741 / 100000) (133109 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775763712 :
    ThetaLowerSegment 1775763712 1775894784 (177571040312011 / 100000)
      (35516788465079 / 20000) := by
  exact
    packedTile65536 1775763712 1775894784 14 6058 42139 31 _ _ (532437 / 25000) (2129751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775894784 :
    ThetaLowerSegment 1775894784 1776025856 (35516788465079 / 20000)
      (177597236262347 / 100000) := by
  exact
    packedTile65536 1775894784 1776025856 14 6242 42141 31 _ _ (532439 / 25000) (2129759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776025856 :
    ThetaLowerSegment 1776025856 1776156928 (177597236262347 / 100000)
      (35522060897623 / 20000) := by
  exact
    packedTile65536 1776025856 1776156928 14 6136 42142 31 _ _ (2129763 / 100000) (1064883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776156928 :
    ThetaLowerSegment 1776156928 1776288000 (35522060897623 / 20000) (35524719702491 / 20000) := by
  exact
    packedTile65536 1776156928 1776288000 14 6242 42144 31 _ _ (212977 / 10000) (2129773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776288000 :
    ThetaLowerSegment 1776288000 1776419072 (35524719702491 / 20000)
      (177636754151161 / 100000) := by
  exact
    packedTile65536 1776288000 1776419072 14 6177 42146 31 _ _ (1064889 / 50000) (2129781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776419072 :
    ThetaLowerSegment 1776419072 1776550144 (177636754151161 / 100000)
      (88824891023003 / 50000) := by
  exact
    packedTile65536 1776419072 1776550144 14 6117 42147 31 _ _ (425957 / 20000) (532447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776550144 :
    ThetaLowerSegment 1776550144 1776681216 (88824891023003 / 50000) (88831504027163 / 50000) := by
  exact
    packedTile65536 1776550144 1776681216 14 6210 42149 31 _ _ (66556 / 3125) (425959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776681216 :
    ThetaLowerSegment 1776681216 1776812288 (88831504027163 / 50000) (88838104277363 / 50000) := by
  exact
    packedTile65536 1776681216 1776812288 14 6198 42150 31 _ _ (10649 / 500) (2129803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776812288 :
    ThetaLowerSegment 1776812288 1776943360 (88838104277363 / 50000) (88844583150257 / 50000) := by
  exact
    packedTile65536 1776812288 1776943360 14 6084 42152 31 _ _ (2129807 / 100000) (212981 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1776943360 :
    ThetaLowerSegment 1776943360 1777074432 (88844583150257 / 50000)
      (177702207157759 / 100000) := by
  exact
    packedTile65536 1776943360 1777074432 14 6123 42153 31 _ _ (425963 / 20000) (1064909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777074432 :
    ThetaLowerSegment 1777074432 1777205504 (177702207157759 / 100000)
      (35543102857123 / 20000) := by
  exact
    packedTile65536 1777074432 1777205504 14 6248 42155 31 _ _ (1064911 / 50000) (85193 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777205504 :
    ThetaLowerSegment 1777205504 1777336576 (35543102857123 / 20000) (88864273354633 / 50000) := by
  exact
    packedTile65536 1777205504 1777336576 14 6119 42156 31 _ _ (2129829 / 100000) (266229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777336576 :
    ThetaLowerSegment 1777336576 1777467648 (88864273354633 / 50000) (22217699261341 / 12500) := by
  exact
    packedTile65536 1777336576 1777467648 14 6126 42158 31 _ _ (2129837 / 100000) (26623 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777467648 :
    ThetaLowerSegment 1777467648 1777598720 (22217699261341 / 12500) (5554834144729 / 3125) := by
  exact
    packedTile65536 1777467648 1777598720 14 6150 42160 31 _ _ (532461 / 25000) (2129847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777598720 :
    ThetaLowerSegment 1777598720 1777729792 (5554834144729 / 3125) (88883870049277 / 50000) := by
  exact
    packedTile65536 1777598720 1777729792 14 6126 42161 31 _ _ (2129851 / 100000) (1064927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777729792 :
    ThetaLowerSegment 1777729792 1777860864 (88883870049277 / 50000)
      (177780725848877 / 100000) := by
  exact
    packedTile65536 1777729792 1777860864 14 6097 42163 31 _ _ (2129859 / 100000) (1064931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777860864 :
    ThetaLowerSegment 1777860864 1777991936 (177780725848877 / 100000)
      (177793858602633 / 100000) := by
  exact
    packedTile65536 1777860864 1777991936 14 6166 42164 31 _ _ (1064933 / 50000) (2129869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777991936 :
    ThetaLowerSegment 1777991936 1778123008 (177793858602633 / 100000)
      (177806950938111 / 100000) := by
  exact
    packedTile65536 1777991936 1778123008 14 6147 42166 31 _ _ (1064937 / 50000) (2129877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778123008 :
    ThetaLowerSegment 1778123008 1778254080 (177806950938111 / 100000)
      (177820177499121 / 100000) := by
  exact
    packedTile65536 1778123008 1778254080 14 6210 42167 31 _ _ (2129881 / 100000) (532471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778254080 :
    ThetaLowerSegment 1778254080 1778385152 (177820177499121 / 100000)
      (35566684228541 / 20000) := by
  exact
    packedTile65536 1778254080 1778385152 14 6218 42169 31 _ _ (66559 / 3125) (2129891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778385152 :
    ThetaLowerSegment 1778385152 1778516224 (35566684228541 / 20000)
      (177846447586641 / 100000) := by
  exact
    packedTile65536 1778385152 1778516224 14 6116 42170 31 _ _ (266237 / 12500) (2129899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778516224 :
    ThetaLowerSegment 1778516224 1778647296 (177846447586641 / 100000)
      (35571938264699 / 20000) := by
  exact
    packedTile65536 1778516224 1778647296 14 6218 42172 31 _ _ (2129903 / 100000) (1064953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778647296 :
    ThetaLowerSegment 1778647296 1778778368 (35571938264699 / 20000) (7114909310497 / 4000) := by
  exact
    packedTile65536 1778647296 1778778368 14 6123 42174 31 _ _ (212991 / 10000) (2129913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778778368 :
    ThetaLowerSegment 1778778368 1778909440 (7114909310497 / 4000) (177885829628207 / 100000) := by
  exact
    packedTile65536 1778778368 1778909440 14 6149 42175 31 _ _ (1064959 / 50000) (2129921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1778909440 :
    ThetaLowerSegment 1778909440 1779040512 (177885829628207 / 100000)
      (177898962745757 / 100000) := by
  exact
    packedTile65536 1778909440 1779040512 14 6166 42177 31 _ _ (85197 / 4000) (266241 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779040512 :
    ThetaLowerSegment 1779040512 1779171584 (177898962745757 / 100000)
      (177912083133037 / 100000) := by
  exact
    packedTile65536 1779040512 1779171584 14 6160 42178 31 _ _ (2129933 / 100000) (133121 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779171584 :
    ThetaLowerSegment 1779171584 1779302656 (177912083133037 / 100000)
      (177925254681997 / 100000) := by
  exact
    packedTile65536 1779171584 1779302656 14 6184 42180 31 _ _ (106497 / 5000) (2129943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779302656 :
    ThetaLowerSegment 1779302656 1779433728 (177925254681997 / 100000)
      (177938264398273 / 100000) := by
  exact
    packedTile65536 1779302656 1779433728 14 6108 42181 31 _ _ (2129947 / 100000) (42599 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779433728 :
    ThetaLowerSegment 1779433728 1779564800 (177938264398273 / 100000) (11121968613043 / 6250) := by
  exact
    packedTile65536 1779433728 1779564800 14 6213 42183 31 _ _ (425991 / 20000) (1064979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779564800 :
    ThetaLowerSegment 1779564800 1779695872 (11121968613043 / 6250) (17796466310381 / 10000) := by
  exact
    packedTile65536 1779564800 1779695872 14 6181 42184 31 _ _ (1064981 / 50000) (425993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779695872 :
    ThetaLowerSegment 1779695872 1779826944 (17796466310381 / 10000) (22247250121211 / 12500) := by
  exact
    packedTile65536 1779695872 1779826944 14 6262 42186 31 _ _ (2129969 / 100000) (532493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779826944 :
    ThetaLowerSegment 1779826944 1779958016 (22247250121211 / 12500) (711964026437 / 400) := by
  exact
    packedTile65536 1779826944 1779958016 14 6106 42187 31 _ _ (2129977 / 100000) (106499 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779958016 :
    ThetaLowerSegment 1779958016 1780089088 (711964026437 / 400) (89002011470737 / 50000) := by
  exact
    packedTile65536 1779958016 1780089088 14 6111 42189 31 _ _ (66562 / 3125) (2129987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780089088 :
    ThetaLowerSegment 1780089088 1780220160 (89002011470737 / 50000)
      (178017256575557 / 100000) := by
  exact
    packedTile65536 1780089088 1780220160 14 6213 42191 31 _ _ (2129991 / 100000) (1064997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780220160 :
    ThetaLowerSegment 1780220160 1780351232 (178017256575557 / 100000) (3560609549587 / 2000) := by
  exact
    packedTile65536 1780220160 1780351232 14 6207 42192 31 _ _ (2129999 / 100000) (1065001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780351232 :
    ThetaLowerSegment 1780351232 1780482304 (3560609549587 / 2000) (44510900111579 / 25000) := by
  exact
    packedTile65536 1780351232 1780482304 14 6161 42194 31 _ _ (1065003 / 50000) (2130009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780482304 :
    ThetaLowerSegment 1780482304 1780613376 (44510900111579 / 25000) (44514152642957 / 25000) := by
  exact
    packedTile65536 1780482304 1780613376 14 6108 42195 31 _ _ (1065007 / 50000) (2130017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780613376 :
    ThetaLowerSegment 1780613376 1780744448 (44514152642957 / 25000)
      (178069673990621 / 100000) := by
  exact
    packedTile65536 1780613376 1780744448 14 6133 42197 31 _ _ (2130021 / 100000) (266253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780744448 :
    ThetaLowerSegment 1780744448 1780875520 (178069673990621 / 100000)
      (178082997315761 / 100000) := by
  exact
    packedTile65536 1780744448 1780875520 14 6255 42198 31 _ _ (532507 / 25000) (2130031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1780875520 :
    ThetaLowerSegment 1780875520 1781006592 (178082997315761 / 100000)
      (178096035266117 / 100000) := by
  exact
    packedTile65536 1780875520 1781006592 14 6121 42200 31 _ _ (532509 / 25000) (2130039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781006592 :
    ThetaLowerSegment 1781006592 1781137664 (178096035266117 / 100000)
      (89054534499617 / 50000) := by
  exact
    packedTile65536 1781006592 1781137664 14 6119 42201 31 _ _ (2130043 / 100000) (1065023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781137664 :
    ThetaLowerSegment 1781137664 1781268736 (89054534499617 / 50000) (89061046062467 / 50000) := by
  exact
    packedTile65536 1781137664 1781268736 14 6114 42203 31 _ _ (42601 / 2000) (2130053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781268736 :
    ThetaLowerSegment 1781268736 1781399808 (89061046062467 / 50000) (89067593860759 / 50000) := by
  exact
    packedTile65536 1781268736 1781399808 14 6148 42205 31 _ _ (1065029 / 50000) (2130061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781399808 :
    ThetaLowerSegment 1781399808 1781530880 (89067593860759 / 50000)
      (178148323832373 / 100000) := by
  exact
    packedTile65536 1781399808 1781530880 14 6167 42206 31 _ _ (426013 / 20000) (532517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781530880 :
    ThetaLowerSegment 1781530880 1781661952 (178148323832373 / 100000)
      (178161366263229 / 100000) := by
  exact
    packedTile65536 1781530880 1781661952 14 6123 42208 31 _ _ (266259 / 12500) (85203 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781661952 :
    ThetaLowerSegment 1781661952 1781793024 (178161366263229 / 100000)
      (178174502466589 / 100000) := by
  exact
    packedTile65536 1781661952 1781793024 14 6167 42209 31 _ _ (13313 / 625) (2130083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781793024 :
    ThetaLowerSegment 1781793024 1781924096 (178174502466589 / 100000)
      (178187410793809 / 100000) := by
  exact
    packedTile65536 1781793024 1781924096 14 6060 42211 31 _ _ (2130087 / 100000) (213009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781924096 :
    ThetaLowerSegment 1781924096 1782055168 (178187410793809 / 100000)
      (178200506611721 / 100000) := by
  exact
    packedTile65536 1781924096 1782055168 14 6148 42212 31 _ _ (1065047 / 50000) (2130097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782055168 :
    ThetaLowerSegment 1782055168 1782186240 (178200506611721 / 100000)
      (178213700463509 / 100000) := by
  exact
    packedTile65536 1782055168 1782186240 14 6194 42214 31 _ _ (1065051 / 50000) (426021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782186240 :
    ThetaLowerSegment 1782186240 1782317312 (178213700463509 / 100000)
      (178226647266011 / 100000) := by
  exact
    packedTile65536 1782186240 1782317312 14 6078 42215 31 _ _ (2130109 / 100000) (66566 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782317312 :
    ThetaLowerSegment 1782317312 1782448384 (178226647266011 / 100000)
      (178239675061583 / 100000) := by
  exact
    packedTile65536 1782317312 1782448384 14 6116 42217 31 _ _ (2130117 / 100000) (53253 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782448384 :
    ThetaLowerSegment 1782448384 1782579456 (178239675061583 / 100000)
      (178252879700259 / 100000) := by
  exact
    packedTile65536 1782448384 1782579456 14 6199 42219 31 _ _ (532531 / 25000) (2130127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782579456 :
    ThetaLowerSegment 1782579456 1782710528 (178252879700259 / 100000)
      (44566493403879 / 25000) := by
  exact
    packedTile65536 1782579456 1782710528 14 6147 42220 31 _ _ (2130131 / 100000) (1065067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782710528 :
    ThetaLowerSegment 1782710528 1782841600 (44566493403879 / 25000) (35655853562603 / 20000) := by
  exact
    packedTile65536 1782710528 1782841600 14 6241 42222 31 _ _ (2130139 / 100000) (1065071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782841600 :
    ThetaLowerSegment 1782841600 1782972672 (35655853562603 / 20000) (35658494943643 / 20000) := by
  exact
    packedTile65536 1782841600 1782972672 14 6200 42223 31 _ _ (1065073 / 50000) (2130149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1782972672 :
    ThetaLowerSegment 1782972672 1783103744 (35658494943643 / 20000) (7132220450183 / 4000) := by
  exact
    packedTile65536 1782972672 1783103744 14 6120 42225 31 _ _ (2130153 / 100000) (532539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783103744 :
    ThetaLowerSegment 1783103744 1783234816 (7132220450183 / 4000) (178318543579573 / 100000) := by
  exact
    packedTile65536 1783103744 1783234816 14 6118 42226 31 _ _ (2130161 / 100000) (532541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783234816 :
    ThetaLowerSegment 1783234816 1783365888 (178318543579573 / 100000)
      (178331752751341 / 100000) := by
  exact
    packedTile65536 1783234816 1783365888 14 6201 42228 31 _ _ (266271 / 12500) (2130171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783365888 :
    ThetaLowerSegment 1783365888 1783496960 (178331752751341 / 100000)
      (178344866108641 / 100000) := by
  exact
    packedTile65536 1783365888 1783496960 14 6156 42229 31 _ _ (85207 / 4000) (1065089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783496960 :
    ThetaLowerSegment 1783496960 1783628032 (178344866108641 / 100000)
      (35671583974013 / 20000) := by
  exact
    packedTile65536 1783496960 1783628032 14 6128 42231 31 _ _ (2130183 / 100000) (1065093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783628032 :
    ThetaLowerSegment 1783628032 1783759104 (35671583974013 / 20000) (35674230948107 / 20000) := by
  exact
    packedTile65536 1783628032 1783759104 14 6213 42233 31 _ _ (213019 / 10000) (2130193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783759104 :
    ThetaLowerSegment 1783759104 1783890176 (35674230948107 / 20000)
      (178384183025387 / 100000) := by
  exact
    packedTile65536 1783759104 1783890176 14 6116 42234 31 _ _ (2130197 / 100000) (10651 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1783890176 :
    ThetaLowerSegment 1783890176 1784021248 (178384183025387 / 100000)
      (178397096328097 / 100000) := by
  exact
    packedTile65536 1783890176 1784021248 14 6062 42236 31 _ _ (426041 / 20000) (66569 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784021248 :
    ThetaLowerSegment 1784021248 1784152320 (178397096328097 / 100000)
      (178410314293557 / 100000) := by
  exact
    packedTile65536 1784021248 1784152320 14 6205 42237 31 _ _ (532553 / 25000) (426043 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784152320 :
    ThetaLowerSegment 1784152320 1784283392 (178410314293557 / 100000)
      (89211717156189 / 50000) := by
  exact
    packedTile65536 1784152320 1784283392 14 6159 42239 31 _ _ (2130219 / 100000) (1065111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784283392 :
    ThetaLowerSegment 1784283392 1784414464 (89211717156189 / 50000) (44609116760291 / 25000) := by
  exact
    packedTile65536 1784283392 1784414464 14 6118 42240 31 _ _ (2130227 / 100000) (213023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784414464 :
    ThetaLowerSegment 1784414464 1784545536 (44609116760291 / 25000) (22306187476597 / 12500) := by
  exact
    packedTile65536 1784414464 1784545536 14 6118 42242 31 _ _ (1065117 / 50000) (2130237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784545536 :
    ThetaLowerSegment 1784545536 1784676608 (22306187476597 / 12500) (22307832022649 / 12500) := by
  exact
    packedTile65536 1784545536 1784676608 14 6176 42243 31 _ _ (2130241 / 100000) (532561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784676608 :
    ThetaLowerSegment 1784676608 1784807680 (22307832022649 / 12500) (8923798724897 / 5000) := by
  exact
    packedTile65536 1784676608 1784807680 14 6252 42245 31 _ _ (2130249 / 100000) (532563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784807680 :
    ThetaLowerSegment 1784807680 1784938752 (8923798724897 / 5000) (44622263034881 / 25000) := by
  exact
    packedTile65536 1784807680 1784938752 14 6139 42246 31 _ _ (133141 / 6250) (2130259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1784938752 :
    ThetaLowerSegment 1784938752 1785069824 (44622263034881 / 25000) (89251106452169 / 50000) := by
  exact
    packedTile65536 1784938752 1785069824 14 6178 42248 31 _ _ (2130263 / 100000) (1065133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785069824 :
    ThetaLowerSegment 1785069824 1785200896 (89251106452169 / 50000) (1428121609333 / 800) := by
  exact
    packedTile65536 1785069824 1785200896 14 6097 42250 31 _ _ (2130271 / 100000) (1065137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785200896 :
    ThetaLowerSegment 1785200896 1785331968 (1428121609333 / 800) (178528406759947 / 100000) := by
  exact
    packedTile65536 1785200896 1785331968 14 6199 42251 31 _ _ (1065139 / 50000) (2130281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785331968 :
    ThetaLowerSegment 1785331968 1785463040 (178528406759947 / 100000)
      (178541512279419 / 100000) := by
  exact
    packedTile65536 1785331968 1785463040 14 6152 42253 31 _ _ (1065143 / 50000) (2130289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785463040 :
    ThetaLowerSegment 1785463040 1785594112 (178541512279419 / 100000)
      (178554771223051 / 100000) := by
  exact
    packedTile65536 1785463040 1785594112 14 6224 42254 31 _ _ (2130293 / 100000) (266287 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785594112 :
    ThetaLowerSegment 1785594112 1785725184 (178554771223051 / 100000)
      (178567804398451 / 100000) := by
  exact
    packedTile65536 1785594112 1785725184 14 6118 42256 31 _ _ (21303 / 1000) (2130303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785725184 :
    ThetaLowerSegment 1785725184 1785856256 (178567804398451 / 100000)
      (178580831231871 / 100000) := by
  exact
    packedTile65536 1785725184 1785856256 14 6115 42257 31 _ _ (532577 / 25000) (2130311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785856256 :
    ThetaLowerSegment 1785856256 1785987328 (178580831231871 / 100000)
      (89296969530033 / 50000) := by
  exact
    packedTile65536 1785856256 1785987328 14 6153 42259 31 _ _ (426063 / 20000) (1065159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1785987328 :
    ThetaLowerSegment 1785987328 1786118400 (89296969530033 / 50000) (44651712735427 / 25000) := by
  exact
    packedTile65536 1785987328 1786118400 14 6061 42260 31 _ _ (1065161 / 50000) (85213 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786118400 :
    ThetaLowerSegment 1786118400 1786249472 (44651712735427 / 25000) (89310030559019 / 50000) := by
  exact
    packedTile65536 1786118400 1786249472 14 6201 42262 31 _ _ (213033 / 10000) (2130333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786249472 :
    ThetaLowerSegment 1786249472 1786380544 (89310030559019 / 50000)
      (178633275598449 / 100000) := by
  exact
    packedTile65536 1786249472 1786380544 14 6203 42264 31 _ _ (2130337 / 100000) (106517 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786380544 :
    ThetaLowerSegment 1786380544 1786511616 (178633275598449 / 100000)
      (178646223829281 / 100000) := by
  exact
    packedTile65536 1786380544 1786511616 14 6078 42265 31 _ _ (266293 / 12500) (2130347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786511616 :
    ThetaLowerSegment 1786511616 1786642688 (178646223829281 / 100000)
      (178659261583521 / 100000) := by
  exact
    packedTile65536 1786511616 1786642688 14 6120 42267 31 _ _ (133147 / 6250) (426071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786642688 :
    ThetaLowerSegment 1786642688 1786773760 (178659261583521 / 100000)
      (178672427202141 / 100000) := by
  exact
    packedTile65536 1786642688 1786773760 14 6180 42268 31 _ _ (2130359 / 100000) (1065181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786773760 :
    ThetaLowerSegment 1786773760 1786904832 (178672427202141 / 100000)
      (178685424565107 / 100000) := by
  exact
    packedTile65536 1786773760 1786904832 14 6101 42270 31 _ _ (1065183 / 50000) (2130369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1786904832 :
    ThetaLowerSegment 1786904832 1787035904 (178685424565107 / 100000)
      (178698688273631 / 100000) := by
  exact
    packedTile65536 1786904832 1787035904 14 6226 42271 31 _ _ (1065187 / 50000) (2130377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787035904 :
    ThetaLowerSegment 1787035904 1787166976 (178698688273631 / 100000)
      (35742342684613 / 20000) := by
  exact
    packedTile65536 1787035904 1787166976 14 6114 42273 31 _ _ (2130381 / 100000) (133149 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787166976 :
    ThetaLowerSegment 1787166976 1787298048 (35742342684613 / 20000) (35744999278449 / 20000) := by
  exact
    packedTile65536 1787166976 1787298048 14 6235 42274 31 _ _ (532597 / 25000) (2130391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787298048 :
    ThetaLowerSegment 1787298048 1787429120 (35744999278449 / 20000)
      (178738042937349 / 100000) := by
  exact
    packedTile65536 1787298048 1787429120 14 6124 42276 31 _ _ (532599 / 25000) (2130399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787429120 :
    ThetaLowerSegment 1787429120 1787560192 (178738042937349 / 100000)
      (178751140654993 / 100000) := by
  exact
    packedTile65536 1787429120 1787560192 14 6148 42277 31 _ _ (2130403 / 100000) (1065203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787560192 :
    ThetaLowerSegment 1787560192 1787691264 (178751140654993 / 100000)
      (178764176633783 / 100000) := by
  exact
    packedTile65536 1787560192 1787691264 14 6119 42279 31 _ _ (213041 / 10000) (2130413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787691264 :
    ThetaLowerSegment 1787691264 1787822336 (178764176633783 / 100000)
      (178777312791171 / 100000) := by
  exact
    packedTile65536 1787691264 1787822336 14 6166 42281 31 _ _ (1065209 / 50000) (2130421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787822336 :
    ThetaLowerSegment 1787822336 1787953408 (178777312791171 / 100000) (11174407189681 / 6250) := by
  exact
    packedTile65536 1787822336 1787953408 14 6197 42282 31 _ _ (85217 / 4000) (532607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1787953408 :
    ThetaLowerSegment 1787953408 1788084480 (11174407189681 / 6250) (11175222878833 / 6250) := by
  exact
    packedTile65536 1787953408 1788084480 14 6126 42284 31 _ _ (66576 / 3125) (426087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788084480 :
    ThetaLowerSegment 1788084480 1788215552 (11175222878833 / 6250) (5588020084439 / 3125) := by
  exact
    packedTile65536 1788084480 1788215552 14 6138 42285 31 _ _ (53261 / 2500) (2130443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788215552 :
    ThetaLowerSegment 1788215552 1788346624 (5588020084439 / 3125) (22353705868817 / 12500) := by
  exact
    packedTile65536 1788215552 1788346624 14 6104 42287 31 _ _ (2130447 / 100000) (42609 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788346624 :
    ThetaLowerSegment 1788346624 1788477696 (22353705868817 / 12500) (17884292180941 / 10000) := by
  exact
    packedTile65536 1788346624 1788477696 14 6231 42288 31 _ _ (1065227 / 50000) (2130457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788477696 :
    ThetaLowerSegment 1788477696 1788608768 (17884292180941 / 10000) (44713974613363 / 25000) := by
  exact
    packedTile65536 1788477696 1788608768 14 6091 42290 31 _ _ (1065231 / 50000) (426093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788608768 :
    ThetaLowerSegment 1788608768 1788739840 (44713974613363 / 25000) (89434432243893 / 50000) := by
  exact
    packedTile65536 1788608768 1788739840 14 6086 42291 31 _ _ (2130469 / 100000) (266309 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788739840 :
    ThetaLowerSegment 1788739840 1788870912 (89434432243893 / 50000) (89440980261879 / 50000) := by
  exact
    packedTile65536 1788739840 1788870912 14 6147 42293 31 _ _ (532619 / 25000) (2130479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1788870912 :
    ThetaLowerSegment 1788870912 1789001984 (89440980261879 / 50000) (89447468650901 / 50000) := by
  exact
    packedTile65536 1788870912 1789001984 14 6091 42295 31 _ _ (532621 / 25000) (2130487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789001984 :
    ThetaLowerSegment 1789001984 1789133056 (89447468650901 / 50000) (17890829121939 / 10000) := by
  exact
    packedTile65536 1789001984 1789133056 14 6268 42296 31 _ _ (2130491 / 100000) (1065247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789133056 :
    ThetaLowerSegment 1789133056 1789264128 (17890829121939 / 10000) (223651728912 / 125) := by
  exact
    packedTile65536 1789133056 1789264128 14 6145 42298 31 _ _ (1065249 / 50000) (2130501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789264128 :
    ThetaLowerSegment 1789264128 1789395200 (223651728912 / 125) (5591700149446 / 3125) := by
  exact
    packedTile65536 1789264128 1789395200 14 6112 42299 31 _ _ (1065253 / 50000) (2130509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789395200 :
    ThetaLowerSegment 1789395200 1789526272 (5591700149446 / 3125) (17894749891517 / 10000) := by
  exact
    packedTile65536 1789395200 1789526272 14 6146 42301 31 _ _ (2130513 / 100000) (532629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789526272 :
    ThetaLowerSegment 1789526272 1789657344 (17894749891517 / 10000) (17896052704497 / 10000) := by
  exact
    packedTile65536 1789526272 1789657344 14 6115 42302 31 _ _ (53263 / 2500) (2130523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789657344 :
    ThetaLowerSegment 1789657344 1789788416 (17896052704497 / 10000) (89486941662501 / 50000) := by
  exact
    packedTile65536 1789657344 1789788416 14 6269 42304 31 _ _ (66579 / 3125) (2130531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789788416 :
    ThetaLowerSegment 1789788416 1789919488 (89486941662501 / 50000) (44746763573093 / 25000) := by
  exact
    packedTile65536 1789788416 1789919488 14 6182 42305 31 _ _ (426107 / 20000) (1065269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1789919488 :
    ThetaLowerSegment 1789919488 1790050560 (44746763573093 / 25000) (11187507157177 / 6250) := by
  exact
    packedTile65536 1789919488 1790050560 14 6130 42307 31 _ _ (1065271 / 50000) (426109 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790050560 :
    ThetaLowerSegment 1790050560 1790181632 (11187507157177 / 6250) (89506625739983 / 50000) := by
  exact
    packedTile65536 1790050560 1790181632 14 6166 42308 31 _ _ (2130549 / 100000) (266319 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790181632 :
    ThetaLowerSegment 1790181632 1790312704 (89506625739983 / 50000) (7161053068331 / 4000) := by
  exact
    packedTile65536 1790181632 1790312704 14 6137 42310 31 _ _ (2130557 / 100000) (13316 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790312704 :
    ThetaLowerSegment 1790312704 1790443776 (7161053068331 / 4000) (179039393457287 / 100000) := by
  exact
    packedTile65536 1790312704 1790443776 14 6133 42312 31 _ _ (532641 / 25000) (2130567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790443776 :
    ThetaLowerSegment 1790443776 1790574848 (179039393457287 / 100000)
      (89526259952609 / 50000) := by
  exact
    packedTile65536 1790443776 1790574848 14 6161 42313 31 _ _ (2130571 / 100000) (1065287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790574848 :
    ThetaLowerSegment 1790574848 1790705920 (89526259952609 / 50000) (89532860486351 / 50000) := by
  exact
    packedTile65536 1790574848 1790705920 14 6196 42315 31 _ _ (2130579 / 100000) (1065291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790705920 :
    ThetaLowerSegment 1790705920 1790836992 (89532860486351 / 50000) (89539390732441 / 50000) := by
  exact
    packedTile65536 1790705920 1790836992 14 6130 42316 31 _ _ (1065293 / 50000) (2130589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790836992 :
    ThetaLowerSegment 1790836992 1790968064 (89539390732441 / 50000) (17909198261911 / 10000) := by
  exact
    packedTile65536 1790836992 1790968064 14 6196 42318 31 _ _ (2130593 / 100000) (532649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1790968064 :
    ThetaLowerSegment 1790968064 1791099136 (17909198261911 / 10000)
      (179104930281387 / 100000) := by
  exact
    packedTile65536 1790968064 1791099136 14 6077 42319 31 _ _ (2130601 / 100000) (532651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791099136 :
    ThetaLowerSegment 1791099136 1791230208 (179104930281387 / 100000)
      (179118042043019 / 100000) := by
  exact
    packedTile65536 1791099136 1791230208 14 6154 42321 31 _ _ (133163 / 6250) (2130611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791230208 :
    ThetaLowerSegment 1791230208 1791361280 (179118042043019 / 100000)
      (179131072884359 / 100000) := by
  exact
    packedTile65536 1791230208 1791361280 14 6116 42322 31 _ _ (426123 / 20000) (1065309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791361280 :
    ThetaLowerSegment 1791361280 1791492352 (179131072884359 / 100000)
      (179144214567023 / 100000) := by
  exact
    packedTile65536 1791361280 1791492352 14 6168 42324 31 _ _ (2130623 / 100000) (1065313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791492352 :
    ThetaLowerSegment 1791492352 1791623424 (179144214567023 / 100000)
      (179157375468533 / 100000) := by
  exact
    packedTile65536 1791492352 1791623424 14 6177 42326 31 _ _ (213063 / 10000) (2130633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791623424 :
    ThetaLowerSegment 1791623424 1791754496 (179157375468533 / 100000)
      (35834072766337 / 20000) := by
  exact
    packedTile65536 1791623424 1791754496 14 6096 42327 31 _ _ (2130637 / 100000) (26633 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791754496 :
    ThetaLowerSegment 1791754496 1791885568 (35834072766337 / 20000) (8959178158873 / 5000) := by
  exact
    packedTile65536 1791754496 1791885568 14 6195 42329 31 _ _ (426129 / 20000) (266331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1791885568 :
    ThetaLowerSegment 1791885568 1792016640 (8959178158873 / 5000) (44799194370291 / 25000) := by
  exact
    packedTile65536 1791885568 1792016640 14 6202 42330 31 _ _ (532663 / 25000) (426131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792016640 :
    ThetaLowerSegment 1792016640 1792147712 (44799194370291 / 25000) (44802496891741 / 25000) := by
  exact
    packedTile65536 1792016640 1792147712 14 6200 42332 31 _ _ (2130659 / 100000) (1065331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792147712 :
    ThetaLowerSegment 1792147712 1792278784 (44802496891741 / 25000)
      (179223187049029 / 100000) := by
  exact
    packedTile65536 1792147712 1792278784 14 6195 42333 31 _ _ (2130667 / 100000) (213067 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792278784 :
    ThetaLowerSegment 1792278784 1792409856 (179223187049029 / 100000)
      (179236367398393 / 100000) := by
  exact
    packedTile65536 1792278784 1792409856 14 6186 42335 31 _ _ (1065337 / 50000) (2130677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792409856 :
    ThetaLowerSegment 1792409856 1792540928 (179236367398393 / 100000) (5601545505368 / 3125) := by
  exact
    packedTile65536 1792409856 1792540928 14 6143 42336 31 _ _ (2130681 / 100000) (532671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792540928 :
    ThetaLowerSegment 1792540928 1792672000 (5601545505368 / 3125) (5601955063552 / 3125) := by
  exact
    packedTile65536 1792540928 1792672000 14 6151 42338 31 _ _ (66584 / 3125) (2130691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792672000 :
    ThetaLowerSegment 1792672000 1792803072 (5601955063552 / 3125) (5602361760151 / 3125) := by
  exact
    packedTile65536 1792672000 1792803072 14 6108 42339 31 _ _ (266337 / 12500) (2130699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792803072 :
    ThetaLowerSegment 1792803072 1792934144 (5602361760151 / 3125) (44822190278749 / 25000) := by
  exact
    packedTile65536 1792803072 1792934144 14 6188 42341 31 _ _ (2130703 / 100000) (1065353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792934144 :
    ThetaLowerSegment 1792934144 1793065216 (44822190278749 / 25000) (89651003869533 / 50000) := by
  exact
    packedTile65536 1792934144 1793065216 14 6217 42343 31 _ _ (213071 / 10000) (2130713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793065216 :
    ThetaLowerSegment 1793065216 1793196288 (89651003869533 / 50000) (44828755008473 / 25000) := by
  exact
    packedTile65536 1793065216 1793196288 14 6107 42344 31 _ _ (1065359 / 50000) (2130721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793196288 :
    ThetaLowerSegment 1793196288 1793327360 (44828755008473 / 25000)
      (179328113339017 / 100000) := by
  exact
    packedTile65536 1793196288 1793327360 14 6145 42346 31 _ _ (85229 / 4000) (266341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793327360 :
    ThetaLowerSegment 1793327360 1793458432 (179328113339017 / 100000)
      (179341419760357 / 100000) := by
  exact
    packedTile65536 1793327360 1793458432 14 6245 42347 31 _ _ (532683 / 25000) (426147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793458432 :
    ThetaLowerSegment 1793458432 1793589504 (179341419760357 / 100000)
      (179354372528817 / 100000) := by
  exact
    packedTile65536 1793458432 1793589504 14 6079 42349 31 _ _ (106537 / 5000) (2130743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793589504 :
    ThetaLowerSegment 1793589504 1793720576 (179354372528817 / 100000)
      (17936749579959 / 10000) := by
  exact
    packedTile65536 1793589504 1793720576 14 6159 42350 31 _ _ (2130747 / 100000) (8523 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793720576 :
    ThetaLowerSegment 1793720576 1793851648 (17936749579959 / 10000) (44845146255353 / 25000) := by
  exact
    packedTile65536 1793720576 1793851648 14 6143 42352 31 _ _ (1065377 / 50000) (2130757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793851648 :
    ThetaLowerSegment 1793851648 1793982720 (44845146255353 / 25000) (89696807315521 / 50000) := by
  exact
    packedTile65536 1793851648 1793982720 14 6115 42353 31 _ _ (1065381 / 50000) (426153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1793982720 :
    ThetaLowerSegment 1793982720 1794113792 (89696807315521 / 50000)
      (179406780652693 / 100000) := by
  exact
    packedTile65536 1793982720 1794113792 14 6179 42355 31 _ _ (2130769 / 100000) (532693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794113792 :
    ThetaLowerSegment 1794113792 1794244864 (179406780652693 / 100000) (7176789601293 / 4000) := by
  exact
    packedTile65536 1794113792 1794244864 14 6082 42356 31 _ _ (266347 / 12500) (2130779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794244864 :
    ThetaLowerSegment 1794244864 1794375936 (7176789601293 / 4000) (179432946631557 / 100000) := by
  exact
    packedTile65536 1794244864 1794375936 14 6198 42358 31 _ _ (66587 / 3125) (2130787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794375936 :
    ThetaLowerSegment 1794375936 1794507008 (179432946631557 / 100000)
      (89723022301917 / 50000) := by
  exact
    packedTile65536 1794375936 1794507008 14 6147 42360 31 _ _ (2130791 / 100000) (1065397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794507008 :
    ThetaLowerSegment 1794507008 1794638080 (89723022301917 / 50000) (44864800570371 / 25000) := by
  exact
    packedTile65536 1794507008 1794638080 14 6175 42361 31 _ _ (1065399 / 50000) (2130801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794638080 :
    ThetaLowerSegment 1794638080 1794769152 (44864800570371 / 25000)
      (179472317386259 / 100000) := by
  exact
    packedTile65536 1794638080 1794769152 14 6155 42363 31 _ _ (426161 / 20000) (266351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794769152 :
    ThetaLowerSegment 1794769152 1794900224 (179472317386259 / 100000)
      (179485686107021 / 100000) := by
  exact
    packedTile65536 1794769152 1794900224 14 6274 42364 31 _ _ (2130813 / 100000) (66588 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1794900224 :
    ThetaLowerSegment 1794900224 1795031296 (179485686107021 / 100000)
      (179498709678861 / 100000) := by
  exact
    packedTile65536 1794900224 1795031296 14 6112 42366 31 _ _ (106541 / 5000) (2130823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795031296 :
    ThetaLowerSegment 1795031296 1795162368 (179498709678861 / 100000) (1436095059611 / 800) := by
  exact
    packedTile65536 1795031296 1795162368 14 6182 42367 31 _ _ (2130827 / 100000) (213083 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795162368 :
    ThetaLowerSegment 1795162368 1795293440 (1436095059611 / 800) (224406247176 / 125) := by
  exact
    packedTile65536 1795162368 1795293440 14 6155 42369 31 _ _ (426167 / 20000) (1065419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795293440 :
    ThetaLowerSegment 1795293440 1795424512 (224406247176 / 125) (44884517081407 / 25000) := by
  exact
    packedTile65536 1795293440 1795424512 14 6134 42370 31 _ _ (1065421 / 50000) (426169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795424512 :
    ThetaLowerSegment 1795424512 1795555584 (44884517081407 / 25000)
      (179551196486317 / 100000) := by
  exact
    packedTile65536 1795424512 1795555584 14 6161 42372 31 _ _ (2130849 / 100000) (532713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795555584 :
    ThetaLowerSegment 1795555584 1795686656 (179551196486317 / 100000)
      (89782136777863 / 50000) := by
  exact
    packedTile65536 1795555584 1795686656 14 6137 42373 31 _ _ (2130857 / 100000) (106543 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795686656 :
    ThetaLowerSegment 1795686656 1795817728 (89782136777863 / 50000) (89788673203183 / 50000) := by
  exact
    packedTile65536 1795686656 1795817728 14 6135 42375 31 _ _ (133179 / 6250) (2130867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795817728 :
    ThetaLowerSegment 1795817728 1795948800 (89788673203183 / 50000)
      (179590547152211 / 100000) := by
  exact
    packedTile65536 1795817728 1795948800 14 6195 42377 31 _ _ (2130871 / 100000) (1065437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1795948800 :
    ThetaLowerSegment 1795948800 1796079872 (179590547152211 / 100000)
      (35920748735933 / 20000) := by
  exact
    packedTile65536 1795948800 1796079872 14 6193 42378 31 _ _ (1065439 / 50000) (2130881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796079872 :
    ThetaLowerSegment 1796079872 1796210944 (35920748735933 / 20000) (35923380380143 / 20000) := by
  exact
    packedTile65536 1796079872 1796210944 14 6175 42380 31 _ _ (1065443 / 50000) (2130889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796210944 :
    ThetaLowerSegment 1796210944 1796342016 (35923380380143 / 20000)
      (179630058034097 / 100000) := by
  exact
    packedTile65536 1796210944 1796342016 14 6174 42381 31 _ _ (2130893 / 100000) (133181 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796342016 :
    ThetaLowerSegment 1796342016 1796473088 (179630058034097 / 100000)
      (179643331410197 / 100000) := by
  exact
    packedTile65536 1796342016 1796473088 14 6229 42383 31 _ _ (21309 / 1000) (2130903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796473088 :
    ThetaLowerSegment 1796473088 1796604160 (179643331410197 / 100000)
      (179656366174433 / 100000) := by
  exact
    packedTile65536 1796473088 1796604160 14 6117 42384 31 _ _ (532727 / 25000) (2130911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796604160 :
    ThetaLowerSegment 1796604160 1796735232 (179656366174433 / 100000)
      (179669296566653 / 100000) := by
  exact
    packedTile65536 1796604160 1796735232 14 6068 42386 31 _ _ (426183 / 20000) (1065459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796735232 :
    ThetaLowerSegment 1796735232 1796866304 (179669296566653 / 100000)
      (35936474380809 / 20000) := by
  exact
    packedTile65536 1796735232 1796866304 14 6136 42387 31 _ _ (1065461 / 50000) (85237 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796866304 :
    ThetaLowerSegment 1796866304 1796997376 (35936474380809 / 20000) (35939137617123 / 20000) := by
  exact
    packedTile65536 1796866304 1796997376 14 6249 42389 31 _ _ (213093 / 10000) (2130933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796997376 :
    ThetaLowerSegment 1796997376 1797128448 (35939137617123 / 20000) (44927214851803 / 25000) := by
  exact
    packedTile65536 1796997376 1797128448 14 6181 42391 31 _ _ (2130937 / 100000) (106547 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797128448 :
    ThetaLowerSegment 1797128448 1797259520 (44927214851803 / 25000) (44930525806043 / 25000) := by
  exact
    packedTile65536 1797128448 1797259520 14 6215 42392 31 _ _ (66592 / 3125) (2130947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797259520 :
    ThetaLowerSegment 1797259520 1797390592 (44930525806043 / 25000) (89867663953039 / 50000) := by
  exact
    packedTile65536 1797259520 1797390592 14 6206 42394 31 _ _ (2130951 / 100000) (1065477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797390592 :
    ThetaLowerSegment 1797390592 1797521664 (89867663953039 / 50000)
      (179748328886937 / 100000) := by
  exact
    packedTile65536 1797390592 1797521664 14 6101 42395 31 _ _ (2130959 / 100000) (1065481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797521664 :
    ThetaLowerSegment 1797521664 1797652736 (179748328886937 / 100000)
      (179761436458803 / 100000) := by
  exact
    packedTile65536 1797521664 1797652736 14 6151 42397 31 _ _ (1065483 / 50000) (2130969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797652736 :
    ThetaLowerSegment 1797652736 1797783808 (179761436458803 / 100000)
      (44943617905161 / 25000) := by
  exact
    packedTile65536 1797652736 1797783808 14 6117 42398 31 _ _ (2130973 / 100000) (66593 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797783808 :
    ThetaLowerSegment 1797783808 1797914880 (44943617905161 / 25000) (22473450873441 / 12500) := by
  exact
    packedTile65536 1797783808 1797914880 14 6164 42400 31 _ _ (2130981 / 100000) (266373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1797914880 :
    ThetaLowerSegment 1797914880 1798045952 (22473450873441 / 12500) (44950146708859 / 25000) := by
  exact
    packedTile65536 1797914880 1798045952 14 6091 42401 31 _ _ (532747 / 25000) (2130991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798045952 :
    ThetaLowerSegment 1798045952 1798177024 (44950146708859 / 25000)
      (179813779825481 / 100000) := by
  exact
    packedTile65536 1798045952 1798177024 14 6191 42403 31 _ _ (426199 / 20000) (1065499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798177024 :
    ThetaLowerSegment 1798177024 1798308096 (179813779825481 / 100000)
      (179826894011789 / 100000) := by
  exact
    packedTile65536 1798177024 1798308096 14 6154 42404 31 _ _ (1065501 / 50000) (426201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798308096 :
    ThetaLowerSegment 1798308096 1798439168 (179826894011789 / 100000)
      (179840214955299 / 100000) := by
  exact
    packedTile65536 1798308096 1798439168 14 6251 42406 31 _ _ (213101 / 10000) (2131013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798439168 :
    ThetaLowerSegment 1798439168 1798570240 (179840214955299 / 100000)
      (179853278089509 / 100000) := by
  exact
    packedTile65536 1798439168 1798570240 14 6130 42408 31 _ _ (2131017 / 100000) (106551 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798570240 :
    ThetaLowerSegment 1798570240 1798701312 (179853278089509 / 100000)
      (179866341266629 / 100000) := by
  exact
    packedTile65536 1798570240 1798701312 14 6130 42409 31 _ _ (133189 / 6250) (2131027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798701312 :
    ThetaLowerSegment 1798701312 1798832384 (179866341266629 / 100000)
      (179879472685813 / 100000) := by
  exact
    packedTile65536 1798701312 1798832384 14 6162 42411 31 _ _ (266379 / 12500) (426207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798832384 :
    ThetaLowerSegment 1798832384 1798963456 (179879472685813 / 100000)
      (179892812989953 / 100000) := by
  exact
    packedTile65536 1798832384 1798963456 14 6260 42412 31 _ _ (2131039 / 100000) (1065521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1798963456 :
    ThetaLowerSegment 1798963456 1799094528 (179892812989953 / 100000)
      (179905857122519 / 100000) := by
  exact
    packedTile65536 1798963456 1799094528 14 6121 42414 31 _ _ (1065523 / 50000) (2131049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799094528 :
    ThetaLowerSegment 1799094528 1799225600 (179905857122519 / 100000) (11244938257043 / 6250) := by
  exact
    packedTile65536 1799094528 1799225600 14 6173 42415 31 _ _ (2131053 / 100000) (133191 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799225600 :
    ThetaLowerSegment 1799225600 1799356672 (11244938257043 / 6250) (89966016447699 / 50000) := by
  exact
    packedTile65536 1799225600 1799356672 14 6110 42417 31 _ _ (2131061 / 100000) (266383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799356672 :
    ThetaLowerSegment 1799356672 1799487744 (89966016447699 / 50000) (89972562023061 / 50000) := by
  exact
    packedTile65536 1799356672 1799487744 14 6143 42418 31 _ _ (532767 / 25000) (2131071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799487744 :
    ThetaLowerSegment 1799487744 1799618816 (89972562023061 / 50000) (44989549015043 / 25000) := by
  exact
    packedTile65536 1799487744 1799618816 14 6134 42420 31 _ _ (85243 / 4000) (1065539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799618816 :
    ThetaLowerSegment 1799618816 1799749888 (44989549015043 / 25000)
      (179971300089539 / 100000) := by
  exact
    packedTile65536 1799618816 1799749888 14 6149 42421 31 _ _ (2131083 / 100000) (1065543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799749888 :
    ThetaLowerSegment 1799749888 1799880960 (179971300089539 / 100000)
      (179984280558729 / 100000) := by
  exact
    packedTile65536 1799749888 1799880960 14 6091 42423 31 _ _ (213109 / 10000) (2131093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1799880960 :
    ThetaLowerSegment 1799880960 1800012032 (179984280558729 / 100000)
      (179997544506457 / 100000) := by
  exact
    packedTile65536 1799880960 1800012032 14 6224 42425 31 _ _ (2131097 / 100000) (21311 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800012032 :
    ThetaLowerSegment 1800012032 1800143104 (179997544506457 / 100000)
      (180010682762617 / 100000) := by
  exact
    packedTile65536 1800012032 1800143104 14 6165 42426 31 _ _ (66597 / 3125) (2131107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800143104 :
    ThetaLowerSegment 1800143104 1800274176 (180010682762617 / 100000)
      (180023752872513 / 100000) := by
  exact
    packedTile65536 1800143104 1800274176 14 6133 42428 31 _ _ (266389 / 12500) (426223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800274176 :
    ThetaLowerSegment 1800274176 1800405248 (180023752872513 / 100000)
      (36007379522901 / 20000) := by
  exact
    packedTile65536 1800274176 1800405248 14 6168 42429 31 _ _ (2131119 / 100000) (1065561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800405248 :
    ThetaLowerSegment 1800405248 1800536320 (36007379522901 / 20000)
      (180050055186429 / 100000) := by
  exact
    packedTile65536 1800405248 1800536320 14 6174 42431 31 _ _ (1065563 / 50000) (2131129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800536320 :
    ThetaLowerSegment 1800536320 1800667392 (180050055186429 / 100000)
      (180063238381353 / 100000) := by
  exact
    packedTile65536 1800536320 1800667392 14 6186 42432 31 _ _ (1065567 / 50000) (2131137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800667392 :
    ThetaLowerSegment 1800667392 1800798464 (180063238381353 / 100000)
      (90038120236297 / 50000) := by
  exact
    packedTile65536 1800667392 1800798464 14 6101 42434 31 _ _ (2131141 / 100000) (266393 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800798464 :
    ThetaLowerSegment 1800798464 1800929536 (90038120236297 / 50000) (90044679909841 / 50000) := by
  exact
    packedTile65536 1800798464 1800929536 14 6156 42435 31 _ _ (532787 / 25000) (2131151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800929536 :
    ThetaLowerSegment 1800929536 1801060608 (90044679909841 / 50000)
      (180102366258647 / 100000) := by
  exact
    packedTile65536 1800929536 1801060608 14 6103 42437 31 _ _ (426231 / 20000) (1065579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801060608 :
    ThetaLowerSegment 1801060608 1801191680 (180102366258647 / 100000) (180115432419 / 100) := by
  exact
    packedTile65536 1801060608 1801191680 14 6131 42438 31 _ _ (2131163 / 100000) (1065583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801191680 :
    ThetaLowerSegment 1801191680 1801322752 (180115432419 / 100) (3602568864237 / 2000) := by
  exact
    packedTile65536 1801191680 1801322752 14 6105 42440 31 _ _ (213117 / 10000) (2131173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801322752 :
    ThetaLowerSegment 1801322752 1801339136 (3602568864237 / 2000) (36026010450097 / 20000) := by
  exact
    packedTile65536 1801322752 1801339136 11 755 42441 31 _ _ (2131177 / 100000) (106559 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801339136 :
    ThetaLowerSegment 1801339136 1801341184 (36026010450097 / 20000)
      (180130263237107 / 100000) := by
  exact
    packedTile65536 1801339136 1801341184 8 99 42442 31 _ _ (1065589 / 50000) (2131181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1769341184_1801341184 :
    ThetaLowerSegment 1769341184 1801341184 (176929258059137 / 100000)
      (180130263237107 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1769341184 cell1769472256)
                  (ThetaLowerSegment.join cell1769603328 cell1769734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1769865472 cell1769996544)
                  (ThetaLowerSegment.join cell1770127616 cell1770258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1770389760 cell1770520832)
                  (ThetaLowerSegment.join cell1770651904 cell1770782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1770914048 cell1771045120)
                  (ThetaLowerSegment.join cell1771176192 cell1771307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1771438336 cell1771569408)
                  (ThetaLowerSegment.join cell1771700480 cell1771831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1771962624 cell1772093696)
                  (ThetaLowerSegment.join cell1772224768 cell1772355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1772486912 cell1772617984)
                  (ThetaLowerSegment.join cell1772749056 cell1772880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1773011200 cell1773142272)
                  (ThetaLowerSegment.join cell1773273344 cell1773404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1773535488 cell1773666560)
                  (ThetaLowerSegment.join cell1773797632 cell1773928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1774059776 cell1774190848)
                  (ThetaLowerSegment.join cell1774321920 cell1774452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1774584064 cell1774715136)
                  (ThetaLowerSegment.join cell1774846208 cell1774977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1775108352 cell1775239424)
                  (ThetaLowerSegment.join cell1775370496 cell1775501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1775632640 cell1775763712)
                  (ThetaLowerSegment.join cell1775894784 cell1776025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1776156928 cell1776288000)
                  (ThetaLowerSegment.join cell1776419072 cell1776550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1776681216 cell1776812288)
                  (ThetaLowerSegment.join cell1776943360 cell1777074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1777205504 cell1777336576)
                  (ThetaLowerSegment.join cell1777467648 cell1777598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1777729792 cell1777860864)
                  (ThetaLowerSegment.join cell1777991936 cell1778123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1778254080 cell1778385152)
                  (ThetaLowerSegment.join cell1778516224 cell1778647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1778778368 cell1778909440)
                  (ThetaLowerSegment.join cell1779040512 cell1779171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1779302656 cell1779433728)
                  (ThetaLowerSegment.join cell1779564800 cell1779695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1779826944 cell1779958016)
                  (ThetaLowerSegment.join cell1780089088 cell1780220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1780351232 cell1780482304)
                  (ThetaLowerSegment.join cell1780613376 cell1780744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1780875520 cell1781006592)
                  (ThetaLowerSegment.join cell1781137664 cell1781268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1781399808 cell1781530880)
                  (ThetaLowerSegment.join cell1781661952 cell1781793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1781924096 cell1782055168)
                  (ThetaLowerSegment.join cell1782186240 cell1782317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1782448384 cell1782579456)
                  (ThetaLowerSegment.join cell1782710528 cell1782841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1782972672 cell1783103744)
                  (ThetaLowerSegment.join cell1783234816 cell1783365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1783496960 cell1783628032)
                  (ThetaLowerSegment.join cell1783759104 cell1783890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1784021248 cell1784152320)
                  (ThetaLowerSegment.join cell1784283392 cell1784414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1784545536 cell1784676608)
                  (ThetaLowerSegment.join cell1784807680 cell1784938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1785069824 cell1785200896)
                  (ThetaLowerSegment.join cell1785331968 cell1785463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1785594112 cell1785725184)
                  (ThetaLowerSegment.join cell1785856256 cell1785987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1786118400 cell1786249472)
                  (ThetaLowerSegment.join cell1786380544 cell1786511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1786642688 cell1786773760)
                  (ThetaLowerSegment.join cell1786904832 cell1787035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1787166976 cell1787298048)
                  (ThetaLowerSegment.join cell1787429120 cell1787560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1787691264 cell1787822336)
                  (ThetaLowerSegment.join cell1787953408 cell1788084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1788215552 cell1788346624)
                  (ThetaLowerSegment.join cell1788477696 cell1788608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1788739840 cell1788870912)
                  (ThetaLowerSegment.join cell1789001984 cell1789133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1789264128 cell1789395200)
                  (ThetaLowerSegment.join cell1789526272 cell1789657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1789788416 cell1789919488)
                  (ThetaLowerSegment.join cell1790050560 cell1790181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1790312704 cell1790443776)
                  (ThetaLowerSegment.join cell1790574848 cell1790705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1790836992 cell1790968064)
                  (ThetaLowerSegment.join cell1791099136 cell1791230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1791361280 cell1791492352)
                  (ThetaLowerSegment.join cell1791623424 cell1791754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1791885568 cell1792016640)
                  (ThetaLowerSegment.join cell1792147712 cell1792278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1792409856 cell1792540928)
                  (ThetaLowerSegment.join cell1792672000 cell1792803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1792934144 cell1793065216)
                  (ThetaLowerSegment.join cell1793196288 cell1793327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1793458432 cell1793589504)
                  (ThetaLowerSegment.join cell1793720576 cell1793851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1793982720 cell1794113792)
                  (ThetaLowerSegment.join cell1794244864 cell1794375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1794507008 cell1794638080)
                  (ThetaLowerSegment.join cell1794769152 cell1794900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1795031296 cell1795162368)
                  (ThetaLowerSegment.join cell1795293440 cell1795424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1795555584 cell1795686656)
                  (ThetaLowerSegment.join cell1795817728 cell1795948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1796079872 cell1796210944)
                  (ThetaLowerSegment.join cell1796342016 cell1796473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1796604160 cell1796735232)
                  (ThetaLowerSegment.join cell1796866304 cell1796997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1797128448 cell1797259520)
                  (ThetaLowerSegment.join cell1797390592 cell1797521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1797652736 cell1797783808)
                  (ThetaLowerSegment.join cell1797914880 cell1798045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1798177024 cell1798308096)
                  (ThetaLowerSegment.join cell1798439168 cell1798570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1798701312 cell1798832384)
                  (ThetaLowerSegment.join cell1798963456 cell1799094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1799225600 cell1799356672)
                  (ThetaLowerSegment.join cell1799487744 cell1799618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1799749888 cell1799880960)
                  (ThetaLowerSegment.join cell1800012032 cell1800143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1800274176 cell1800405248)
                  (ThetaLowerSegment.join cell1800536320 cell1800667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1800798464 cell1800929536)
                (ThetaLowerSegment.join cell1801060608 cell1801191680))
              (ThetaLowerSegment.join cell1801322752 cell1801339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
