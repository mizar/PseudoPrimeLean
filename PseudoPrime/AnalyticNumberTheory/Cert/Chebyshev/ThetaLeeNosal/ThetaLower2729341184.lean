/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2729341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2697341184 :
    ThetaLowerSegment 2697341184 2697472256 (134864620473499 / 50000)
      (134871162273899 / 50000) := by
  exact
    packedTile65536 2697341184 2697472256 14 6025 51935 31 _ _ (67861 / 3125) (434311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697472256 :
    ThetaLowerSegment 2697472256 2697603328 (134871162273899 / 50000)
      (269755512413459 / 100000) := by
  exact
    packedTile65536 2697472256 2697603328 14 6073 51937 31 _ _ (2171557 / 100000) (54289 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697603328 :
    ThetaLowerSegment 2697603328 2697734400 (269755512413459 / 100000) (1348842502599 / 500) := by
  exact
    packedTile65536 2697603328 2697734400 14 5981 51938 31 _ _ (2171561 / 100000) (542891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697734400 :
    ThetaLowerSegment 2697734400 2697865472 (1348842502599 / 500) (33722721641399 / 12500) := by
  exact
    packedTile65536 2697734400 2697865472 14 6112 51939 31 _ _ (1085783 / 50000) (2171569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697865472 :
    ThetaLowerSegment 2697865472 2697996544 (33722721641399 / 12500) (33724350319649 / 12500) := by
  exact
    packedTile65536 2697865472 2697996544 14 6000 51940 31 _ _ (2171571 / 100000) (1085787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2697996544 :
    ThetaLowerSegment 2697996544 2698127616 (33724350319649 / 12500) (1349039246929 / 500) := by
  exact
    packedTile65536 2697996544 2698127616 14 6008 51942 31 _ _ (271447 / 12500) (2171579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698127616 :
    ThetaLowerSegment 2698127616 2698258688 (1349039246929 / 500) (33727622888461 / 12500) := by
  exact
    packedTile65536 2698127616 2698258688 14 6048 51943 31 _ _ (2171581 / 100000) (67862 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698258688 :
    ThetaLowerSegment 2698258688 2698389760 (33727622888461 / 12500) (134917124663281 / 50000) := by
  exact
    packedTile65536 2698258688 2698389760 14 6109 51944 31 _ _ (1085793 / 50000) (2171589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698389760 :
    ThetaLowerSegment 2698389760 2698520832 (134917124663281 / 50000)
      (134923639436281 / 50000) := by
  exact
    packedTile65536 2698389760 2698520832 14 6000 51946 31 _ _ (2171591 / 100000) (1085797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698520832 :
    ThetaLowerSegment 2698520832 2698651904 (134923639436281 / 50000)
      (269860423537097 / 100000) := by
  exact
    packedTile65536 2698520832 2698651904 14 6053 51947 31 _ _ (434319 / 20000) (1085799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698651904 :
    ThetaLowerSegment 2698651904 2698782976 (269860423537097 / 100000)
      (269873461823497 / 100000) := by
  exact
    packedTile65536 2698651904 2698782976 14 6004 51948 31 _ _ (5429 / 250) (2171603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698782976 :
    ThetaLowerSegment 2698782976 2698914048 (269873461823497 / 100000)
      (134943290244651 / 50000) := by
  exact
    packedTile65536 2698782976 2698914048 14 6041 51949 31 _ _ (434321 / 20000) (271451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2698914048 :
    ThetaLowerSegment 2698914048 2699045120 (134943290244651 / 50000)
      (134949835477191 / 50000) := by
  exact
    packedTile65536 2698914048 2699045120 14 6028 51951 31 _ _ (217161 / 10000) (2171613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699045120 :
    ThetaLowerSegment 2699045120 2699176192 (134949835477191 / 50000)
      (134956376381571 / 50000) := by
  exact
    packedTile65536 2699045120 2699176192 14 6024 51952 31 _ _ (434323 / 20000) (1085809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699176192 :
    ThetaLowerSegment 2699176192 2699307264 (134956376381571 / 50000)
      (134962977020561 / 50000) := by
  exact
    packedTile65536 2699176192 2699307264 14 6079 51953 31 _ _ (108581 / 5000) (2171623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699307264 :
    ThetaLowerSegment 2699307264 2699438336 (134962977020561 / 50000)
      (269939098887247 / 100000) := by
  exact
    packedTile65536 2699307264 2699438336 14 6053 51954 31 _ _ (17373 / 800) (542907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699438336 :
    ThetaLowerSegment 2699438336 2699569408 (269939098887247 / 100000)
      (269952059169119 / 100000) := by
  exact
    packedTile65536 2699438336 2699569408 14 5968 51956 31 _ _ (2171629 / 100000) (135727 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699569408 :
    ThetaLowerSegment 2699569408 2699700480 (269952059169119 / 100000)
      (269965041197171 / 100000) := by
  exact
    packedTile65536 2699569408 2699700480 14 5978 51957 31 _ _ (1085817 / 50000) (2171637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699700480 :
    ThetaLowerSegment 2699700480 2699831552 (269965041197171 / 100000)
      (134989084377463 / 50000) := by
  exact
    packedTile65536 2699700480 2699831552 14 6045 51958 31 _ _ (2171639 / 100000) (1085821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699831552 :
    ThetaLowerSegment 2699831552 2699962624 (134989084377463 / 50000)
      (134995630798301 / 50000) := by
  exact
    packedTile65536 2699831552 2699962624 14 6029 51959 31 _ _ (542911 / 25000) (2171647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2699962624 :
    ThetaLowerSegment 2699962624 2700093696 (134995630798301 / 50000) (54000887398217 / 20000) := by
  exact
    packedTile65536 2699962624 2700093696 14 6067 51961 31 _ _ (2171649 / 100000) (542913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700093696 :
    ThetaLowerSegment 2700093696 2700224768 (54000887398217 / 20000)
      (270017529893051 / 100000) := by
  exact
    packedTile65536 2700093696 2700224768 14 6029 51962 31 _ _ (1085827 / 50000) (2171657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700224768 :
    ThetaLowerSegment 2700224768 2700355840 (270017529893051 / 100000)
      (270030829132767 / 100000) := by
  exact
    packedTile65536 2700224768 2700355840 14 6124 51963 31 _ _ (2171659 / 100000) (1085831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700355840 :
    ThetaLowerSegment 2700355840 2700486912 (270030829132767 / 100000)
      (135021913267911 / 50000) := by
  exact
    packedTile65536 2700355840 2700486912 14 5985 51964 31 _ _ (2171663 / 100000) (1085833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700486912 :
    ThetaLowerSegment 2700486912 2700617984 (135021913267911 / 50000)
      (135028426100243 / 50000) := by
  exact
    packedTile65536 2700486912 2700617984 14 5998 51966 31 _ _ (542917 / 25000) (2171671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700617984 :
    ThetaLowerSegment 2700617984 2700749056 (135028426100243 / 50000)
      (270069984307117 / 100000) := by
  exact
    packedTile65536 2700617984 2700749056 14 6047 51967 31 _ _ (2171673 / 100000) (542919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700749056 :
    ThetaLowerSegment 2700749056 2700880128 (270069984307117 / 100000)
      (270083118615661 / 100000) := by
  exact
    packedTile65536 2700749056 2700880128 14 6048 51968 31 _ _ (1085839 / 50000) (2171681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2700880128 :
    ThetaLowerSegment 2700880128 2701011200 (270083118615661 / 100000) (10803855330217 / 4000) := by
  exact
    packedTile65536 2700880128 2701011200 14 6108 51969 31 _ _ (2171683 / 100000) (1085843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701011200 :
    ThetaLowerSegment 2701011200 2701142272 (10803855330217 / 4000) (270109426413553 / 100000) := by
  exact
    packedTile65536 2701011200 2701142272 14 6006 51971 31 _ _ (271461 / 12500) (2171691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701142272 :
    ThetaLowerSegment 2701142272 2701273344 (270109426413553 / 100000)
      (67530661377211 / 25000) := by
  exact
    packedTile65536 2701142272 2701273344 14 6087 51972 31 _ _ (2171693 / 100000) (135731 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701273344 :
    ThetaLowerSegment 2701273344 2701404416 (67530661377211 / 25000) (54027140784581 / 20000) := by
  exact
    packedTile65536 2701273344 2701404416 14 6013 51973 31 _ _ (2171697 / 100000) (21717 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701404416 :
    ThetaLowerSegment 2701404416 2701535488 (54027140784581 / 20000)
      (270148836204899 / 100000) := by
  exact
    packedTile65536 2701404416 2701535488 14 6047 51975 31 _ _ (1085851 / 50000) (434341 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701535488 :
    ThetaLowerSegment 2701535488 2701666560 (270148836204899 / 100000)
      (270162061900529 / 100000) := by
  exact
    packedTile65536 2701535488 2701666560 14 6090 51976 31 _ _ (2171707 / 100000) (217171 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701666560 :
    ThetaLowerSegment 2701666560 2701797632 (270162061900529 / 100000)
      (270175118233073 / 100000) := by
  exact
    packedTile65536 2701666560 2701797632 14 6012 51977 31 _ _ (67866 / 3125) (434343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701797632 :
    ThetaLowerSegment 2701797632 2701928704 (270175118233073 / 100000) (13509406449481 / 5000) := by
  exact
    packedTile65536 2701797632 2701928704 14 5991 51978 31 _ _ (2171717 / 100000) (54293 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2701928704 :
    ThetaLowerSegment 2701928704 2702059776 (13509406449481 / 5000) (27020101815969 / 10000) := by
  exact
    packedTile65536 2701928704 2702059776 14 5935 51980 31 _ _ (1085861 / 50000) (86869 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702059776 :
    ThetaLowerSegment 2702059776 2702190848 (27020101815969 / 10000) (135107163251373 / 50000) := by
  exact
    packedTile65536 2702059776 2702190848 14 6128 51981 31 _ _ (2171727 / 100000) (217173 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702190848 :
    ThetaLowerSegment 2702190848 2702321920 (135107163251373 / 50000)
      (270227450273179 / 100000) := by
  exact
    packedTile65536 2702190848 2702321920 14 6043 51982 31 _ _ (2171731 / 100000) (1085867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702321920 :
    ThetaLowerSegment 2702321920 2702452992 (270227450273179 / 100000)
      (270240487204387 / 100000) := by
  exact
    packedTile65536 2702321920 2702452992 14 6003 51983 31 _ _ (271467 / 12500) (2171739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702452992 :
    ThetaLowerSegment 2702452992 2702584064 (270240487204387 / 100000)
      (135126857639409 / 50000) := by
  exact
    packedTile65536 2702452992 2702584064 14 6091 51985 31 _ _ (2171741 / 100000) (67867 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702584064 :
    ThetaLowerSegment 2702584064 2702715136 (135126857639409 / 50000)
      (135133442373281 / 50000) := by
  exact
    packedTile65536 2702584064 2702715136 14 6064 51986 31 _ _ (1085873 / 50000) (2171749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702715136 :
    ThetaLowerSegment 2702715136 2702846208 (135133442373281 / 50000)
      (270279887019799 / 100000) := by
  exact
    packedTile65536 2702715136 2702846208 14 5987 51987 31 _ _ (2171751 / 100000) (1085877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702846208 :
    ThetaLowerSegment 2702846208 2702977280 (270279887019799 / 100000)
      (270292978364967 / 100000) := by
  exact
    packedTile65536 2702846208 2702977280 14 6028 51988 31 _ _ (542939 / 25000) (2171759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2702977280 :
    ThetaLowerSegment 2702977280 2703108352 (270292978364967 / 100000)
      (270306152261127 / 100000) := by
  exact
    packedTile65536 2702977280 2703108352 14 6066 51990 31 _ _ (27147 / 1250) (2171763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703108352 :
    ThetaLowerSegment 2703108352 2703239424 (270306152261127 / 100000)
      (135159585996151 / 50000) := by
  exact
    packedTile65536 2703108352 2703239424 14 5995 51991 31 _ _ (434353 / 20000) (271471 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703239424 :
    ThetaLowerSegment 2703239424 2703370496 (135159585996151 / 50000) (33791532113319 / 12500) := by
  exact
    packedTile65536 2703239424 2703370496 14 6025 51992 31 _ _ (217177 / 10000) (2171773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703370496 :
    ThetaLowerSegment 2703370496 2703501568 (33791532113319 / 12500) (135172724133951 / 50000) := by
  exact
    packedTile65536 2703370496 2703501568 14 6074 51993 31 _ _ (86871 / 4000) (1085889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703501568 :
    ThetaLowerSegment 2703501568 2703632640 (135172724133951 / 50000)
      (135179336118161 / 50000) := by
  exact
    packedTile65536 2703501568 2703632640 14 6089 51995 31 _ _ (108589 / 5000) (2171783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703632640 :
    ThetaLowerSegment 2703632640 2703763712 (135179336118161 / 50000) (67592926822473 / 25000) := by
  exact
    packedTile65536 2703632640 2703763712 14 6002 51996 31 _ _ (434357 / 20000) (542947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703763712 :
    ThetaLowerSegment 2703763712 2703894784 (67592926822473 / 25000) (135192374444421 / 50000) := by
  exact
    packedTile65536 2703763712 2703894784 14 6005 51997 31 _ _ (217179 / 10000) (2171793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2703894784 :
    ThetaLowerSegment 2703894784 2704025856 (135192374444421 / 50000)
      (135198874623863 / 50000) := by
  exact
    packedTile65536 2703894784 2704025856 14 5986 51998 31 _ _ (1085897 / 50000) (2171797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704025856 :
    ThetaLowerSegment 2704025856 2704156928 (135198874623863 / 50000)
      (270410708372359 / 100000) := by
  exact
    packedTile65536 2704025856 2704156928 14 5967 52000 31 _ _ (2171799 / 100000) (1085901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704156928 :
    ThetaLowerSegment 2704156928 2704288000 (270410708372359 / 100000)
      (270423732680947 / 100000) := by
  exact
    packedTile65536 2704156928 2704288000 14 5997 52001 31 _ _ (542951 / 25000) (2171807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704288000 :
    ThetaLowerSegment 2704288000 2704419072 (270423732680947 / 100000)
      (27043682217379 / 10000) := by
  exact
    packedTile65536 2704288000 2704419072 14 6027 52002 31 _ _ (2171809 / 100000) (542953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704419072 :
    ThetaLowerSegment 2704419072 2704550144 (27043682217379 / 10000) (135225022088711 / 50000) := by
  exact
    packedTile65536 2704419072 2704550144 14 6088 52004 31 _ _ (1085907 / 50000) (2171817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704550144 :
    ThetaLowerSegment 2704550144 2704681216 (135225022088711 / 50000)
      (270463016452309 / 100000) := by
  exact
    packedTile65536 2704550144 2704681216 14 5973 52005 31 _ _ (2171819 / 100000) (1085911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704681216 :
    ThetaLowerSegment 2704681216 2704812288 (270463016452309 / 100000)
      (270476147294167 / 100000) := by
  exact
    packedTile65536 2704681216 2704812288 14 6046 52006 31 _ _ (2171823 / 100000) (1085913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704812288 :
    ThetaLowerSegment 2704812288 2704943360 (270476147294167 / 100000)
      (270489273822599 / 100000) := by
  exact
    packedTile65536 2704812288 2704943360 14 6044 52007 31 _ _ (542957 / 25000) (2171831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2704943360 :
    ThetaLowerSegment 2704943360 2705074432 (270489273822599 / 100000)
      (270502426443247 / 100000) := by
  exact
    packedTile65536 2704943360 2705074432 14 6056 52009 31 _ _ (2171833 / 100000) (542959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705074432 :
    ThetaLowerSegment 2705074432 2705205504 (270502426443247 / 100000)
      (54103131021701 / 20000) := by
  exact
    packedTile65536 2705074432 2705205504 14 6091 52010 31 _ _ (1085919 / 50000) (2171841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705205504 :
    ThetaLowerSegment 2705205504 2705336576 (54103131021701 / 20000) (135264320278901 / 50000) := by
  exact
    packedTile65536 2705205504 2705336576 14 5979 52011 31 _ _ (2171843 / 100000) (1085923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705336576 :
    ThetaLowerSegment 2705336576 2705467648 (135264320278901 / 50000)
      (135270931384213 / 50000) := by
  exact
    packedTile65536 2705336576 2705467648 14 6088 52012 31 _ _ (271481 / 12500) (2171851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705467648 :
    ThetaLowerSegment 2705467648 2705598720 (135270931384213 / 50000)
      (270555069806519 / 100000) := by
  exact
    packedTile65536 2705467648 2705598720 14 6081 52014 31 _ _ (2171853 / 100000) (135741 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705598720 :
    ThetaLowerSegment 2705598720 2705729792 (270555069806519 / 100000)
      (54113636695817 / 20000) := by
  exact
    packedTile65536 2705598720 2705729792 14 6038 52015 31 _ _ (2171857 / 100000) (108593 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705729792 :
    ThetaLowerSegment 2705729792 2705860864 (54113636695817 / 20000)
      (270581169041983 / 100000) := by
  exact
    packedTile65536 2705729792 2705860864 14 5979 52016 31 _ _ (1085931 / 50000) (434373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705860864 :
    ThetaLowerSegment 2705860864 2705991936 (270581169041983 / 100000)
      (135297162020201 / 50000) := by
  exact
    packedTile65536 2705860864 2705991936 14 6057 52017 31 _ _ (2171867 / 100000) (217187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2705991936 :
    ThetaLowerSegment 2705991936 2706123008 (135297162020201 / 50000) (27060735310053 / 10000) := by
  exact
    packedTile65536 2705991936 2706123008 14 5999 52019 31 _ _ (67871 / 3125) (695 / 32) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706123008 :
    ThetaLowerSegment 2706123008 2706254080 (27060735310053 / 10000)
      (270620586347091 / 100000) := by
  exact
    packedTile65536 2706123008 2706254080 14 6093 52020 31 _ _ (2171877 / 100000) (54297 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706254080 :
    ThetaLowerSegment 2706254080 2706385152 (270620586347091 / 100000)
      (270633658904849 / 100000) := by
  exact
    packedTile65536 2706254080 2706385152 14 6019 52021 31 _ _ (1085941 / 50000) (434377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706385152 :
    ThetaLowerSegment 2706385152 2706516224 (270633658904849 / 100000)
      (270646842252869 / 100000) := by
  exact
    packedTile65536 2706385152 2706516224 14 6070 52022 31 _ _ (1085943 / 50000) (2171889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706516224 :
    ThetaLowerSegment 2706516224 2706647296 (270646842252869 / 100000)
      (135329996526437 / 50000) := by
  exact
    packedTile65536 2706516224 2706647296 14 6055 52024 31 _ _ (2171891 / 100000) (1085947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706647296 :
    ThetaLowerSegment 2706647296 2706778368 (135329996526437 / 50000)
      (135336498097113 / 50000) := by
  exact
    packedTile65536 2706647296 2706778368 14 5987 52025 31 _ _ (271487 / 12500) (2171899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706778368 :
    ThetaLowerSegment 2706778368 2706909440 (135336498097113 / 50000) (33835765938459 / 12500) := by
  exact
    packedTile65536 2706778368 2706909440 14 6046 52026 31 _ _ (2171901 / 100000) (67872 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2706909440 :
    ThetaLowerSegment 2706909440 2707040512 (33835765938459 / 12500) (135349610964473 / 50000) := by
  exact
    packedTile65536 2706909440 2707040512 14 6029 52027 31 _ _ (1085953 / 50000) (2171909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707040512 :
    ThetaLowerSegment 2707040512 2707171584 (135349610964473 / 50000) (67678062262781 / 25000) := by
  exact
    packedTile65536 2707040512 2707171584 14 5998 52029 31 _ _ (2171911 / 100000) (1085957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707171584 :
    ThetaLowerSegment 2707171584 2707302656 (67678062262781 / 25000) (67681371176807 / 25000) := by
  exact
    packedTile65536 2707171584 2707302656 14 6094 52030 31 _ _ (542979 / 25000) (2171919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707302656 :
    ThetaLowerSegment 2707302656 2707433728 (67681371176807 / 25000) (67684652947927 / 25000) := by
  exact
    packedTile65536 2707302656 2707433728 14 6044 52031 31 _ _ (27149 / 1250) (2171923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707433728 :
    ThetaLowerSegment 2707433728 2707564800 (67684652947927 / 25000)
      (270751671576733 / 100000) := by
  exact
    packedTile65536 2707433728 2707564800 14 6013 52033 31 _ _ (86877 / 4000) (271491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707564800 :
    ThetaLowerSegment 2707564800 2707695872 (270751671576733 / 100000)
      (270764948584823 / 100000) := by
  exact
    packedTile65536 2707564800 2707695872 14 6113 52034 31 _ _ (217193 / 10000) (2171933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707695872 :
    ThetaLowerSegment 2707695872 2707826944 (270764948584823 / 100000)
      (270778067072223 / 100000) := by
  exact
    packedTile65536 2707695872 2707826944 14 6040 52035 31 _ _ (434387 / 20000) (1085969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707826944 :
    ThetaLowerSegment 2707826944 2707958016 (270778067072223 / 100000)
      (270790964051943 / 100000) := by
  exact
    packedTile65536 2707826944 2707958016 14 5938 52036 31 _ _ (108597 / 5000) (2171943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2707958016 :
    ThetaLowerSegment 2707958016 2708089088 (270790964051943 / 100000)
      (270804160789763 / 100000) := by
  exact
    packedTile65536 2707958016 2708089088 14 6076 52038 31 _ _ (434389 / 20000) (542987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708089088 :
    ThetaLowerSegment 2708089088 2708220160 (270804160789763 / 100000)
      (54163450659667 / 20000) := by
  exact
    packedTile65536 2708089088 2708220160 14 6028 52039 31 _ _ (2171949 / 100000) (135747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708220160 :
    ThetaLowerSegment 2708220160 2708351232 (54163450659667 / 20000)
      (270830439231069 / 100000) := by
  exact
    packedTile65536 2708220160 2708351232 14 6071 52040 31 _ _ (1085977 / 50000) (2171957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708351232 :
    ThetaLowerSegment 2708351232 2708482304 (270830439231069 / 100000)
      (67710924760191 / 25000) := by
  exact
    packedTile65536 2708351232 2708482304 14 6105 52041 31 _ _ (2171959 / 100000) (1085981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708482304 :
    ThetaLowerSegment 2708482304 2708613376 (67710924760191 / 25000) (33857092710573 / 12500) := by
  exact
    packedTile65536 2708482304 2708613376 14 6005 52043 31 _ _ (542991 / 25000) (2171967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708613376 :
    ThetaLowerSegment 2708613376 2708744448 (33857092710573 / 12500)
      (270869914676569 / 100000) := by
  exact
    packedTile65536 2708613376 2708744448 14 6065 52044 31 _ _ (2171969 / 100000) (542993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708744448 :
    ThetaLowerSegment 2708744448 2708875520 (270869914676569 / 100000)
      (270882926972803 / 100000) := by
  exact
    packedTile65536 2708744448 2708875520 14 5991 52045 31 _ _ (1085987 / 50000) (2171977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2708875520 :
    ThetaLowerSegment 2708875520 2709006592 (270882926972803 / 100000)
      (54179195677721 / 20000) := by
  exact
    packedTile65536 2708875520 2709006592 14 6009 52046 31 _ _ (1085989 / 50000) (2171981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709006592 :
    ThetaLowerSegment 2709006592 2709137664 (54179195677721 / 20000) (67727274834477 / 25000) := by
  exact
    packedTile65536 2709006592 2709137664 14 6041 52048 31 _ _ (2171983 / 100000) (1085993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709137664 :
    ThetaLowerSegment 2709137664 2709268736 (67727274834477 / 25000) (67730537160453 / 25000) := by
  exact
    packedTile65536 2709137664 2709268736 14 6008 52049 31 _ _ (542997 / 25000) (2171991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709268736 :
    ThetaLowerSegment 2709268736 2709399808 (67730537160453 / 25000)
      (270935048108239 / 100000) := by
  exact
    packedTile65536 2709268736 2709399808 14 5939 52050 31 _ _ (2171993 / 100000) (542999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709399808 :
    ThetaLowerSegment 2709399808 2709530880 (270935048108239 / 100000)
      (270948134396189 / 100000) := by
  exact
    packedTile65536 2709399808 2709530880 14 6025 52051 31 _ _ (1085999 / 50000) (2172001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709530880 :
    ThetaLowerSegment 2709530880 2709661952 (270948134396189 / 100000)
      (54192264559681 / 20000) := by
  exact
    packedTile65536 2709530880 2709661952 14 6072 52053 31 _ _ (2172003 / 100000) (1086003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709661952 :
    ThetaLowerSegment 2709661952 2709793024 (54192264559681 / 20000) (27097438742051 / 10000) := by
  exact
    packedTile65536 2709661952 2709793024 14 6015 52054 31 _ _ (2172007 / 100000) (217201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709793024 :
    ThetaLowerSegment 2709793024 2709924096 (27097438742051 / 10000) (135493777078627 / 50000) := by
  exact
    packedTile65536 2709793024 2709924096 14 6062 52055 31 _ _ (543003 / 25000) (434403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2709924096 :
    ThetaLowerSegment 2709924096 2710055168 (135493777078627 / 50000)
      (271000544990931 / 100000) := by
  exact
    packedTile65536 2709924096 2710055168 14 5981 52056 31 _ _ (2172017 / 100000) (108601 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710055168 :
    ThetaLowerSegment 2710055168 2710186240 (271000544990931 / 100000)
      (271013726992449 / 100000) := by
  exact
    packedTile65536 2710055168 2710186240 14 6069 52058 31 _ _ (1086011 / 50000) (86881 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710186240 :
    ThetaLowerSegment 2710186240 2710317312 (271013726992449 / 100000) (1693918507206 / 625) := by
  exact
    packedTile65536 2710186240 2710317312 14 6093 52059 31 _ _ (2172027 / 100000) (217203 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710317312 :
    ThetaLowerSegment 2710317312 2710448384 (1693918507206 / 625) (8470004950606 / 3125) := by
  exact
    packedTile65536 2710317312 2710448384 14 6076 52060 31 _ _ (67876 / 3125) (434407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710448384 :
    ThetaLowerSegment 2710448384 2710579456 (8470004950606 / 3125) (33881651544469 / 12500) := by
  exact
    packedTile65536 2710448384 2710579456 14 6010 52061 31 _ _ (543009 / 25000) (2172039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710579456 :
    ThetaLowerSegment 2710579456 2710710528 (33881651544469 / 12500) (1694164137363 / 625) := by
  exact
    packedTile65536 2710579456 2710710528 14 6008 52063 31 _ _ (2172041 / 100000) (543011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710710528 :
    ThetaLowerSegment 2710710528 2710841600 (1694164137363 / 625) (33884908523691 / 12500) := by
  exact
    packedTile65536 2710710528 2710841600 14 5988 52064 31 _ _ (1086023 / 50000) (2172049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710841600 :
    ThetaLowerSegment 2710841600 2710972672 (33884908523691 / 12500) (67773090328239 / 25000) := by
  exact
    packedTile65536 2710841600 2710972672 14 6028 52065 31 _ _ (2172051 / 100000) (1086027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2710972672 :
    ThetaLowerSegment 2710972672 2711103744 (67773090328239 / 25000) (67776335922917 / 25000) := by
  exact
    packedTile65536 2710972672 2711103744 14 5977 52067 31 _ _ (271507 / 12500) (2172059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711103744 :
    ThetaLowerSegment 2711103744 2711234816 (67776335922917 / 25000)
      (271118534618121 / 100000) := by
  exact
    packedTile65536 2711103744 2711234816 14 6073 52068 31 _ _ (2172061 / 100000) (67877 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711234816 :
    ThetaLowerSegment 2711234816 2711365888 (271118534618121 / 100000)
      (271131701682213 / 100000) := by
  exact
    packedTile65536 2711234816 2711365888 14 6062 52069 31 _ _ (1086033 / 50000) (2172069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711365888 :
    ThetaLowerSegment 2711365888 2711496960 (271131701682213 / 100000)
      (271144942620933 / 100000) := by
  exact
    packedTile65536 2711365888 2711496960 14 6096 52070 31 _ _ (217207 / 10000) (2172073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711496960 :
    ThetaLowerSegment 2711496960 2711628032 (271144942620933 / 100000)
      (271158218343333 / 100000) := by
  exact
    packedTile65536 2711496960 2711628032 14 6112 52072 31 _ _ (86883 / 4000) (1086039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711628032 :
    ThetaLowerSegment 2711628032 2711759104 (271158218343333 / 100000)
      (271171285576613 / 100000) := by
  exact
    packedTile65536 2711628032 2711759104 14 6016 52073 31 _ _ (27151 / 1250) (2172083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711759104 :
    ThetaLowerSegment 2711759104 2711890176 (271171285576613 / 100000)
      (67796059429867 / 25000) := by
  exact
    packedTile65536 2711759104 2711890176 14 5963 52074 31 _ _ (434417 / 20000) (271511 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2711890176 :
    ThetaLowerSegment 2711890176 2712021248 (67796059429867 / 25000) (135598770885359 / 50000) := by
  exact
    packedTile65536 2711890176 2712021248 14 6125 52075 31 _ _ (217209 / 10000) (2172093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712021248 :
    ThetaLowerSegment 2712021248 2712152320 (135598770885359 / 50000)
      (271210611266333 / 100000) := by
  exact
    packedTile65536 2712021248 2712152320 14 6017 52077 31 _ _ (434419 / 20000) (1086049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712152320 :
    ThetaLowerSegment 2712152320 2712283392 (271210611266333 / 100000)
      (135611838220909 / 50000) := by
  exact
    packedTile65536 2712152320 2712283392 14 6015 52078 31 _ _ (2172099 / 100000) (1086051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712283392 :
    ThetaLowerSegment 2712283392 2712414464 (135611838220909 / 50000)
      (135618435986809 / 50000) := by
  exact
    packedTile65536 2712283392 2712414464 14 6075 52079 31 _ _ (271513 / 12500) (2172107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712414464 :
    ThetaLowerSegment 2712414464 2712545536 (135618435986809 / 50000) (54249982228789 / 20000) := by
  exact
    packedTile65536 2712414464 2712545536 14 6003 52080 31 _ _ (2172109 / 100000) (135757 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712545536 :
    ThetaLowerSegment 2712545536 2712676608 (54249982228789 / 20000)
      (271262937311603 / 100000) := by
  exact
    packedTile65536 2712545536 2712676608 14 5997 52082 31 _ _ (1086057 / 50000) (2172117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712676608 :
    ThetaLowerSegment 2712676608 2712807680 (271262937311603 / 100000)
      (271276026500697 / 100000) := by
  exact
    packedTile65536 2712676608 2712807680 14 6026 52083 31 _ _ (2172119 / 100000) (1086061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712807680 :
    ThetaLowerSegment 2712807680 2712938752 (271276026500697 / 100000)
      (54257853552501 / 20000) := by
  exact
    packedTile65536 2712807680 2712938752 14 6096 52084 31 _ _ (2172123 / 100000) (1086063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2712938752 :
    ThetaLowerSegment 2712938752 2713069824 (54257853552501 / 20000)
      (271302304874761 / 100000) := by
  exact
    packedTile65536 2712938752 2713069824 14 6002 52085 31 _ _ (67879 / 3125) (2172131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713069824 :
    ThetaLowerSegment 2713069824 2713200896 (271302304874761 / 100000)
      (271315320295697 / 100000) := by
  exact
    packedTile65536 2713069824 2713200896 14 5992 52087 31 _ _ (2172133 / 100000) (271517 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713200896 :
    ThetaLowerSegment 2713200896 2713331968 (271315320295697 / 100000)
      (54265688436271 / 20000) := by
  exact
    packedTile65536 2713200896 2713331968 14 6041 52088 31 _ _ (1086069 / 50000) (2172141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713331968 :
    ThetaLowerSegment 2713331968 2713463040 (54265688436271 / 20000)
      (271341644466509 / 100000) := by
  exact
    packedTile65536 2713331968 2713463040 14 6078 52089 31 _ _ (2172143 / 100000) (1086073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713463040 :
    ThetaLowerSegment 2713463040 2713594112 (271341644466509 / 100000)
      (271354696903841 / 100000) := by
  exact
    packedTile65536 2713463040 2713594112 14 6009 52090 31 _ _ (543037 / 25000) (2172151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713594112 :
    ThetaLowerSegment 2713594112 2713725184 (271354696903841 / 100000)
      (271367779775337 / 100000) := by
  exact
    packedTile65536 2713594112 2713725184 14 6023 52092 31 _ _ (271519 / 12500) (434431 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713725184 :
    ThetaLowerSegment 2713725184 2713856256 (271367779775337 / 100000)
      (54276181658449 / 20000) := by
  exact
    packedTile65536 2713725184 2713856256 14 6044 52093 31 _ _ (2172157 / 100000) (13576 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713856256 :
    ThetaLowerSegment 2713856256 2713987328 (54276181658449 / 20000)
      (271394078110451 / 100000) := by
  exact
    packedTile65536 2713856256 2713987328 14 6063 52094 31 _ _ (1086081 / 50000) (434433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2713987328 :
    ThetaLowerSegment 2713987328 2714118400 (271394078110451 / 100000)
      (271407098079449 / 100000) := by
  exact
    packedTile65536 2713987328 2714118400 14 5994 52095 31 _ _ (2172167 / 100000) (217217 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714118400 :
    ThetaLowerSegment 2714118400 2714249472 (271407098079449 / 100000)
      (271420296196521 / 100000) := by
  exact
    packedTile65536 2714118400 2714249472 14 6076 52097 31 _ _ (543043 / 25000) (86887 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714249472 :
    ThetaLowerSegment 2714249472 2714380544 (271420296196521 / 100000)
      (135716717847597 / 50000) := by
  exact
    packedTile65536 2714249472 2714380544 14 6049 52098 31 _ _ (2172177 / 100000) (108609 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714380544 :
    ThetaLowerSegment 2714380544 2714511616 (135716717847597 / 50000)
      (271446696860199 / 100000) := by
  exact
    packedTile65536 2714380544 2714511616 14 6105 52099 31 _ _ (2172181 / 100000) (271523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714511616 :
    ThetaLowerSegment 2714511616 2714642688 (271446696860199 / 100000)
      (271459647433131 / 100000) := by
  exact
    packedTile65536 2714511616 2714642688 14 5962 52100 31 _ _ (1086093 / 50000) (2172189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714642688 :
    ThetaLowerSegment 2714642688 2714773760 (271459647433131 / 100000)
      (135736289243077 / 50000) := by
  exact
    packedTile65536 2714642688 2714773760 14 5953 52102 31 _ _ (2172191 / 100000) (1086097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714773760 :
    ThetaLowerSegment 2714773760 2714904832 (135736289243077 / 50000)
      (135742880771839 / 50000) := by
  exact
    packedTile65536 2714773760 2714904832 14 6069 52103 31 _ _ (543049 / 25000) (2172199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2714904832 :
    ThetaLowerSegment 2714904832 2715035904 (135742880771839 / 50000) (434398234949 / 160) := by
  exact
    packedTile65536 2714904832 2715035904 14 6047 52104 31 _ _ (2172201 / 100000) (543051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715035904 :
    ThetaLowerSegment 2715035904 2715166976 (434398234949 / 160) (271512119061047 / 100000) := by
  exact
    packedTile65536 2715035904 2715166976 14 6087 52106 31 _ _ (1086103 / 50000) (2172209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715166976 :
    ThetaLowerSegment 2715166976 2715298048 (271512119061047 / 100000)
      (271525098015797 / 100000) := by
  exact
    packedTile65536 2715166976 2715298048 14 5975 52107 31 _ _ (217221 / 10000) (2172213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715298048 :
    ThetaLowerSegment 2715298048 2715429120 (271525098015797 / 100000)
      (271538226883257 / 100000) := by
  exact
    packedTile65536 2715298048 2715429120 14 6044 52108 31 _ _ (434443 / 20000) (1086109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715429120 :
    ThetaLowerSegment 2715429120 2715560192 (271538226883257 / 100000)
      (271551336230957 / 100000) := by
  exact
    packedTile65536 2715429120 2715560192 14 6035 52109 31 _ _ (108611 / 5000) (2172223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715560192 :
    ThetaLowerSegment 2715560192 2715691264 (271551336230957 / 100000)
      (135782155465441 / 50000) := by
  exact
    packedTile65536 2715560192 2715691264 14 5973 52111 31 _ _ (86889 / 4000) (543057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715691264 :
    ThetaLowerSegment 2715691264 2715822336 (135782155465441 / 50000)
      (135788782939171 / 50000) := by
  exact
    packedTile65536 2715691264 2715822336 14 6102 52112 31 _ _ (217223 / 10000) (2172233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715822336 :
    ThetaLowerSegment 2715822336 2715953408 (135788782939171 / 50000)
      (135795269232881 / 50000) := by
  exact
    packedTile65536 2715822336 2715953408 14 5972 52113 31 _ _ (434447 / 20000) (1086119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2715953408 :
    ThetaLowerSegment 2715953408 2716084480 (135795269232881 / 50000)
      (271603617516781 / 100000) := by
  exact
    packedTile65536 2715953408 2716084480 14 6021 52114 31 _ _ (2172239 / 100000) (1086121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716084480 :
    ThetaLowerSegment 2716084480 2716215552 (271603617516781 / 100000)
      (271616774798689 / 100000) := by
  exact
    packedTile65536 2716084480 2716215552 14 6057 52116 31 _ _ (543061 / 25000) (2172247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716215552 :
    ThetaLowerSegment 2716215552 2716346624 (271616774798689 / 100000)
      (135814944332951 / 50000) := by
  exact
    packedTile65536 2716215552 2716346624 14 6037 52117 31 _ _ (2172249 / 100000) (543063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716346624 :
    ThetaLowerSegment 2716346624 2716477696 (135814944332951 / 50000)
      (135821445889173 / 50000) := by
  exact
    packedTile65536 2716346624 2716477696 14 5986 52118 31 _ _ (1086127 / 50000) (2172257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716477696 :
    ThetaLowerSegment 2716477696 2716608768 (135821445889173 / 50000) (16978502121581 / 6250) := by
  exact
    packedTile65536 2716477696 2716608768 14 6050 52119 31 _ _ (2172259 / 100000) (1086131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716608768 :
    ThetaLowerSegment 2716608768 2716739840 (16978502121581 / 6250) (8489657681458 / 3125) := by
  exact
    packedTile65536 2716608768 2716739840 14 5990 52121 31 _ _ (271533 / 12500) (2172267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716739840 :
    ThetaLowerSegment 2716739840 2716870912 (8489657681458 / 3125) (67920523655133 / 25000) := by
  exact
    packedTile65536 2716739840 2716870912 14 6007 52122 31 _ _ (543067 / 25000) (2172271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2716870912 :
    ThetaLowerSegment 2716870912 2717001984 (67920523655133 / 25000)
      (271695399792657 / 100000) := by
  exact
    packedTile65536 2716870912 2717001984 14 6125 52123 31 _ _ (2172273 / 100000) (543069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717001984 :
    ThetaLowerSegment 2717001984 2717133056 (271695399792657 / 100000)
      (271708552935947 / 100000) := by
  exact
    packedTile65536 2717001984 2717133056 14 6055 52124 31 _ _ (1086139 / 50000) (2172281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717133056 :
    ThetaLowerSegment 2717133056 2717264128 (271708552935947 / 100000)
      (135860811781379 / 50000) := by
  exact
    packedTile65536 2717133056 2717264128 14 6017 52126 31 _ _ (2172283 / 100000) (1086143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717264128 :
    ThetaLowerSegment 2717264128 2717395200 (135860811781379 / 50000)
      (135867382952579 / 50000) := by
  exact
    packedTile65536 2717264128 2717395200 14 6050 52127 31 _ _ (67884 / 3125) (2172291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717395200 :
    ThetaLowerSegment 2717395200 2717526272 (135867382952579 / 50000)
      (135873970428069 / 50000) := by
  exact
    packedTile65536 2717395200 2717526272 14 6065 52128 31 _ _ (543073 / 25000) (434459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717526272 :
    ThetaLowerSegment 2717526272 2717657344 (135873970428069 / 50000)
      (135880509042039 / 50000) := by
  exact
    packedTile65536 2717526272 2717657344 14 6020 52129 31 _ _ (2172297 / 100000) (21723 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717657344 :
    ThetaLowerSegment 2717657344 2717788416 (135880509042039 / 50000) (67943561307739 / 25000) := by
  exact
    packedTile65536 2717657344 2717788416 14 6089 52131 31 _ _ (1086151 / 50000) (434461 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717788416 :
    ThetaLowerSegment 2717788416 2717919488 (67943561307739 / 25000) (13589367429339 / 5000) := by
  exact
    packedTile65536 2717788416 2717919488 14 6032 52132 31 _ _ (2172307 / 100000) (217231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2717919488 :
    ThetaLowerSegment 2717919488 2718050560 (13589367429339 / 5000) (67950110820879 / 25000) := by
  exact
    packedTile65536 2717919488 2718050560 14 6028 52133 31 _ _ (271539 / 12500) (434463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718050560 :
    ThetaLowerSegment 2718050560 2718181632 (67950110820879 / 25000) (135906714697271 / 50000) := by
  exact
    packedTile65536 2718050560 2718181632 14 5978 52134 31 _ _ (2172317 / 100000) (13577 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718181632 :
    ThetaLowerSegment 2718181632 2718312704 (135906714697271 / 50000)
      (135913236004913 / 50000) := by
  exact
    packedTile65536 2718181632 2718312704 14 6004 52136 31 _ _ (2172321 / 100000) (543081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718312704 :
    ThetaLowerSegment 2718312704 2718443776 (135913236004913 / 50000) (8494987073184 / 3125) := by
  exact
    packedTile65536 2718312704 2718443776 14 6037 52137 31 _ _ (1086163 / 50000) (2172329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718443776 :
    ThetaLowerSegment 2718443776 2718574848 (8494987073184 / 3125) (271852783252713 / 100000) := by
  exact
    packedTile65536 2718443776 2718574848 14 6075 52138 31 _ _ (2172331 / 100000) (1086167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718574848 :
    ThetaLowerSegment 2718574848 2718705920 (271852783252713 / 100000)
      (271865762960313 / 100000) := by
  exact
    packedTile65536 2718574848 2718705920 14 5975 52139 31 _ _ (135771 / 6250) (2172339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718705920 :
    ThetaLowerSegment 2718705920 2718836992 (271865762960313 / 100000) (10875154660849 / 4000) := by
  exact
    packedTile65536 2718705920 2718836992 14 6032 52141 31 _ _ (2172341 / 100000) (271543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718836992 :
    ThetaLowerSegment 2718836992 2718968064 (10875154660849 / 4000) (271891894080187 / 100000) := by
  exact
    packedTile65536 2718836992 2718968064 14 5997 52142 31 _ _ (1086173 / 50000) (2172349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2718968064 :
    ThetaLowerSegment 2718968064 2719099136 (271891894080187 / 100000)
      (271905251860337 / 100000) := by
  exact
    packedTile65536 2718968064 2719099136 14 6149 52143 31 _ _ (43447 / 2000) (2172353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719099136 :
    ThetaLowerSegment 2719099136 2719230208 (271905251860337 / 100000)
      (271918368539827 / 100000) := by
  exact
    packedTile65536 2719099136 2719230208 14 6038 52144 31 _ _ (434471 / 20000) (1086179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719230208 :
    ThetaLowerSegment 2719230208 2719361280 (271918368539827 / 100000)
      (271931572143907 / 100000) := by
  exact
    packedTile65536 2719230208 2719361280 14 6078 52146 31 _ _ (54309 / 2500) (2172363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719361280 :
    ThetaLowerSegment 2719361280 2719492352 (271931572143907 / 100000)
      (135972380285911 / 50000) := by
  exact
    packedTile65536 2719361280 2719492352 14 6071 52147 31 _ _ (434473 / 20000) (135773 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719492352 :
    ThetaLowerSegment 2719492352 2719623424 (135972380285911 / 50000) (33994730051449 / 12500) := by
  exact
    packedTile65536 2719492352 2719623424 14 6021 52148 31 _ _ (217237 / 10000) (2172373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719623424 :
    ThetaLowerSegment 2719623424 2719754496 (33994730051449 / 12500) (33996348470079 / 12500) := by
  exact
    packedTile65536 2719623424 2719754496 14 5960 52150 31 _ _ (1086187 / 50000) (2172377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719754496 :
    ThetaLowerSegment 2719754496 2719885568 (33996348470079 / 12500)
      (271983954549751 / 100000) := by
  exact
    packedTile65536 2719754496 2719885568 14 6061 52151 31 _ _ (2172379 / 100000) (1086191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2719885568 :
    ThetaLowerSegment 2719885568 2720016640 (271983954549751 / 100000)
      (271997151782551 / 100000) := by
  exact
    packedTile65536 2719885568 2720016640 14 6075 52152 31 _ _ (67887 / 3125) (2172387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720016640 :
    ThetaLowerSegment 2720016640 2720147712 (271997151782551 / 100000)
      (34001294173813 / 12500) := by
  exact
    packedTile65536 2720016640 2720147712 14 6077 52153 31 _ _ (2172389 / 100000) (271549 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720147712 :
    ThetaLowerSegment 2720147712 2720278784 (34001294173813 / 12500) (68005817611307 / 25000) := by
  exact
    packedTile65536 2720147712 2720278784 14 5946 52155 31 _ _ (1086197 / 50000) (2172397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720278784 :
    ThetaLowerSegment 2720278784 2720409856 (68005817611307 / 25000) (136018137212821 / 50000) := by
  exact
    packedTile65536 2720278784 2720409856 14 5986 52156 31 _ _ (2172399 / 100000) (1086201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720409856 :
    ThetaLowerSegment 2720409856 2720540928 (136018137212821 / 50000)
      (136024667456239 / 50000) := by
  exact
    packedTile65536 2720409856 2720540928 14 6012 52157 31 _ _ (2172403 / 100000) (1086203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720540928 :
    ThetaLowerSegment 2720540928 2720672000 (136024667456239 / 50000)
      (136031225955991 / 50000) := by
  exact
    packedTile65536 2720540928 2720672000 14 6038 52158 31 _ _ (271551 / 12500) (2172411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720672000 :
    ThetaLowerSegment 2720672000 2720803072 (136031225955991 / 50000) (68018883545767 / 25000) := by
  exact
    packedTile65536 2720672000 2720803072 14 6022 52160 31 _ _ (2172413 / 100000) (67888 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720803072 :
    ThetaLowerSegment 2720803072 2720934144 (68018883545767 / 25000) (136044231121293 / 50000) := by
  exact
    packedTile65536 2720803072 2720934144 14 5951 52161 31 _ _ (1086209 / 50000) (2172421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2720934144 :
    ThetaLowerSegment 2720934144 2721065216 (136044231121293 / 50000) (54420322383801 / 20000) := by
  exact
    packedTile65536 2720934144 2721065216 14 6053 52162 31 _ _ (2172423 / 100000) (1086213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721065216 :
    ThetaLowerSegment 2721065216 2721196288 (54420322383801 / 20000)
      (272114729033231 / 100000) := by
  exact
    packedTile65536 2721065216 2721196288 14 6038 52163 31 _ _ (2172427 / 100000) (217243 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721196288 :
    ThetaLowerSegment 2721196288 2721327360 (272114729033231 / 100000)
      (272127759280367 / 100000) := by
  exact
    packedTile65536 2721196288 2721327360 14 5998 52165 31 _ _ (135777 / 6250) (434487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721327360 :
    ThetaLowerSegment 2721327360 2721458432 (272127759280367 / 100000)
      (272140828661359 / 100000) := by
  exact
    packedTile65536 2721327360 2721458432 14 6016 52166 31 _ _ (2172437 / 100000) (54311 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721458432 :
    ThetaLowerSegment 2721458432 2721589504 (272140828661359 / 100000) (10886156531181 / 4000) := by
  exact
    packedTile65536 2721458432 2721589504 14 6023 52167 31 _ _ (1086221 / 50000) (434489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721589504 :
    ThetaLowerSegment 2721589504 2721720576 (10886156531181 / 4000) (272167160861331 / 100000) := by
  exact
    packedTile65536 2721589504 2721720576 14 6098 52168 31 _ _ (2172447 / 100000) (43449 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721720576 :
    ThetaLowerSegment 2721720576 2721851648 (272167160861331 / 100000)
      (272180315058191 / 100000) := by
  exact
    packedTile65536 2721720576 2721851648 14 6055 52170 31 _ _ (543113 / 25000) (434491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721851648 :
    ThetaLowerSegment 2721851648 2721982720 (272180315058191 / 100000)
      (54438699938731 / 20000) := by
  exact
    packedTile65536 2721851648 2721982720 14 6069 52171 31 _ _ (271557 / 12500) (2172459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2721982720 :
    ThetaLowerSegment 2721982720 2722113792 (54438699938731 / 20000)
      (272206612668251 / 100000) := by
  exact
    packedTile65536 2721982720 2722113792 14 6036 52172 31 _ _ (2172461 / 100000) (135779 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722113792 :
    ThetaLowerSegment 2722113792 2722244864 (272206612668251 / 100000)
      (272219703948367 / 100000) := by
  exact
    packedTile65536 2722113792 2722244864 14 6026 52173 31 _ _ (1086233 / 50000) (2172469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722244864 :
    ThetaLowerSegment 2722244864 2722375936 (272219703948367 / 100000)
      (136116409577897 / 50000) := by
  exact
    packedTile65536 2722244864 2722375936 14 6037 52175 31 _ _ (2172471 / 100000) (1086237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722375936 :
    ThetaLowerSegment 2722375936 2722507008 (136116409577897 / 50000) (5444922772123 / 2000) := by
  exact
    packedTile65536 2722375936 2722507008 14 6131 52176 31 _ _ (543119 / 25000) (2172479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722507008 :
    ThetaLowerSegment 2722507008 2722638080 (5444922772123 / 2000) (27225911700167 / 10000) := by
  exact
    packedTile65536 2722507008 2722638080 14 5974 52177 31 _ _ (13578 / 625) (2172483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722638080 :
    ThetaLowerSegment 2722638080 2722769152 (27225911700167 / 10000) (54454450803693 / 20000) := by
  exact
    packedTile65536 2722638080 2722769152 14 6047 52178 31 _ _ (434497 / 20000) (271561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722769152 :
    ThetaLowerSegment 2722769152 2722900224 (54454450803693 / 20000) (2178281599091 / 800) := by
  exact
    packedTile65536 2722769152 2722900224 14 5959 52180 31 _ _ (217249 / 10000) (2172493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2722900224 :
    ThetaLowerSegment 2722900224 2723031296 (2178281599091 / 800) (27229822833889 / 10000) := by
  exact
    packedTile65536 2722900224 2723031296 14 5997 52181 31 _ _ (434499 / 20000) (1086249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723031296 :
    ThetaLowerSegment 2723031296 2723162368 (27229822833889 / 10000) (27231126551139 / 10000) := by
  exact
    packedTile65536 2723031296 2723162368 14 6001 52182 31 _ _ (869 / 40) (2172503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723162368 :
    ThetaLowerSegment 2723162368 2723293440 (27231126551139 / 10000) (136162136146419 / 50000) := by
  exact
    packedTile65536 2723162368 2723293440 14 5987 52183 31 _ _ (271563 / 12500) (2172507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723293440 :
    ThetaLowerSegment 2723293440 2723424512 (136162136146419 / 50000)
      (272337309519347 / 100000) := by
  exact
    packedTile65536 2723293440 2723424512 14 6001 52185 31 _ _ (2172509 / 100000) (67891 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723424512 :
    ThetaLowerSegment 2723424512 2723555584 (272337309519347 / 100000)
      (272350487989271 / 100000) := by
  exact
    packedTile65536 2723424512 2723555584 14 6066 52186 31 _ _ (1086257 / 50000) (2172517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723555584 :
    ThetaLowerSegment 2723555584 2723686656 (272350487989271 / 100000)
      (54472702882639 / 20000) := by
  exact
    packedTile65536 2723555584 2723686656 14 5996 52187 31 _ _ (2172519 / 100000) (1086261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723686656 :
    ThetaLowerSegment 2723686656 2723817728 (54472702882639 / 20000)
      (272376738566783 / 100000) := by
  exact
    packedTile65536 2723686656 2723817728 14 6087 52188 31 _ _ (543131 / 25000) (2172527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723817728 :
    ThetaLowerSegment 2723817728 2723948800 (272376738566783 / 100000)
      (68097415735451 / 25000) := by
  exact
    packedTile65536 2723817728 2723948800 14 5949 52190 31 _ _ (2172529 / 100000) (543133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2723948800 :
    ThetaLowerSegment 2723948800 2724079872 (68097415735451 / 25000) (68100635429357 / 25000) := by
  exact
    packedTile65536 2723948800 2724079872 14 5928 52191 31 _ _ (2172533 / 100000) (271567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724079872 :
    ThetaLowerSegment 2724079872 2724210944 (68100635429357 / 25000) (136207804766749 / 50000) := by
  exact
    packedTile65536 2724079872 2724210944 14 6015 52192 31 _ _ (1086269 / 50000) (2172541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724210944 :
    ThetaLowerSegment 2724210944 2724342016 (136207804766749 / 50000) (17026793829851 / 6250) := by
  exact
    packedTile65536 2724210944 2724342016 14 6026 52193 31 _ _ (2172543 / 100000) (1086273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724342016 :
    ThetaLowerSegment 2724342016 2724473088 (17026793829851 / 6250) (34055220872661 / 12500) := by
  exact
    packedTile65536 2724342016 2724473088 14 6014 52195 31 _ _ (543137 / 25000) (2172551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724473088 :
    ThetaLowerSegment 2724473088 2724604160 (34055220872661 / 12500) (54490990441089 / 20000) := by
  exact
    packedTile65536 2724473088 2724604160 14 6069 52196 31 _ _ (2172553 / 100000) (543139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724604160 :
    ThetaLowerSegment 2724604160 2724735232 (54490990441089 / 20000)
      (272468083139953 / 100000) := by
  exact
    packedTile65536 2724604160 2724735232 14 6044 52197 31 _ _ (2172557 / 100000) (27157 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724735232 :
    ThetaLowerSegment 2724735232 2724866304 (272468083139953 / 100000)
      (272481268418731 / 100000) := by
  exact
    packedTile65536 2724735232 2724866304 14 6069 52198 31 _ _ (1086281 / 50000) (434513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724866304 :
    ThetaLowerSegment 2724866304 2724997376 (272481268418731 / 100000)
      (68123636243917 / 25000) := by
  exact
    packedTile65536 2724866304 2724997376 14 6111 52200 31 _ _ (2172567 / 100000) (217257 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2724997376 :
    ThetaLowerSegment 2724997376 2725128448 (68123636243917 / 25000) (68126915741351 / 25000) := by
  exact
    packedTile65536 2724997376 2725128448 14 6038 52201 31 _ _ (543143 / 25000) (86903 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725128448 :
    ThetaLowerSegment 2725128448 2725259520 (68126915741351 / 25000)
      (272520843990063 / 100000) := by
  exact
    packedTile65536 2725128448 2725259520 14 6067 52202 31 _ _ (2172577 / 100000) (108629 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725259520 :
    ThetaLowerSegment 2725259520 2725390592 (272520843990063 / 100000)
      (272533996795437 / 100000) := by
  exact
    packedTile65536 2725259520 2725390592 14 6054 52204 31 _ _ (2172581 / 100000) (271573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725390592 :
    ThetaLowerSegment 2725390592 2725521664 (272533996795437 / 100000)
      (272546928027309 / 100000) := by
  exact
    packedTile65536 2725390592 2725521664 14 5952 52205 31 _ _ (1086293 / 50000) (2172589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725521664 :
    ThetaLowerSegment 2725521664 2725652736 (272546928027309 / 100000)
      (272560002679947 / 100000) := by
  exact
    packedTile65536 2725521664 2725652736 14 6018 52206 31 _ _ (2172591 / 100000) (1086297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725652736 :
    ThetaLowerSegment 2725652736 2725783808 (272560002679947 / 100000)
      (272573092570847 / 100000) := by
  exact
    packedTile65536 2725652736 2725783808 14 6025 52207 31 _ _ (543149 / 25000) (2172599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725783808 :
    ThetaLowerSegment 2725783808 2725914880 (272573092570847 / 100000) (8518322548073 / 3125) := by
  exact
    packedTile65536 2725783808 2725914880 14 6089 52209 31 _ _ (2172601 / 100000) (543151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2725914880 :
    ThetaLowerSegment 2725914880 2726045952 (8518322548073 / 3125) (136299763315763 / 50000) := by
  exact
    packedTile65536 2725914880 2726045952 14 6078 52210 31 _ _ (434521 / 20000) (67894 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726045952 :
    ThetaLowerSegment 2726045952 2726177024 (136299763315763 / 50000)
      (136306339806233 / 50000) := by
  exact
    packedTile65536 2726045952 2726177024 14 6054 52211 31 _ _ (217261 / 10000) (2172613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726177024 :
    ThetaLowerSegment 2726177024 2726308096 (136306339806233 / 50000) (8519561343143 / 3125) := by
  exact
    packedTile65536 2726177024 2726308096 14 6114 52212 31 _ _ (434523 / 20000) (1086309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726308096 :
    ThetaLowerSegment 2726308096 2726439168 (8519561343143 / 3125) (34079873208107 / 12500) := by
  exact
    packedTile65536 2726308096 2726439168 14 5994 52214 31 _ _ (108631 / 5000) (2172623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726439168 :
    ThetaLowerSegment 2726439168 2726570240 (34079873208107 / 12500) (136325999844303 / 50000) := by
  exact
    packedTile65536 2726439168 2726570240 14 5990 52215 31 _ _ (17381 / 800) (543157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726570240 :
    ThetaLowerSegment 2726570240 2726701312 (136325999844303 / 50000) (34083124816737 / 12500) := by
  exact
    packedTile65536 2726570240 2726701312 14 5983 52216 31 _ _ (217263 / 10000) (2172633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726701312 :
    ThetaLowerSegment 2726701312 2726832384 (34083124816737 / 12500) (68169535742399 / 25000) := by
  exact
    packedTile65536 2726701312 2726832384 14 6050 52217 31 _ _ (1086317 / 50000) (2172637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726832384 :
    ThetaLowerSegment 2726832384 2726963456 (68169535742399 / 25000)
      (272691124487621 / 100000) := by
  exact
    packedTile65536 2726832384 2726963456 14 5975 52219 31 _ _ (2172639 / 100000) (1086321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2726963456 :
    ThetaLowerSegment 2726963456 2727094528 (272691124487621 / 100000)
      (272704101690233 / 100000) := by
  exact
    packedTile65536 2726963456 2727094528 14 5973 52220 31 _ _ (543161 / 25000) (2172647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727094528 :
    ThetaLowerSegment 2727094528 2727225600 (272704101690233 / 100000)
      (272717194073107 / 100000) := by
  exact
    packedTile65536 2727094528 2727225600 14 6026 52221 31 _ _ (2172649 / 100000) (543163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727225600 :
    ThetaLowerSegment 2727225600 2727356672 (272717194073107 / 100000)
      (272730306039997 / 100000) := by
  exact
    packedTile65536 2727225600 2727356672 14 6035 52222 31 _ _ (1086327 / 50000) (2172657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727356672 :
    ThetaLowerSegment 2727356672 2727487744 (272730306039997 / 100000)
      (54548662314157 / 20000) := by
  exact
    packedTile65536 2727356672 2727487744 14 5986 52224 31 _ _ (1086329 / 50000) (2172661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727487744 :
    ThetaLowerSegment 2727487744 2727618816 (54548662314157 / 20000) (136378272630559 / 50000) := by
  exact
    packedTile65536 2727487744 2727618816 14 6091 52225 31 _ _ (2172663 / 100000) (1086333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727618816 :
    ThetaLowerSegment 2727618816 2727749888 (136378272630559 / 50000)
      (136384806929569 / 50000) := by
  exact
    packedTile65536 2727618816 2727749888 14 6015 52226 31 _ _ (543167 / 25000) (2172671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727749888 :
    ThetaLowerSegment 2727749888 2727880960 (136384806929569 / 50000) (27278261513437 / 10000) := by
  exact
    packedTile65536 2727749888 2727880960 14 5984 52227 31 _ _ (2172673 / 100000) (543169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2727880960 :
    ThetaLowerSegment 2727880960 2728012032 (27278261513437 / 10000) (136397747384777 / 50000) := by
  exact
    packedTile65536 2727880960 2728012032 14 5928 52229 31 _ _ (1086339 / 50000) (2172681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728012032 :
    ThetaLowerSegment 2728012032 2728143104 (136397747384777 / 50000) (13640425782639 / 5000) := by
  exact
    packedTile65536 2728012032 2728143104 14 5993 52230 31 _ _ (1086341 / 50000) (434537 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728143104 :
    ThetaLowerSegment 2728143104 2728274176 (13640425782639 / 5000) (272821419240873 / 100000) := by
  exact
    packedTile65536 2728143104 2728274176 14 5939 52231 31 _ _ (2172687 / 100000) (217269 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728274176 :
    ThetaLowerSegment 2728274176 2728405248 (272821419240873 / 100000)
      (54566895858497 / 20000) := by
  exact
    packedTile65536 2728274176 2728405248 14 6011 52232 31 _ _ (543173 / 25000) (434539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728405248 :
    ThetaLowerSegment 2728405248 2728536320 (54566895858497 / 20000) (6821191960669 / 2500) := by
  exact
    packedTile65536 2728405248 2728536320 14 6075 52234 31 _ _ (2172697 / 100000) (21727 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728536320 :
    ThetaLowerSegment 2728536320 2728667392 (6821191960669 / 2500) (136430486595149 / 50000) := by
  exact
    packedTile65536 2728536320 2728667392 14 6119 52235 31 _ _ (1086351 / 50000) (434541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728667392 :
    ThetaLowerSegment 2728667392 2728798464 (136430486595149 / 50000) (27287383995523 / 10000) := by
  exact
    packedTile65536 2728667392 2728798464 14 5922 52236 31 _ _ (1086353 / 50000) (2172709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728798464 :
    ThetaLowerSegment 2728798464 2728929536 (27287383995523 / 10000) (136443507637367 / 50000) := by
  exact
    packedTile65536 2728798464 2728929536 14 6064 52237 31 _ _ (2172711 / 100000) (1086357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2728929536 :
    ThetaLowerSegment 2728929536 2729060608 (136443507637367 / 50000)
      (136450107262217 / 50000) := by
  exact
    packedTile65536 2728929536 2729060608 14 6075 52239 31 _ _ (543179 / 25000) (2172719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729060608 :
    ThetaLowerSegment 2729060608 2729191680 (136450107262217 / 50000)
      (272913279095807 / 100000) := by
  exact
    packedTile65536 2729060608 2729191680 14 6013 52240 31 _ _ (2172721 / 100000) (543181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729191680 :
    ThetaLowerSegment 2729191680 2729322752 (272913279095807 / 100000)
      (54585233975833 / 20000) := by
  exact
    packedTile65536 2729191680 2729322752 14 5933 52241 31 _ _ (1086363 / 50000) (2172729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729322752 :
    ThetaLowerSegment 2729322752 2729339136 (54585233975833 / 20000) (54585572487167 / 20000) := by
  exact
    packedTile65536 2729322752 2729339136 11 779 52242 31 _ _ (217273 / 10000) (2172733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729339136 :
    ThetaLowerSegment 2729339136 2729341184 (54585572487167 / 20000) (1705800430283 / 625) := by
  exact
    packedTile65536 2729339136 2729341184 8 95 52243 31 _ _ (2172731 / 100000) (1086367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2697341184_2729341184 :
    ThetaLowerSegment 2697341184 2729341184 (134864620473499 / 50000) (1705800430283 / 625) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2697341184 cell2697472256)
                  (ThetaLowerSegment.join cell2697603328 cell2697734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2697865472 cell2697996544)
                  (ThetaLowerSegment.join cell2698127616 cell2698258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2698389760 cell2698520832)
                  (ThetaLowerSegment.join cell2698651904 cell2698782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2698914048 cell2699045120)
                  (ThetaLowerSegment.join cell2699176192 cell2699307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2699438336 cell2699569408)
                  (ThetaLowerSegment.join cell2699700480 cell2699831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2699962624 cell2700093696)
                  (ThetaLowerSegment.join cell2700224768 cell2700355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2700486912 cell2700617984)
                  (ThetaLowerSegment.join cell2700749056 cell2700880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2701011200 cell2701142272)
                  (ThetaLowerSegment.join cell2701273344 cell2701404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2701535488 cell2701666560)
                  (ThetaLowerSegment.join cell2701797632 cell2701928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2702059776 cell2702190848)
                  (ThetaLowerSegment.join cell2702321920 cell2702452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2702584064 cell2702715136)
                  (ThetaLowerSegment.join cell2702846208 cell2702977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2703108352 cell2703239424)
                  (ThetaLowerSegment.join cell2703370496 cell2703501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2703632640 cell2703763712)
                  (ThetaLowerSegment.join cell2703894784 cell2704025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2704156928 cell2704288000)
                  (ThetaLowerSegment.join cell2704419072 cell2704550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2704681216 cell2704812288)
                  (ThetaLowerSegment.join cell2704943360 cell2705074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2705205504 cell2705336576)
                  (ThetaLowerSegment.join cell2705467648 cell2705598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2705729792 cell2705860864)
                  (ThetaLowerSegment.join cell2705991936 cell2706123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2706254080 cell2706385152)
                  (ThetaLowerSegment.join cell2706516224 cell2706647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2706778368 cell2706909440)
                  (ThetaLowerSegment.join cell2707040512 cell2707171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2707302656 cell2707433728)
                  (ThetaLowerSegment.join cell2707564800 cell2707695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2707826944 cell2707958016)
                  (ThetaLowerSegment.join cell2708089088 cell2708220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2708351232 cell2708482304)
                  (ThetaLowerSegment.join cell2708613376 cell2708744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2708875520 cell2709006592)
                  (ThetaLowerSegment.join cell2709137664 cell2709268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2709399808 cell2709530880)
                  (ThetaLowerSegment.join cell2709661952 cell2709793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2709924096 cell2710055168)
                  (ThetaLowerSegment.join cell2710186240 cell2710317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2710448384 cell2710579456)
                  (ThetaLowerSegment.join cell2710710528 cell2710841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2710972672 cell2711103744)
                  (ThetaLowerSegment.join cell2711234816 cell2711365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2711496960 cell2711628032)
                  (ThetaLowerSegment.join cell2711759104 cell2711890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2712021248 cell2712152320)
                  (ThetaLowerSegment.join cell2712283392 cell2712414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2712545536 cell2712676608)
                  (ThetaLowerSegment.join cell2712807680 cell2712938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2713069824 cell2713200896)
                  (ThetaLowerSegment.join cell2713331968 cell2713463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2713594112 cell2713725184)
                  (ThetaLowerSegment.join cell2713856256 cell2713987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2714118400 cell2714249472)
                  (ThetaLowerSegment.join cell2714380544 cell2714511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2714642688 cell2714773760)
                  (ThetaLowerSegment.join cell2714904832 cell2715035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2715166976 cell2715298048)
                  (ThetaLowerSegment.join cell2715429120 cell2715560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2715691264 cell2715822336)
                  (ThetaLowerSegment.join cell2715953408 cell2716084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2716215552 cell2716346624)
                  (ThetaLowerSegment.join cell2716477696 cell2716608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2716739840 cell2716870912)
                  (ThetaLowerSegment.join cell2717001984 cell2717133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2717264128 cell2717395200)
                  (ThetaLowerSegment.join cell2717526272 cell2717657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2717788416 cell2717919488)
                  (ThetaLowerSegment.join cell2718050560 cell2718181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2718312704 cell2718443776)
                  (ThetaLowerSegment.join cell2718574848 cell2718705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2718836992 cell2718968064)
                  (ThetaLowerSegment.join cell2719099136 cell2719230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2719361280 cell2719492352)
                  (ThetaLowerSegment.join cell2719623424 cell2719754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2719885568 cell2720016640)
                  (ThetaLowerSegment.join cell2720147712 cell2720278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2720409856 cell2720540928)
                  (ThetaLowerSegment.join cell2720672000 cell2720803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2720934144 cell2721065216)
                  (ThetaLowerSegment.join cell2721196288 cell2721327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2721458432 cell2721589504)
                  (ThetaLowerSegment.join cell2721720576 cell2721851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2721982720 cell2722113792)
                  (ThetaLowerSegment.join cell2722244864 cell2722375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2722507008 cell2722638080)
                  (ThetaLowerSegment.join cell2722769152 cell2722900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2723031296 cell2723162368)
                  (ThetaLowerSegment.join cell2723293440 cell2723424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2723555584 cell2723686656)
                  (ThetaLowerSegment.join cell2723817728 cell2723948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2724079872 cell2724210944)
                  (ThetaLowerSegment.join cell2724342016 cell2724473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2724604160 cell2724735232)
                  (ThetaLowerSegment.join cell2724866304 cell2724997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2725128448 cell2725259520)
                  (ThetaLowerSegment.join cell2725390592 cell2725521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2725652736 cell2725783808)
                  (ThetaLowerSegment.join cell2725914880 cell2726045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2726177024 cell2726308096)
                  (ThetaLowerSegment.join cell2726439168 cell2726570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2726701312 cell2726832384)
                  (ThetaLowerSegment.join cell2726963456 cell2727094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2727225600 cell2727356672)
                  (ThetaLowerSegment.join cell2727487744 cell2727618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2727749888 cell2727880960)
                  (ThetaLowerSegment.join cell2728012032 cell2728143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2728274176 cell2728405248)
                  (ThetaLowerSegment.join cell2728536320 cell2728667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2728798464 cell2728929536)
                (ThetaLowerSegment.join cell2729060608 cell2729191680))
              (ThetaLowerSegment.join cell2729322752 cell2729339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
