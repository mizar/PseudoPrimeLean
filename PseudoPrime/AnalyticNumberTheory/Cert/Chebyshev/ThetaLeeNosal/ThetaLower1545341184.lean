/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1545341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1513341184 :
    ThetaLowerSegment 1513341184 1513472256 (151330029786991 / 100000)
      (151342995572429 / 100000) := by
  exact
    packedTile65536 1513341184 1513472256 14 6134 38901 30 _ _ (2113757 / 100000) (13211 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513472256 :
    ThetaLowerSegment 1513472256 1513603328 (151342995572429 / 100000)
      (151356022712287 / 100000) := by
  exact
    packedTile65536 1513472256 1513603328 14 6163 38903 30 _ _ (1056883 / 50000) (2113769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513603328 :
    ThetaLowerSegment 1513603328 1513734400 (151356022712287 / 100000)
      (151368923075009 / 100000) := by
  exact
    packedTile65536 1513603328 1513734400 14 6103 38905 30 _ _ (1056887 / 50000) (2113777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513734400 :
    ThetaLowerSegment 1513734400 1513865472 (151368923075009 / 100000)
      (151382087715533 / 100000) := by
  exact
    packedTile65536 1513734400 1513865472 14 6228 38906 30 _ _ (2113783 / 100000) (1056893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513865472 :
    ThetaLowerSegment 1513865472 1513996544 (151382087715533 / 100000)
      (30279058092073 / 20000) := by
  exact
    packedTile65536 1513865472 1513996544 14 6246 38908 30 _ _ (66056 / 3125) (422759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513996544 :
    ThetaLowerSegment 1513996544 1514127616 (30279058092073 / 20000) (30281672017153 / 20000) := by
  exact
    packedTile65536 1513996544 1514127616 14 6183 38910 30 _ _ (10569 / 500) (2113803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514127616 :
    ThetaLowerSegment 1514127616 1514258688 (30281672017153 / 20000)
      (151421461473947 / 100000) := by
  exact
    packedTile65536 1514127616 1514258688 14 6198 38911 30 _ _ (2113809 / 100000) (528453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514258688 :
    ThetaLowerSegment 1514258688 1514389760 (151421461473947 / 100000)
      (151434524869187 / 100000) := by
  exact
    packedTile65536 1514258688 1514389760 14 6180 38913 30 _ _ (1056909 / 50000) (2113821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514389760 :
    ThetaLowerSegment 1514389760 1514520832 (151434524869187 / 100000)
      (151447746850817 / 100000) := by
  exact
    packedTile65536 1514389760 1514520832 14 6255 38915 30 _ _ (1056913 / 50000) (2113829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514520832 :
    ThetaLowerSegment 1514520832 1514651904 (151447746850817 / 100000)
      (151460954091897 / 100000) := by
  exact
    packedTile65536 1514520832 1514651904 14 6248 38916 30 _ _ (422767 / 20000) (1056919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514651904 :
    ThetaLowerSegment 1514651904 1514782976 (151460954091897 / 100000)
      (151474207893777 / 100000) := by
  exact
    packedTile65536 1514651904 1514782976 14 6270 38918 30 _ _ (528461 / 25000) (2113847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514782976 :
    ThetaLowerSegment 1514782976 1514914048 (151474207893777 / 100000)
      (151487252474469 / 100000) := by
  exact
    packedTile65536 1514782976 1514914048 14 6171 38920 30 _ _ (528463 / 25000) (422771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1514914048 :
    ThetaLowerSegment 1514914048 1515045120 (151487252474469 / 100000)
      (151500333046337 / 100000) := by
  exact
    packedTile65536 1514914048 1515045120 14 6188 38921 30 _ _ (2113861 / 100000) (264233 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515045120 :
    ThetaLowerSegment 1515045120 1515176192 (151500333046337 / 100000)
      (151513466520647 / 100000) := by
  exact
    packedTile65536 1515045120 1515176192 14 6213 38923 30 _ _ (211387 / 10000) (2113873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515176192 :
    ThetaLowerSegment 1515176192 1515307264 (151513466520647 / 100000)
      (151526488009127 / 100000) := by
  exact
    packedTile65536 1515176192 1515307264 14 6160 38925 30 _ _ (1056939 / 50000) (2113881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515307264 :
    ThetaLowerSegment 1515307264 1515438336 (151526488009127 / 100000)
      (37884925479191 / 25000) := by
  exact
    packedTile65536 1515307264 1515438336 14 6251 38926 30 _ _ (2113887 / 100000) (211389 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515438336 :
    ThetaLowerSegment 1515438336 1515569408 (37884925479191 / 25000) (37888202017991 / 25000) := by
  exact
    packedTile65536 1515438336 1515569408 14 6200 38928 30 _ _ (264237 / 12500) (2113899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515569408 :
    ThetaLowerSegment 1515569408 1515700480 (37888202017991 / 25000) (37891485439379 / 25000) := by
  exact
    packedTile65536 1515569408 1515700480 14 6213 38930 30 _ _ (132119 / 6250) (2113907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515700480 :
    ThetaLowerSegment 1515700480 1515831552 (37891485439379 / 25000)
      (151578999398117 / 100000) := by
  exact
    packedTile65536 1515700480 1515831552 14 6177 38931 30 _ _ (2113913 / 100000) (528479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515831552 :
    ThetaLowerSegment 1515831552 1515962624 (151578999398117 / 100000)
      (151592046524701 / 100000) := by
  exact
    packedTile65536 1515831552 1515962624 14 6172 38933 30 _ _ (1056961 / 50000) (84557 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515962624 :
    ThetaLowerSegment 1515962624 1516093696 (151592046524701 / 100000)
      (151605224764321 / 100000) := by
  exact
    packedTile65536 1515962624 1516093696 14 6234 38935 30 _ _ (211393 / 10000) (2113933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516093696 :
    ThetaLowerSegment 1516093696 1516224768 (151605224764321 / 100000)
      (151618255084317 / 100000) := by
  exact
    packedTile65536 1516093696 1516224768 14 6164 38937 30 _ _ (2113939 / 100000) (1056971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516224768 :
    ThetaLowerSegment 1516224768 1516355840 (151618255084317 / 100000)
      (75815768506659 / 50000) := by
  exact
    packedTile65536 1516224768 1516355840 14 6283 38938 30 _ _ (2113947 / 100000) (42279 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516355840 :
    ThetaLowerSegment 1516355840 1516486912 (75815768506659 / 50000) (75822269978337 / 50000) := by
  exact
    packedTile65536 1516355840 1516486912 14 6151 38940 30 _ _ (528489 / 25000) (2113959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516486912 :
    ThetaLowerSegment 1516486912 1516617984 (75822269978337 / 50000)
      (151658008027689 / 100000) := by
  exact
    packedTile65536 1516486912 1516617984 14 6371 38942 30 _ _ (422793 / 20000) (132123 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516617984 :
    ThetaLowerSegment 1516617984 1516749056 (151658008027689 / 100000)
      (151671144255911 / 100000) := by
  exact
    packedTile65536 1516617984 1516749056 14 6214 38943 30 _ _ (2113973 / 100000) (264247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516749056 :
    ThetaLowerSegment 1516749056 1516880128 (151671144255911 / 100000)
      (30336834122599 / 20000) := by
  exact
    packedTile65536 1516749056 1516880128 14 6162 38945 30 _ _ (1056991 / 50000) (422797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1516880128 :
    ThetaLowerSegment 1516880128 1517011200 (30336834122599 / 20000) (948106331927 / 625) := by
  exact
    packedTile65536 1516880128 1517011200 14 6075 38947 30 _ _ (2113991 / 100000) (1056997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517011200 :
    ThetaLowerSegment 1517011200 1517142272 (948106331927 / 625) (151710244628061 / 100000) := by
  exact
    packedTile65536 1517011200 1517142272 14 6259 38948 30 _ _ (2113999 / 100000) (1057001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517142272 :
    ThetaLowerSegment 1517142272 1517273344 (151710244628061 / 100000)
      (151723235207221 / 100000) := by
  exact
    packedTile65536 1517142272 1517273344 14 6145 38950 30 _ _ (264251 / 12500) (2114011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517273344 :
    ThetaLowerSegment 1517273344 1517404416 (151723235207221 / 100000)
      (37934101911787 / 25000) := by
  exact
    packedTile65536 1517273344 1517404416 14 6231 38952 30 _ _ (2114017 / 100000) (105701 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517404416 :
    ThetaLowerSegment 1517404416 1517535488 (37934101911787 / 25000)
      (151749516716173 / 100000) := by
  exact
    packedTile65536 1517404416 1517535488 14 6201 38953 30 _ _ (84561 / 4000) (528507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517535488 :
    ThetaLowerSegment 1517535488 1517666560 (151749516716173 / 100000)
      (151762615270837 / 100000) := by
  exact
    packedTile65536 1517535488 1517666560 14 6196 38955 30 _ _ (1057017 / 50000) (2114037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517666560 :
    ThetaLowerSegment 1517666560 1517797632 (151762615270837 / 100000)
      (151775694848691 / 100000) := by
  exact
    packedTile65536 1517666560 1517797632 14 6187 38957 30 _ _ (1057021 / 50000) (422809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517797632 :
    ThetaLowerSegment 1517797632 1517928704 (151775694848691 / 100000)
      (18973587297049 / 12500) := by
  exact
    packedTile65536 1517797632 1517928704 14 6151 38958 30 _ _ (2114051 / 100000) (1057027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1517928704 :
    ThetaLowerSegment 1517928704 1518059776 (18973587297049 / 12500) (37950425489863 / 25000) := by
  exact
    packedTile65536 1517928704 1518059776 14 6151 38960 30 _ _ (105703 / 5000) (2114063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518059776 :
    ThetaLowerSegment 1518059776 1518190848 (37950425489863 / 25000) (948842306336 / 625) := by
  exact
    packedTile65536 1518059776 1518190848 14 6181 38962 30 _ _ (528517 / 25000) (2114071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518190848 :
    ThetaLowerSegment 1518190848 1518321920 (948842306336 / 625) (75913982541197 / 50000) := by
  exact
    packedTile65536 1518190848 1518321920 14 6242 38963 30 _ _ (2114077 / 100000) (13213 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518321920 :
    ThetaLowerSegment 1518321920 1518452992 (75913982541197 / 50000) (75920555234571 / 50000) := by
  exact
    packedTile65536 1518321920 1518452992 14 6218 38965 30 _ _ (1057043 / 50000) (2114089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518452992 :
    ThetaLowerSegment 1518452992 1518584064 (75920555234571 / 50000) (75927098355501 / 50000) := by
  exact
    packedTile65536 1518452992 1518584064 14 6190 38967 30 _ _ (1057047 / 50000) (2114097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518584064 :
    ThetaLowerSegment 1518584064 1518715136 (75927098355501 / 50000) (30373482393771 / 20000) := by
  exact
    packedTile65536 1518584064 1518715136 14 6251 38969 31 _ _ (2114103 / 100000) (1057053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518715136 :
    ThetaLowerSegment 1518715136 1518846208 (30373482393771 / 20000)
      (151880697048663 / 100000) := by
  exact
    packedTile65536 1518715136 1518846208 14 6284 38970 31 _ _ (66066 / 3125) (422823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518846208 :
    ThetaLowerSegment 1518846208 1518977280 (151880697048663 / 100000)
      (151893887043343 / 100000) := by
  exact
    packedTile65536 1518846208 1518977280 14 6239 38972 31 _ _ (52853 / 2500) (2114123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1518977280 :
    ThetaLowerSegment 1518977280 1519108352 (151893887043343 / 100000)
      (151907168001721 / 100000) := by
  exact
    packedTile65536 1518977280 1519108352 14 6282 38974 31 _ _ (2114129 / 100000) (528533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519108352 :
    ThetaLowerSegment 1519108352 1519239424 (151907168001721 / 100000)
      (18990029963849 / 12500) := by
  exact
    packedTile65536 1519108352 1519239424 14 6183 38975 31 _ _ (2114137 / 100000) (105707 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519239424 :
    ThetaLowerSegment 1519239424 1519370496 (18990029963849 / 12500) (75966683221653 / 50000) := by
  exact
    packedTile65536 1519239424 1519370496 14 6209 38977 31 _ _ (1057073 / 50000) (2114149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519370496 :
    ThetaLowerSegment 1519370496 1519501568 (75966683221653 / 50000) (37986604809069 / 25000) := by
  exact
    packedTile65536 1519370496 1519501568 14 6174 38979 31 _ _ (422831 / 20000) (1057079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519501568 :
    ThetaLowerSegment 1519501568 1519632640 (37986604809069 / 25000) (18994946166267 / 12500) := by
  exact
    packedTile65536 1519501568 1519632640 14 6220 38980 31 _ _ (2114163 / 100000) (1057083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519632640 :
    ThetaLowerSegment 1519632640 1519763712 (18994946166267 / 12500) (37993138115097 / 25000) := by
  exact
    packedTile65536 1519632640 1519763712 14 6141 38982 31 _ _ (528543 / 25000) (84567 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519763712 :
    ThetaLowerSegment 1519763712 1519894784 (37993138115097 / 25000)
      (151985848544697 / 100000) := by
  exact
    packedTile65536 1519763712 1519894784 14 6289 38984 31 _ _ (2114181 / 100000) (264273 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519894784 :
    ThetaLowerSegment 1519894784 1520025856 (151985848544697 / 100000)
      (151998766239487 / 100000) := by
  exact
    packedTile65536 1519894784 1520025856 14 6110 38985 31 _ _ (2114189 / 100000) (132137 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520025856 :
    ThetaLowerSegment 1520025856 1520156928 (151998766239487 / 100000)
      (152011994776373 / 100000) := by
  exact
    packedTile65536 1520025856 1520156928 14 6257 38987 31 _ _ (1057099 / 50000) (2114201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520156928 :
    ThetaLowerSegment 1520156928 1520288000 (152011994776373 / 100000) (1216199841837 / 800) := by
  exact
    packedTile65536 1520156928 1520288000 14 6142 38989 31 _ _ (1057103 / 50000) (2114209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520288000 :
    ThetaLowerSegment 1520288000 1520419072 (1216199841837 / 800) (3800949724863 / 2500) := by
  exact
    packedTile65536 1520288000 1520419072 14 6153 38990 31 _ _ (422843 / 20000) (1057109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520419072 :
    ThetaLowerSegment 1520419072 1520550144 (3800949724863 / 2500) (19006405911653 / 12500) := by
  exact
    packedTile65536 1520419072 1520550144 14 6271 38992 31 _ _ (132139 / 6250) (2114227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520550144 :
    ThetaLowerSegment 1520550144 1520681216 (19006405911653 / 12500) (1900803994871 / 1250) := by
  exact
    packedTile65536 1520550144 1520681216 14 6183 38994 31 _ _ (264279 / 12500) (422847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520681216 :
    ThetaLowerSegment 1520681216 1520812288 (1900803994871 / 1250) (38019333714319 / 25000) := by
  exact
    packedTile65536 1520681216 1520812288 14 6156 38995 31 _ _ (2114241 / 100000) (528561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520812288 :
    ThetaLowerSegment 1520812288 1520943360 (38019333714319 / 25000) (76045203632513 / 50000) := by
  exact
    packedTile65536 1520812288 1520943360 14 6183 38997 31 _ _ (8457 / 400) (2114253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1520943360 :
    ThetaLowerSegment 1520943360 1521074432 (76045203632513 / 50000) (9506474882543 / 6250) := by
  exact
    packedTile65536 1520943360 1521074432 14 6239 38999 31 _ _ (1057129 / 50000) (2114261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521074432 :
    ThetaLowerSegment 1521074432 1521205504 (9506474882543 / 6250) (76058355402311 / 50000) := by
  exact
    packedTile65536 1521074432 1521205504 14 6202 39000 31 _ _ (2114267 / 100000) (211427 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521205504 :
    ThetaLowerSegment 1521205504 1521336576 (76058355402311 / 50000) (38032426284693 / 25000) := by
  exact
    packedTile65536 1521205504 1521336576 14 6146 39002 31 _ _ (84571 / 4000) (1057139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521336576 :
    ThetaLowerSegment 1521336576 1521467648 (38032426284693 / 25000) (7607130324987 / 5000) := by
  exact
    packedTile65536 1521336576 1521467648 14 6102 39004 31 _ _ (528571 / 25000) (2114287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521467648 :
    ThetaLowerSegment 1521467648 1521598720 (7607130324987 / 5000) (3803898163641 / 2500) := by
  exact
    packedTile65536 1521467648 1521598720 14 6300 39005 31 _ _ (2114293 / 100000) (264287 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521598720 :
    ThetaLowerSegment 1521598720 1521729792 (3803898163641 / 2500) (152169050011947 / 100000) := by
  exact
    packedTile65536 1521598720 1521729792 14 6207 39007 31 _ _ (2114301 / 100000) (66072 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521729792 :
    ThetaLowerSegment 1521729792 1521860864 (152169050011947 / 100000)
      (152182012846557 / 100000) := by
  exact
    packedTile65536 1521729792 1521860864 14 6131 39009 31 _ _ (211431 / 10000) (2114313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521860864 :
    ThetaLowerSegment 1521860864 1521991936 (152182012846557 / 100000)
      (152195075103161 / 100000) := by
  exact
    packedTile65536 1521860864 1521991936 14 6178 39011 31 _ _ (1057159 / 50000) (2114321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1521991936 :
    ThetaLowerSegment 1521991936 1522123008 (152195075103161 / 100000)
      (152208276960949 / 100000) := by
  exact
    packedTile65536 1521991936 1522123008 14 6244 39012 31 _ _ (2114327 / 100000) (211433 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522123008 :
    ThetaLowerSegment 1522123008 1522254080 (152208276960949 / 100000)
      (152221508475637 / 100000) := by
  exact
    packedTile65536 1522123008 1522254080 14 6258 39014 31 _ _ (66073 / 3125) (2114339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522254080 :
    ThetaLowerSegment 1522254080 1522385152 (152221508475637 / 100000)
      (30446939127833 / 20000) := by
  exact
    packedTile65536 1522254080 1522385152 14 6237 39016 31 _ _ (264293 / 12500) (2114347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522385152 :
    ThetaLowerSegment 1522385152 1522516224 (30446939127833 / 20000) (76123911828471 / 50000) := by
  exact
    packedTile65536 1522385152 1522516224 14 6209 39017 31 _ _ (2114353 / 100000) (528589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522516224 :
    ThetaLowerSegment 1522516224 1522647296 (76123911828471 / 50000) (19032635881221 / 12500) := by
  exact
    packedTile65536 1522516224 1522647296 14 6273 39019 31 _ _ (1057181 / 50000) (422873 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522647296 :
    ThetaLowerSegment 1522647296 1522778368 (19032635881221 / 12500) (76137063184779 / 50000) := by
  exact
    packedTile65536 1522647296 1522778368 14 6167 39021 31 _ _ (211437 / 10000) (2114373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522778368 :
    ThetaLowerSegment 1522778368 1522909440 (76137063184779 / 50000)
      (152286937391919 / 100000) := by
  exact
    packedTile65536 1522778368 1522909440 14 6059 39022 31 _ _ (2114379 / 100000) (1057191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1522909440 :
    ThetaLowerSegment 1522909440 1523040512 (152286937391919 / 100000)
      (152300156539443 / 100000) := by
  exact
    packedTile65536 1522909440 1523040512 14 6252 39024 31 _ _ (2114387 / 100000) (211439 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523040512 :
    ThetaLowerSegment 1523040512 1523171584 (152300156539443 / 100000)
      (152313373628839 / 100000) := by
  exact
    packedTile65536 1523040512 1523171584 14 6251 39026 31 _ _ (528599 / 25000) (2114399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523171584 :
    ThetaLowerSegment 1523171584 1523302656 (152313373628839 / 100000)
      (76163185438187 / 50000) := by
  exact
    packedTile65536 1523171584 1523302656 14 6147 39027 31 _ _ (422881 / 20000) (264301 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523302656 :
    ThetaLowerSegment 1523302656 1523433728 (76163185438187 / 50000)
      (152339499266691 / 100000) := by
  exact
    packedTile65536 1523302656 1523433728 14 6209 39029 31 _ _ (2114413 / 100000) (132151 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523433728 :
    ThetaLowerSegment 1523433728 1523564800 (152339499266691 / 100000)
      (152352551593697 / 100000) := by
  exact
    packedTile65536 1523433728 1523564800 14 6173 39031 31 _ _ (1057211 / 50000) (84577 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523564800 :
    ThetaLowerSegment 1523564800 1523695872 (152352551593697 / 100000)
      (152365675860707 / 100000) := by
  exact
    packedTile65536 1523564800 1523695872 14 6207 39032 31 _ _ (211443 / 10000) (2114433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523695872 :
    ThetaLowerSegment 1523695872 1523826944 (152365675860707 / 100000)
      (76189397977351 / 50000) := by
  exact
    packedTile65536 1523695872 1523826944 14 6205 39034 31 _ _ (2114439 / 100000) (1057221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523826944 :
    ThetaLowerSegment 1523826944 1523958016 (76189397977351 / 50000) (76195944308359 / 50000) := by
  exact
    packedTile65536 1523826944 1523958016 14 6192 39036 31 _ _ (132153 / 6250) (2114451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523958016 :
    ThetaLowerSegment 1523958016 1524089088 (76195944308359 / 50000) (76202516037607 / 50000) := by
  exact
    packedTile65536 1523958016 1524089088 14 6216 39037 31 _ _ (264307 / 12500) (2114459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524089088 :
    ThetaLowerSegment 1524089088 1524220160 (76202516037607 / 50000)
      (152418194619839 / 100000) := by
  exact
    packedTile65536 1524089088 1524220160 14 6225 39039 31 _ _ (422893 / 20000) (528617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524220160 :
    ThetaLowerSegment 1524220160 1524351232 (152418194619839 / 100000)
      (19053915422837 / 12500) := by
  exact
    packedTile65536 1524220160 1524351232 14 6209 39041 31 _ _ (2114473 / 100000) (528619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524351232 :
    ThetaLowerSegment 1524351232 1524482304 (19053915422837 / 12500) (76222249360019 / 50000) := by
  exact
    packedTile65536 1524351232 1524482304 14 6231 39042 31 _ _ (1057241 / 50000) (422897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524482304 :
    ThetaLowerSegment 1524482304 1524613376 (76222249360019 / 50000)
      (152457572617891 / 100000) := by
  exact
    packedTile65536 1524482304 1524613376 14 6183 39044 31 _ _ (2114491 / 100000) (1057247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524613376 :
    ThetaLowerSegment 1524613376 1524744448 (152457572617891 / 100000)
      (152470559870749 / 100000) := by
  exact
    packedTile65536 1524613376 1524744448 14 6142 39046 31 _ _ (2114499 / 100000) (1057251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524744448 :
    ThetaLowerSegment 1524744448 1524875520 (152470559870749 / 100000) (6099350768089 / 4000) := by
  exact
    packedTile65536 1524744448 1524875520 14 6247 39047 31 _ _ (528627 / 25000) (2114511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1524875520 :
    ThetaLowerSegment 1524875520 1525006592 (6099350768089 / 4000) (152496779819173 / 100000) := by
  exact
    packedTile65536 1524875520 1525006592 14 6153 39049 31 _ _ (528629 / 25000) (2114519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525006592 :
    ThetaLowerSegment 1525006592 1525137664 (152496779819173 / 100000)
      (76254996742949 / 50000) := by
  exact
    packedTile65536 1525006592 1525137664 14 6249 39051 31 _ _ (84581 / 4000) (66079 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525137664 :
    ThetaLowerSegment 1525137664 1525268736 (76254996742949 / 50000) (76261405895503 / 50000) := by
  exact
    packedTile65536 1525137664 1525268736 14 6062 39053 31 _ _ (1057267 / 50000) (2114537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525268736 :
    ThetaLowerSegment 1525268736 1525399808 (76261405895503 / 50000) (9533502390701 / 6250) := by
  exact
    packedTile65536 1525268736 1525399808 14 6255 39054 31 _ _ (1057271 / 50000) (422909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525399808 :
    ThetaLowerSegment 1525399808 1525530880 (9533502390701 / 6250) (30509850416083 / 20000) := by
  exact
    packedTile65536 1525399808 1525530880 14 6249 39056 31 _ _ (2114551 / 100000) (1057277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525530880 :
    ThetaLowerSegment 1525530880 1525661952 (30509850416083 / 20000) (30512438636299 / 20000) := by
  exact
    packedTile65536 1525530880 1525661952 14 6120 39058 31 _ _ (2114559 / 100000) (1057281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525661952 :
    ThetaLowerSegment 1525661952 1525793024 (30512438636299 / 20000)
      (152575284471983 / 100000) := by
  exact
    packedTile65536 1525661952 1525793024 14 6191 39059 31 _ _ (264321 / 12500) (2114571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525793024 :
    ThetaLowerSegment 1525793024 1525924096 (152575284471983 / 100000)
      (152588415995153 / 100000) := by
  exact
    packedTile65536 1525793024 1525924096 14 6210 39061 31 _ _ (2114577 / 100000) (105729 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1525924096 :
    ThetaLowerSegment 1525924096 1526055168 (152588415995153 / 100000)
      (76300760039199 / 50000) := by
  exact
    packedTile65536 1525924096 1526055168 14 6197 39063 31 _ _ (422917 / 20000) (528647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526055168 :
    ThetaLowerSegment 1526055168 1526186240 (76300760039199 / 50000) (76307338541133 / 50000) := by
  exact
    packedTile65536 1526055168 1526186240 14 6222 39064 31 _ _ (1057297 / 50000) (2114597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526186240 :
    ThetaLowerSegment 1526186240 1526317312 (76307338541133 / 50000) (38156943203113 / 25000) := by
  exact
    packedTile65536 1526186240 1526317312 14 6193 39066 31 _ _ (1057301 / 50000) (422921 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526317312 :
    ThetaLowerSegment 1526317312 1526448384 (38156943203113 / 25000)
      (152640927807483 / 100000) := by
  exact
    packedTile65536 1526317312 1526448384 14 6221 39068 31 _ _ (2114611 / 100000) (1057307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526448384 :
    ThetaLowerSegment 1526448384 1526579456 (152640927807483 / 100000)
      (38163519655761 / 25000) := by
  exact
    packedTile65536 1526448384 1526579456 14 6219 39069 31 _ _ (2114619 / 100000) (1057311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526579456 :
    ThetaLowerSegment 1526579456 1526710528 (38163519655761 / 25000) (19083390470397 / 12500) := by
  exact
    packedTile65536 1526579456 1526710528 14 6169 39071 31 _ _ (528657 / 25000) (2114631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526710528 :
    ThetaLowerSegment 1526710528 1526841600 (19083390470397 / 12500) (4771257328518 / 3125) := by
  exact
    packedTile65536 1526710528 1526841600 14 6200 39073 31 _ _ (2114637 / 100000) (26433 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526841600 :
    ThetaLowerSegment 1526841600 1526972672 (4771257328518 / 3125) (152693309362611 / 100000) := by
  exact
    packedTile65536 1526841600 1526972672 14 6183 39074 31 _ _ (422929 / 20000) (264331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1526972672 :
    ThetaLowerSegment 1526972672 1527103744 (152693309362611 / 100000)
      (152706394841563 / 100000) := by
  exact
    packedTile65536 1526972672 1527103744 14 6188 39076 31 _ _ (1057327 / 50000) (2114657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527103744 :
    ThetaLowerSegment 1527103744 1527234816 (152706394841563 / 100000) (6108784543749 / 4000) := by
  exact
    packedTile65536 1527103744 1527234816 14 6251 39078 31 _ _ (1057331 / 50000) (422933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527234816 :
    ThetaLowerSegment 1527234816 1527365888 (6108784543749 / 4000) (30546553369469 / 20000) := by
  exact
    packedTile65536 1527234816 1527365888 14 6220 39079 31 _ _ (2114671 / 100000) (1057337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527365888 :
    ThetaLowerSegment 1527365888 1527496960 (30546553369469 / 20000) (6109839851417 / 4000) := by
  exact
    packedTile65536 1527365888 1527496960 14 6256 39081 31 _ _ (52867 / 2500) (2114683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527496960 :
    ThetaLowerSegment 1527496960 1527628032 (6109839851417 / 4000) (152759098892273 / 100000) := by
  exact
    packedTile65536 1527496960 1527628032 14 6196 39083 31 _ _ (66084 / 3125) (2114691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527628032 :
    ThetaLowerSegment 1527628032 1527759104 (152759098892273 / 100000)
      (152772104278823 / 100000) := by
  exact
    packedTile65536 1527628032 1527759104 14 6150 39084 31 _ _ (2114697 / 100000) (21147 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527759104 :
    ThetaLowerSegment 1527759104 1527890176 (152772104278823 / 100000)
      (76392725091039 / 50000) := by
  exact
    packedTile65536 1527759104 1527890176 14 6311 39086 31 _ _ (422941 / 20000) (528677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1527890176 :
    ThetaLowerSegment 1527890176 1528021248 (76392725091039 / 50000) (76399259557299 / 50000) := by
  exact
    packedTile65536 1527890176 1528021248 14 6180 39088 31 _ _ (1057357 / 50000) (2114717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528021248 :
    ThetaLowerSegment 1528021248 1528152320 (76399259557299 / 50000) (76405802507167 / 50000) := by
  exact
    packedTile65536 1528021248 1528152320 14 6188 39089 31 _ _ (1057361 / 50000) (84589 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528152320 :
    ThetaLowerSegment 1528152320 1528283392 (76405802507167 / 50000) (76412451221431 / 50000) := by
  exact
    packedTile65536 1528152320 1528283392 14 6288 39091 31 _ _ (2114731 / 100000) (1057367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528283392 :
    ThetaLowerSegment 1528283392 1528414464 (76412451221431 / 50000) (76418988940141 / 50000) := by
  exact
    packedTile65536 1528283392 1528414464 14 6183 39093 31 _ _ (105737 / 5000) (2114743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528414464 :
    ThetaLowerSegment 1528414464 1528545536 (76418988940141 / 50000) (76425567921169 / 50000) := by
  exact
    packedTile65536 1528414464 1528545536 14 6222 39094 31 _ _ (528687 / 25000) (2114751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528545536 :
    ThetaLowerSegment 1528545536 1528676608 (76425567921169 / 50000) (30572811824473 / 20000) := by
  exact
    packedTile65536 1528545536 1528676608 14 6111 39096 31 _ _ (2114757 / 100000) (52869 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528676608 :
    ThetaLowerSegment 1528676608 1528807680 (30572811824473 / 20000) (955482197703 / 625) := by
  exact
    packedTile65536 1528676608 1528807680 14 6191 39098 31 _ _ (422953 / 20000) (132173 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528807680 :
    ThetaLowerSegment 1528807680 1528938752 (955482197703 / 625) (76445134787801 / 50000) := by
  exact
    packedTile65536 1528807680 1528938752 14 6203 39099 31 _ _ (1057387 / 50000) (2114777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528938752 :
    ThetaLowerSegment 1528938752 1529069824 (76445134787801 / 50000) (38225810940793 / 25000) := by
  exact
    packedTile65536 1528938752 1529069824 14 6135 39101 31 _ _ (1057391 / 50000) (422957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529069824 :
    ThetaLowerSegment 1529069824 1529200896 (38225810940793 / 25000) (76458357490921 / 50000) := by
  exact
    packedTile65536 1529069824 1529200896 14 6370 39103 31 _ _ (2114791 / 100000) (1057397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529200896 :
    ThetaLowerSegment 1529200896 1529331968 (76458357490921 / 50000) (76464965183521 / 50000) := by
  exact
    packedTile65536 1529200896 1529331968 14 6249 39104 31 _ _ (5287 / 250) (2114803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529331968 :
    ThetaLowerSegment 1529331968 1529463040 (76464965183521 / 50000) (76471542236401 / 50000) := by
  exact
    packedTile65536 1529331968 1529463040 14 6220 39106 31 _ _ (264351 / 12500) (2114811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529463040 :
    ThetaLowerSegment 1529463040 1529594112 (76471542236401 / 50000) (19119536702473 / 12500) := by
  exact
    packedTile65536 1529463040 1529594112 14 6246 39108 31 _ _ (2114817 / 100000) (105741 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529594112 :
    ThetaLowerSegment 1529594112 1529725184 (19119536702473 / 12500) (19121194725273 / 12500) := by
  exact
    packedTile65536 1529594112 1529725184 14 6272 39110 31 _ _ (84593 / 4000) (528707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529725184 :
    ThetaLowerSegment 1529725184 1529856256 (19121194725273 / 12500) (19122835836457 / 12500) := by
  exact
    packedTile65536 1529725184 1529856256 14 6208 39111 31 _ _ (1057417 / 50000) (2114837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529856256 :
    ThetaLowerSegment 1529856256 1529987328 (19122835836457 / 12500) (19124489642901 / 12500) := by
  exact
    packedTile65536 1529856256 1529987328 14 6256 39113 31 _ _ (1057421 / 50000) (422969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1529987328 :
    ThetaLowerSegment 1529987328 1530118400 (19124489642901 / 12500)
      (153008870605583 / 100000) := by
  exact
    packedTile65536 1529987328 1530118400 14 6125 39115 31 _ _ (2114851 / 100000) (1057427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530118400 :
    ThetaLowerSegment 1530118400 1530249472 (153008870605583 / 100000)
      (153022115973763 / 100000) := by
  exact
    packedTile65536 1530118400 1530249472 14 6263 39116 31 _ _ (105743 / 5000) (2114863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530249472 :
    ThetaLowerSegment 1530249472 1530380544 (153022115973763 / 100000)
      (30607013485079 / 20000) := by
  exact
    packedTile65536 1530249472 1530380544 14 6124 39118 31 _ _ (528717 / 25000) (2114871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530380544 :
    ThetaLowerSegment 1530380544 1530511616 (30607013485079 / 20000)
      (153048205041319 / 100000) := by
  exact
    packedTile65536 1530380544 1530511616 14 6212 39120 31 _ _ (2114877 / 100000) (13218 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530511616 :
    ThetaLowerSegment 1530511616 1530642688 (153048205041319 / 100000)
      (153061359626019 / 100000) := by
  exact
    packedTile65536 1530511616 1530642688 14 6220 39121 31 _ _ (422977 / 20000) (264361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530642688 :
    ThetaLowerSegment 1530642688 1530773760 (153061359626019 / 100000)
      (153074471968819 / 100000) := by
  exact
    packedTile65536 1530642688 1530773760 14 6200 39123 31 _ _ (1057447 / 50000) (2114897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530773760 :
    ThetaLowerSegment 1530773760 1530904832 (153074471968819 / 100000)
      (153087419398863 / 100000) := by
  exact
    packedTile65536 1530773760 1530904832 14 6122 39125 31 _ _ (1057451 / 50000) (422981 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1530904832 :
    ThetaLowerSegment 1530904832 1531035904 (153087419398863 / 100000) (7655020987839 / 5000) := by
  exact
    packedTile65536 1530904832 1531035904 14 6147 39126 31 _ _ (2114911 / 100000) (1057457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531035904 :
    ThetaLowerSegment 1531035904 1531166976 (7655020987839 / 5000) (7655667941867 / 5000) := by
  exact
    packedTile65536 1531035904 1531166976 14 6118 39128 31 _ _ (52873 / 2500) (2114923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531166976 :
    ThetaLowerSegment 1531166976 1531298048 (7655667941867 / 5000) (38281611502951 / 25000) := by
  exact
    packedTile65536 1531166976 1531298048 14 6188 39130 31 _ _ (132183 / 6250) (2114931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531298048 :
    ThetaLowerSegment 1531298048 1531429120 (38281611502951 / 25000) (76569772965791 / 50000) := by
  exact
    packedTile65536 1531298048 1531429120 14 6194 39131 31 _ _ (2114937 / 100000) (105747 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531429120 :
    ThetaLowerSegment 1531429120 1531560192 (76569772965791 / 50000)
      (153152495739817 / 100000) := by
  exact
    packedTile65536 1531429120 1531560192 14 6123 39133 31 _ _ (422989 / 20000) (528737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531560192 :
    ThetaLowerSegment 1531560192 1531691264 (153152495739817 / 100000)
      (153165642293881 / 100000) := by
  exact
    packedTile65536 1531560192 1531691264 14 6216 39135 31 _ _ (1057477 / 50000) (2114957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531691264 :
    ThetaLowerSegment 1531691264 1531822336 (153165642293881 / 100000)
      (153178623930637 / 100000) := by
  exact
    packedTile65536 1531691264 1531822336 14 6138 39136 31 _ _ (1057481 / 50000) (422993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531822336 :
    ThetaLowerSegment 1531822336 1531953408 (153178623930637 / 100000)
      (38297966441017 / 25000) := by
  exact
    packedTile65536 1531822336 1531953408 14 6261 39138 31 _ _ (2114971 / 100000) (1057487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1531953408 :
    ThetaLowerSegment 1531953408 1532084480 (38297966441017 / 25000) (38301236198551 / 25000) := by
  exact
    packedTile65536 1531953408 1532084480 14 6184 39140 31 _ _ (2114979 / 100000) (1057491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532084480 :
    ThetaLowerSegment 1532084480 1532215552 (38301236198551 / 25000) (38304540867301 / 25000) := by
  exact
    packedTile65536 1532084480 1532215552 14 6250 39141 31 _ _ (528747 / 25000) (2114991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532215552 :
    ThetaLowerSegment 1532215552 1532346624 (38304540867301 / 25000)
      (153231278565601 / 100000) := by
  exact
    packedTile65536 1532215552 1532346624 14 6201 39143 31 _ _ (2114997 / 100000) (423 / 20)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532346624 :
    ThetaLowerSegment 1532346624 1532477696 (153231278565601 / 100000)
      (38311033920249 / 25000) := by
  exact
    packedTile65536 1532346624 1532477696 14 6079 39145 31 _ _ (423001 / 20000) (66094 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532477696 :
    ThetaLowerSegment 1532477696 1532608768 (38311033920249 / 25000) (76628623326391 / 50000) := by
  exact
    packedTile65536 1532477696 1532608768 14 6199 39146 31 _ _ (1057507 / 50000) (2115017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532608768 :
    ThetaLowerSegment 1532608768 1532739840 (76628623326391 / 50000) (7663521056241 / 5000) := by
  exact
    packedTile65536 1532608768 1532739840 14 6229 39148 31 _ _ (1057511 / 50000) (84601 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532739840 :
    ThetaLowerSegment 1532739840 1532870912 (7663521056241 / 5000) (7664176715851 / 5000) := by
  exact
    packedTile65536 1532739840 1532870912 14 6200 39150 31 _ _ (2115031 / 100000) (1057517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532870912 :
    ThetaLowerSegment 1532870912 1533001984 (7664176715851 / 5000) (19162079887333 / 12500) := by
  exact
    packedTile65536 1532870912 1533001984 14 6196 39151 31 _ _ (2115039 / 100000) (1057521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533001984 :
    ThetaLowerSegment 1533001984 1533133056 (19162079887333 / 12500) (9581855955623 / 6250) := by
  exact
    packedTile65536 1533001984 1533133056 14 6173 39153 31 _ _ (264381 / 12500) (2115051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533133056 :
    ThetaLowerSegment 1533133056 1533264128 (9581855955623 / 6250) (9582674746677 / 6250) := by
  exact
    packedTile65536 1533133056 1533264128 14 6194 39155 31 _ _ (132191 / 6250) (2115059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533264128 :
    ThetaLowerSegment 1533264128 1533395200 (9582674746677 / 6250) (153335877623857 / 100000) := by
  exact
    packedTile65536 1533264128 1533395200 14 6185 39156 31 _ _ (423013 / 20000) (528767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533395200 :
    ThetaLowerSegment 1533395200 1533526272 (153335877623857 / 100000)
      (153348895904327 / 100000) := by
  exact
    packedTile65536 1533395200 1533526272 14 6155 39158 31 _ _ (1057537 / 50000) (2115077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533526272 :
    ThetaLowerSegment 1533526272 1533657344 (153348895904327 / 100000)
      (153362129972401 / 100000) := by
  exact
    packedTile65536 1533526272 1533657344 14 6257 39160 31 _ _ (1057541 / 50000) (423017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533657344 :
    ThetaLowerSegment 1533657344 1533788416 (153362129972401 / 100000)
      (153375239306419 / 100000) := by
  exact
    packedTile65536 1533657344 1533788416 14 6198 39161 31 _ _ (2115091 / 100000) (1057547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533788416 :
    ThetaLowerSegment 1533788416 1533919488 (153375239306419 / 100000)
      (153388513667743 / 100000) := by
  exact
    packedTile65536 1533788416 1533919488 14 6276 39163 31 _ _ (2115099 / 100000) (1057551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1533919488 :
    ThetaLowerSegment 1533919488 1534050560 (153388513667743 / 100000)
      (153401500430863 / 100000) := by
  exact
    packedTile65536 1533919488 1534050560 14 6140 39165 31 _ _ (528777 / 25000) (2115111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534050560 :
    ThetaLowerSegment 1534050560 1534181632 (153401500430863 / 100000)
      (153414531660539 / 100000) := by
  exact
    packedTile65536 1534050560 1534181632 14 6161 39166 31 _ _ (528779 / 25000) (2115119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534181632 :
    ThetaLowerSegment 1534181632 1534312704 (153414531660539 / 100000)
      (38356875930541 / 25000) := by
  exact
    packedTile65536 1534181632 1534312704 14 6133 39168 31 _ _ (16921 / 800) (264391 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534312704 :
    ThetaLowerSegment 1534312704 1534443776 (38356875930541 / 25000) (76720348960909 / 50000) := by
  exact
    packedTile65536 1534312704 1534443776 14 6238 39170 31 _ _ (2115133 / 100000) (66098 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534443776 :
    ThetaLowerSegment 1534443776 1534574848 (76720348960909 / 50000) (15345386679591 / 10000) := by
  exact
    packedTile65536 1534443776 1534574848 14 6226 39171 31 _ _ (1057571 / 50000) (423029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534574848 :
    ThetaLowerSegment 1534574848 1534705920 (15345386679591 / 10000) (3836674042239 / 2500) := by
  exact
    packedTile65536 1534574848 1534705920 14 6191 39173 31 _ _ (42303 / 2000) (2115153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534705920 :
    ThetaLowerSegment 1534705920 1534836992 (3836674042239 / 2500) (76740086486337 / 50000) := by
  exact
    packedTile65536 1534705920 1534836992 14 6246 39175 31 _ _ (2115159 / 100000) (1057581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534836992 :
    ThetaLowerSegment 1534836992 1534968064 (76740086486337 / 50000) (76746606491697 / 50000) := by
  exact
    packedTile65536 1534836992 1534968064 14 6165 39176 31 _ _ (66099 / 3125) (2115171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1534968064 :
    ThetaLowerSegment 1534968064 1535099136 (76746606491697 / 50000) (15350627631037 / 10000) := by
  exact
    packedTile65536 1534968064 1535099136 14 6176 39178 31 _ _ (264397 / 12500) (2115179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535099136 :
    ThetaLowerSegment 1535099136 1535230208 (15350627631037 / 10000) (1535194285307 / 1000) := by
  exact
    packedTile65536 1535099136 1535230208 14 6218 39180 31 _ _ (423037 / 20000) (528797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535230208 :
    ThetaLowerSegment 1535230208 1535361280 (1535194285307 / 1000) (76766256557299 / 50000) := by
  exact
    packedTile65536 1535230208 1535361280 14 6186 39182 31 _ _ (2115193 / 100000) (528799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535361280 :
    ThetaLowerSegment 1535361280 1535492352 (76766256557299 / 50000) (15354561890619 / 10000) := by
  exact
    packedTile65536 1535361280 1535492352 14 6196 39183 31 _ _ (1057601 / 50000) (423041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535492352 :
    ThetaLowerSegment 1535492352 1535623424 (15354561890619 / 10000) (7677927670767 / 5000) := by
  exact
    packedTile65536 1535492352 1535623424 14 6115 39185 31 _ _ (211521 / 10000) (2115213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535623424 :
    ThetaLowerSegment 1535623424 1535754496 (7677927670767 / 5000) (30714348361161 / 20000) := by
  exact
    packedTile65536 1535623424 1535754496 14 6235 39187 31 _ _ (2115219 / 100000) (1057611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535754496 :
    ThetaLowerSegment 1535754496 1535885568 (30714348361161 / 20000) (9599057875981 / 6250) := by
  exact
    packedTile65536 1535754496 1535885568 14 6233 39188 31 _ _ (2115227 / 100000) (211523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1535885568 :
    ThetaLowerSegment 1535885568 1536016640 (9599057875981 / 6250) (7679904033419 / 5000) := by
  exact
    packedTile65536 1535885568 1536016640 14 6219 39190 31 _ _ (528809 / 25000) (2115239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536016640 :
    ThetaLowerSegment 1536016640 1536147712 (7679904033419 / 5000) (38402768124257 / 25000) := by
  exact
    packedTile65536 1536016640 1536147712 14 6142 39192 31 _ _ (528811 / 25000) (2115247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536147712 :
    ThetaLowerSegment 1536147712 1536278784 (38402768124257 / 25000) (76811964502381 / 50000) := by
  exact
    packedTile65536 1536147712 1536278784 14 6078 39193 31 _ _ (2115253 / 100000) (264407 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536278784 :
    ThetaLowerSegment 1536278784 1536409856 (76811964502381 / 50000)
      (153636893439431 / 100000) := by
  exact
    packedTile65536 1536278784 1536409856 14 6129 39195 31 _ _ (2115261 / 100000) (66102 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536409856 :
    ThetaLowerSegment 1536409856 1536540928 (153636893439431 / 100000)
      (153650166758681 / 100000) := by
  exact
    packedTile65536 1536409856 1536540928 14 6275 39197 31 _ _ (211527 / 10000) (2115273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536540928 :
    ThetaLowerSegment 1536540928 1536672000 (153650166758681 / 100000)
      (153663423205907 / 100000) := by
  exact
    packedTile65536 1536540928 1536672000 14 6267 39198 31 _ _ (1057639 / 50000) (2115281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536672000 :
    ThetaLowerSegment 1536672000 1536803072 (153663423205907 / 100000)
      (153676529524159 / 100000) := by
  exact
    packedTile65536 1536672000 1536803072 14 6196 39200 31 _ _ (2115287 / 100000) (211529 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536803072 :
    ThetaLowerSegment 1536803072 1536934144 (153676529524159 / 100000)
      (153689671858207 / 100000) := by
  exact
    packedTile65536 1536803072 1536934144 14 6213 39202 31 _ _ (66103 / 3125) (2115299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536934144 :
    ThetaLowerSegment 1536934144 1537065216 (153689671858207 / 100000)
      (153702816357263 / 100000) := by
  exact
    packedTile65536 1536934144 1537065216 14 6214 39203 31 _ _ (264413 / 12500) (2115307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537065216 :
    ThetaLowerSegment 1537065216 1537196288 (153702816357263 / 100000)
      (153715994757253 / 100000) := by
  exact
    packedTile65536 1537065216 1537196288 14 6230 39205 31 _ _ (2115313 / 100000) (528829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537196288 :
    ThetaLowerSegment 1537196288 1537327360 (153715994757253 / 100000)
      (38432319214453 / 25000) := by
  exact
    packedTile65536 1537196288 1537327360 14 6279 39207 31 _ _ (2115321 / 100000) (528831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537327360 :
    ThetaLowerSegment 1537327360 1537458432 (38432319214453 / 25000) (38435568361333 / 25000) := by
  exact
    packedTile65536 1537327360 1537458432 14 6144 39208 31 _ _ (211533 / 10000) (2115333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537458432 :
    ThetaLowerSegment 1537458432 1537589504 (38435568361333 / 25000) (76877655136713 / 50000) := by
  exact
    packedTile65536 1537458432 1537589504 14 6163 39210 31 _ _ (1057669 / 50000) (2115341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537589504 :
    ThetaLowerSegment 1537589504 1537720576 (76877655136713 / 50000) (19221047360899 / 12500) := by
  exact
    packedTile65536 1537589504 1537720576 14 6178 39212 31 _ _ (2115347 / 100000) (42307 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537720576 :
    ThetaLowerSegment 1537720576 1537851648 (19221047360899 / 12500) (38445362945273 / 25000) := by
  exact
    packedTile65536 1537720576 1537851648 14 6180 39213 31 _ _ (423071 / 20000) (1057679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537851648 :
    ThetaLowerSegment 1537851648 1537982720 (38445362945273 / 25000) (4806079624988 / 3125) := by
  exact
    packedTile65536 1537851648 1537982720 14 6191 39215 31 _ _ (528841 / 25000) (2115367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1537982720 :
    ThetaLowerSegment 1537982720 1538113792 (4806079624988 / 3125) (38451897316999 / 25000) := by
  exact
    packedTile65536 1537982720 1538113792 14 6165 39217 31 _ _ (528843 / 25000) (16923 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538113792 :
    ThetaLowerSegment 1538113792 1538244864 (38451897316999 / 25000) (76910299430573 / 50000) := by
  exact
    packedTile65536 1538113792 1538244864 14 6150 39218 31 _ _ (2115381 / 100000) (264423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538244864 :
    ThetaLowerSegment 1538244864 1538375936 (76910299430573 / 50000) (76916848674917 / 50000) := by
  exact
    packedTile65536 1538244864 1538375936 14 6192 39220 31 _ _ (2115389 / 100000) (66106 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538375936 :
    ThetaLowerSegment 1538375936 1538507008 (76916848674917 / 50000) (19230846578109 / 12500) := by
  exact
    packedTile65536 1538375936 1538507008 14 6181 39222 31 _ _ (1057699 / 50000) (2115401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538507008 :
    ThetaLowerSegment 1538507008 1538638080 (19230846578109 / 12500) (38464947708349 / 25000) := by
  exact
    packedTile65536 1538507008 1538638080 14 6154 39223 31 _ _ (1057703 / 50000) (2115409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538638080 :
    ThetaLowerSegment 1538638080 1538769152 (38464947708349 / 25000)
      (153872938137621 / 100000) := by
  exact
    packedTile65536 1538638080 1538769152 14 6215 39225 31 _ _ (423083 / 20000) (1057709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538769152 :
    ThetaLowerSegment 1538769152 1538900224 (153872938137621 / 100000)
      (38471501276373 / 25000) := by
  exact
    packedTile65536 1538769152 1538900224 14 6177 39227 31 _ _ (2115423 / 100000) (1057713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1538900224 :
    ThetaLowerSegment 1538900224 1539031296 (38471501276373 / 25000) (38474789186559 / 25000) := by
  exact
    packedTile65536 1538900224 1539031296 14 6217 39228 31 _ _ (264429 / 12500) (423087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539031296 :
    ThetaLowerSegment 1539031296 1539162368 (38474789186559 / 25000) (38478059656799 / 25000) := by
  exact
    packedTile65536 1539031296 1539162368 14 6184 39230 31 _ _ (26443 / 1250) (2115443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539162368 :
    ThetaLowerSegment 1539162368 1539293440 (38478059656799 / 25000)
      (153925305755669 / 100000) := by
  exact
    packedTile65536 1539162368 1539293440 14 6177 39232 31 _ _ (2115449 / 100000) (528863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539293440 :
    ThetaLowerSegment 1539293440 1539424512 (153925305755669 / 100000)
      (19242297145559 / 12500) := by
  exact
    packedTile65536 1539293440 1539424512 14 6179 39233 31 _ _ (2115457 / 100000) (105773 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539424512 :
    ThetaLowerSegment 1539424512 1539555584 (19242297145559 / 12500) (19243947209039 / 12500) := by
  exact
    packedTile65536 1539424512 1539555584 14 6240 39235 31 _ _ (1057733 / 50000) (2115469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539555584 :
    ThetaLowerSegment 1539555584 1539686656 (19243947209039 / 12500) (76982413442987 / 50000) := by
  exact
    packedTile65536 1539555584 1539686656 14 6263 39237 31 _ _ (1057737 / 50000) (2115477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539686656 :
    ThetaLowerSegment 1539686656 1539817728 (76982413442987 / 50000) (30795583075859 / 20000) := by
  exact
    packedTile65536 1539686656 1539817728 14 6187 39238 31 _ _ (2115483 / 100000) (1057743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539817728 :
    ThetaLowerSegment 1539817728 1539948800 (30795583075859 / 20000) (19248886067719 / 12500) := by
  exact
    packedTile65536 1539817728 1539948800 14 6227 39240 31 _ _ (2115491 / 100000) (1057747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1539948800 :
    ThetaLowerSegment 1539948800 1540079872 (19248886067719 / 12500) (4812631262836 / 3125) := by
  exact
    packedTile65536 1539948800 1540079872 14 6198 39242 31 _ _ (4231 / 200) (2115503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540079872 :
    ThetaLowerSegment 1540079872 1540210944 (4812631262836 / 3125) (154017221368647 / 100000) := by
  exact
    packedTile65536 1540079872 1540210944 14 6155 39243 31 _ _ (2115509 / 100000) (264439 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540210944 :
    ThetaLowerSegment 1540210944 1540342016 (154017221368647 / 100000) (3850755742067 / 2500) := by
  exact
    packedTile65536 1540210944 1540342016 14 6149 39245 31 _ _ (2115517 / 100000) (13222 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540342016 :
    ThetaLowerSegment 1540342016 1540473088 (3850755742067 / 2500) (19255426705089 / 12500) := by
  exact
    packedTile65536 1540342016 1540473088 14 6232 39247 31 _ _ (1057763 / 50000) (2115529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540473088 :
    ThetaLowerSegment 1540473088 1540604160 (19255426705089 / 12500) (38514106043703 / 25000) := by
  exact
    packedTile65536 1540473088 1540604160 14 6150 39248 31 _ _ (1057767 / 50000) (2115537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540604160 :
    ThetaLowerSegment 1540604160 1540735232 (38514106043703 / 25000) (19258687278819 / 12500) := by
  exact
    packedTile65536 1540604160 1540735232 14 6180 39250 31 _ _ (2115543 / 100000) (1057773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540735232 :
    ThetaLowerSegment 1540735232 1540866304 (19258687278819 / 12500) (38520676932749 / 25000) := by
  exact
    packedTile65536 1540735232 1540866304 14 6244 39252 31 _ _ (2115551 / 100000) (1057777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540866304 :
    ThetaLowerSegment 1540866304 1540997376 (38520676932749 / 25000) (38523965041879 / 25000) := by
  exact
    packedTile65536 1540866304 1540997376 14 6217 39253 31 _ _ (52889 / 2500) (2115563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540997376 :
    ThetaLowerSegment 1540997376 1541128448 (38523965041879 / 25000) (38527212438759 / 25000) := by
  exact
    packedTile65536 1540997376 1541128448 14 6140 39255 31 _ _ (132223 / 6250) (2115571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541128448 :
    ThetaLowerSegment 1541128448 1541259520 (38527212438759 / 25000)
      (154121904980703 / 100000) := by
  exact
    packedTile65536 1541128448 1541259520 14 6171 39257 31 _ _ (2115577 / 100000) (105779 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541259520 :
    ThetaLowerSegment 1541259520 1541390592 (154121904980703 / 100000)
      (19266877965411 / 12500) := by
  exact
    packedTile65536 1541259520 1541390592 14 6201 39258 31 _ _ (423117 / 20000) (528897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541390592 :
    ThetaLowerSegment 1541390592 1541521664 (19266877965411 / 12500) (77074028948961 / 50000) := by
  exact
    packedTile65536 1541390592 1541521664 14 6161 39260 31 _ _ (1057797 / 50000) (2115597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541521664 :
    ThetaLowerSegment 1541521664 1541652736 (77074028948961 / 50000) (77080631742803 / 50000) := by
  exact
    packedTile65536 1541521664 1541652736 14 6242 39262 31 _ _ (1057801 / 50000) (423121 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541652736 :
    ThetaLowerSegment 1541652736 1541783808 (77080631742803 / 50000) (30834892556527 / 20000) := by
  exact
    packedTile65536 1541652736 1541783808 14 6239 39263 31 _ _ (2115611 / 100000) (1057807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541783808 :
    ThetaLowerSegment 1541783808 1541914880 (30834892556527 / 20000) (15418780176043 / 10000) := by
  exact
    packedTile65536 1541783808 1541914880 14 6305 39265 31 _ _ (2115619 / 100000) (1057811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1541914880 :
    ThetaLowerSegment 1541914880 1542045952 (15418780176043 / 10000) (77100328158079 / 50000) := by
  exact
    packedTile65536 1541914880 1542045952 14 6076 39267 31 _ _ (528907 / 25000) (2115631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542045952 :
    ThetaLowerSegment 1542045952 1542177024 (77100328158079 / 50000) (77106865473319 / 50000) := by
  exact
    packedTile65536 1542045952 1542177024 14 6180 39268 31 _ _ (528909 / 25000) (2115639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542177024 :
    ThetaLowerSegment 1542177024 1542308096 (77106865473319 / 50000)
      (154226998156433 / 100000) := by
  exact
    packedTile65536 1542177024 1542308096 14 6271 39270 31 _ _ (423129 / 20000) (66114 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542308096 :
    ThetaLowerSegment 1542308096 1542439168 (154226998156433 / 100000)
      (77119995190753 / 50000) := by
  exact
    packedTile65536 1542308096 1542439168 14 6141 39272 31 _ _ (2115653 / 100000) (264457 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542439168 :
    ThetaLowerSegment 1542439168 1542570240 (77119995190753 / 50000) (38563278458223 / 25000) := by
  exact
    packedTile65536 1542439168 1542570240 14 6203 39273 31 _ _ (1057831 / 50000) (423133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542570240 :
    ThetaLowerSegment 1542570240 1542701312 (38563278458223 / 25000) (19283279402279 / 12500) := by
  exact
    packedTile65536 1542570240 1542701312 14 6202 39275 31 _ _ (211567 / 10000) (2115673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542701312 :
    ThetaLowerSegment 1542701312 1542832384 (19283279402279 / 12500) (9642461642431 / 6250) := by
  exact
    packedTile65536 1542701312 1542832384 14 6216 39277 31 _ _ (2115679 / 100000) (1057841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542832384 :
    ThetaLowerSegment 1542832384 1542963456 (9642461642431 / 6250) (9643278297613 / 6250) := by
  exact
    packedTile65536 1542832384 1542963456 14 6176 39278 31 _ _ (2115687 / 100000) (211569 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1542963456 :
    ThetaLowerSegment 1542963456 1543094528 (9643278297613 / 6250) (9644098923199 / 6250) := by
  exact
    packedTile65536 1542963456 1543094528 14 6206 39280 31 _ _ (132231 / 6250) (2115699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543094528 :
    ThetaLowerSegment 1543094528 1543225600 (9644098923199 / 6250) (4822457395777 / 3125) := by
  exact
    packedTile65536 1543094528 1543225600 14 6170 39282 31 _ _ (264463 / 12500) (2115707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543225600 :
    ThetaLowerSegment 1543225600 1543356672 (4822457395777 / 3125) (77165828381333 / 50000) := by
  exact
    packedTile65536 1543225600 1543356672 14 6154 39283 31 _ _ (2115713 / 100000) (528929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543356672 :
    ThetaLowerSegment 1543356672 1543487744 (77165828381333 / 50000)
      (154344636711001 / 100000) := by
  exact
    packedTile65536 1543356672 1543487744 14 6135 39285 31 _ _ (2115721 / 100000) (528931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543487744 :
    ThetaLowerSegment 1543487744 1543618816 (154344636711001 / 100000)
      (154357673839261 / 100000) := by
  exact
    packedTile65536 1543487744 1543618816 14 6162 39287 31 _ _ (211573 / 10000) (2115733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543618816 :
    ThetaLowerSegment 1543618816 1543749888 (154357673839261 / 100000)
      (154370793530599 / 100000) := by
  exact
    packedTile65536 1543618816 1543749888 14 6201 39288 31 _ _ (1057869 / 50000) (2115741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543749888 :
    ThetaLowerSegment 1543749888 1543880960 (154370793530599 / 100000)
      (77191897397957 / 50000) := by
  exact
    packedTile65536 1543749888 1543880960 14 6145 39290 31 _ _ (2115747 / 100000) (8463 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1543880960 :
    ThetaLowerSegment 1543880960 1544012032 (77191897397957 / 50000)
      (154397033074949 / 100000) := by
  exact
    packedTile65536 1543880960 1544012032 14 6257 39292 31 _ _ (423151 / 20000) (1057879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544012032 :
    ThetaLowerSegment 1544012032 1544143104 (154397033074949 / 100000)
      (154410281989117 / 100000) := by
  exact
    packedTile65536 1544012032 1544143104 14 6262 39293 31 _ _ (528941 / 25000) (2115767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544143104 :
    ThetaLowerSegment 1544143104 1544274176 (154410281989117 / 100000)
      (154423245324161 / 100000) := by
  exact
    packedTile65536 1544143104 1544274176 14 6127 39295 31 _ _ (528943 / 25000) (84631 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544274176 :
    ThetaLowerSegment 1544274176 1544405248 (154423245324161 / 100000)
      (154436318728781 / 100000) := by
  exact
    packedTile65536 1544274176 1544405248 14 6179 39297 31 _ _ (105789 / 5000) (2115783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544405248 :
    ThetaLowerSegment 1544405248 1544536320 (154436318728781 / 100000)
      (154449419694269 / 100000) := by
  exact
    packedTile65536 1544405248 1544536320 14 6192 39298 31 _ _ (2115789 / 100000) (132237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544536320 :
    ThetaLowerSegment 1544536320 1544667392 (154449419694269 / 100000)
      (77231337581237 / 50000) := by
  exact
    packedTile65536 1544536320 1544667392 14 6265 39300 31 _ _ (2115797 / 100000) (10579 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544667392 :
    ThetaLowerSegment 1544667392 1544798464 (77231337581237 / 50000) (4827366222077 / 3125) := by
  exact
    packedTile65536 1544667392 1544798464 14 6165 39302 31 _ _ (1057903 / 50000) (2115809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544798464 :
    ThetaLowerSegment 1544798464 1544929536 (4827366222077 / 3125) (77244455603377 / 50000) := by
  exact
    packedTile65536 1544798464 1544929536 14 6235 39303 31 _ _ (1057907 / 50000) (2115817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544929536 :
    ThetaLowerSegment 1544929536 1545060608 (77244455603377 / 50000) (77251023117969 / 50000) := by
  exact
    packedTile65536 1544929536 1545060608 14 6208 39305 31 _ _ (2115823 / 100000) (1057913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545060608 :
    ThetaLowerSegment 1545060608 1545191680 (77251023117969 / 50000)
      (154515035322447 / 100000) := by
  exact
    packedTile65536 1545060608 1545191680 14 6139 39307 31 _ _ (2115831 / 100000) (1057917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545191680 :
    ThetaLowerSegment 1545191680 1545322752 (154515035322447 / 100000)
      (154528259322447 / 100000) := by
  exact
    packedTile65536 1545191680 1545322752 14 6250 39308 31 _ _ (13224 / 625) (2115843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545322752 :
    ThetaLowerSegment 1545322752 1545339136 (154528259322447 / 100000)
      (30905980244099 / 20000) := by
  exact
    packedTile65536 1545322752 1545339136 11 776 39310 31 _ _ (264481 / 12500) (2115851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545339136 :
    ThetaLowerSegment 1545339136 1545341184 (30905980244099 / 20000) (77265055344773 / 50000) := by
  exact
    packedTile65536 1545339136 1545341184 8 99 39310 31 _ _ (2115849 / 100000) (528963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1513341184_1545341184 :
    ThetaLowerSegment 1513341184 1545341184 (151330029786991 / 100000)
      (77265055344773 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1513341184 cell1513472256)
                  (ThetaLowerSegment.join cell1513603328 cell1513734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1513865472 cell1513996544)
                  (ThetaLowerSegment.join cell1514127616 cell1514258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1514389760 cell1514520832)
                  (ThetaLowerSegment.join cell1514651904 cell1514782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1514914048 cell1515045120)
                  (ThetaLowerSegment.join cell1515176192 cell1515307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1515438336 cell1515569408)
                  (ThetaLowerSegment.join cell1515700480 cell1515831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1515962624 cell1516093696)
                  (ThetaLowerSegment.join cell1516224768 cell1516355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1516486912 cell1516617984)
                  (ThetaLowerSegment.join cell1516749056 cell1516880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1517011200 cell1517142272)
                  (ThetaLowerSegment.join cell1517273344 cell1517404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1517535488 cell1517666560)
                  (ThetaLowerSegment.join cell1517797632 cell1517928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1518059776 cell1518190848)
                  (ThetaLowerSegment.join cell1518321920 cell1518452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1518584064 cell1518715136)
                  (ThetaLowerSegment.join cell1518846208 cell1518977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1519108352 cell1519239424)
                  (ThetaLowerSegment.join cell1519370496 cell1519501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1519632640 cell1519763712)
                  (ThetaLowerSegment.join cell1519894784 cell1520025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1520156928 cell1520288000)
                  (ThetaLowerSegment.join cell1520419072 cell1520550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1520681216 cell1520812288)
                  (ThetaLowerSegment.join cell1520943360 cell1521074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1521205504 cell1521336576)
                  (ThetaLowerSegment.join cell1521467648 cell1521598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1521729792 cell1521860864)
                  (ThetaLowerSegment.join cell1521991936 cell1522123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1522254080 cell1522385152)
                  (ThetaLowerSegment.join cell1522516224 cell1522647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1522778368 cell1522909440)
                  (ThetaLowerSegment.join cell1523040512 cell1523171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1523302656 cell1523433728)
                  (ThetaLowerSegment.join cell1523564800 cell1523695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1523826944 cell1523958016)
                  (ThetaLowerSegment.join cell1524089088 cell1524220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1524351232 cell1524482304)
                  (ThetaLowerSegment.join cell1524613376 cell1524744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1524875520 cell1525006592)
                  (ThetaLowerSegment.join cell1525137664 cell1525268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1525399808 cell1525530880)
                  (ThetaLowerSegment.join cell1525661952 cell1525793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1525924096 cell1526055168)
                  (ThetaLowerSegment.join cell1526186240 cell1526317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1526448384 cell1526579456)
                  (ThetaLowerSegment.join cell1526710528 cell1526841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1526972672 cell1527103744)
                  (ThetaLowerSegment.join cell1527234816 cell1527365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1527496960 cell1527628032)
                  (ThetaLowerSegment.join cell1527759104 cell1527890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1528021248 cell1528152320)
                  (ThetaLowerSegment.join cell1528283392 cell1528414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1528545536 cell1528676608)
                  (ThetaLowerSegment.join cell1528807680 cell1528938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1529069824 cell1529200896)
                  (ThetaLowerSegment.join cell1529331968 cell1529463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1529594112 cell1529725184)
                  (ThetaLowerSegment.join cell1529856256 cell1529987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1530118400 cell1530249472)
                  (ThetaLowerSegment.join cell1530380544 cell1530511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1530642688 cell1530773760)
                  (ThetaLowerSegment.join cell1530904832 cell1531035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1531166976 cell1531298048)
                  (ThetaLowerSegment.join cell1531429120 cell1531560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1531691264 cell1531822336)
                  (ThetaLowerSegment.join cell1531953408 cell1532084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1532215552 cell1532346624)
                  (ThetaLowerSegment.join cell1532477696 cell1532608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1532739840 cell1532870912)
                  (ThetaLowerSegment.join cell1533001984 cell1533133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1533264128 cell1533395200)
                  (ThetaLowerSegment.join cell1533526272 cell1533657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1533788416 cell1533919488)
                  (ThetaLowerSegment.join cell1534050560 cell1534181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1534312704 cell1534443776)
                  (ThetaLowerSegment.join cell1534574848 cell1534705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1534836992 cell1534968064)
                  (ThetaLowerSegment.join cell1535099136 cell1535230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1535361280 cell1535492352)
                  (ThetaLowerSegment.join cell1535623424 cell1535754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1535885568 cell1536016640)
                  (ThetaLowerSegment.join cell1536147712 cell1536278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1536409856 cell1536540928)
                  (ThetaLowerSegment.join cell1536672000 cell1536803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1536934144 cell1537065216)
                  (ThetaLowerSegment.join cell1537196288 cell1537327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1537458432 cell1537589504)
                  (ThetaLowerSegment.join cell1537720576 cell1537851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1537982720 cell1538113792)
                  (ThetaLowerSegment.join cell1538244864 cell1538375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1538507008 cell1538638080)
                  (ThetaLowerSegment.join cell1538769152 cell1538900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1539031296 cell1539162368)
                  (ThetaLowerSegment.join cell1539293440 cell1539424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1539555584 cell1539686656)
                  (ThetaLowerSegment.join cell1539817728 cell1539948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1540079872 cell1540210944)
                  (ThetaLowerSegment.join cell1540342016 cell1540473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1540604160 cell1540735232)
                  (ThetaLowerSegment.join cell1540866304 cell1540997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1541128448 cell1541259520)
                  (ThetaLowerSegment.join cell1541390592 cell1541521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1541652736 cell1541783808)
                  (ThetaLowerSegment.join cell1541914880 cell1542045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1542177024 cell1542308096)
                  (ThetaLowerSegment.join cell1542439168 cell1542570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1542701312 cell1542832384)
                  (ThetaLowerSegment.join cell1542963456 cell1543094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1543225600 cell1543356672)
                  (ThetaLowerSegment.join cell1543487744 cell1543618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1543749888 cell1543880960)
                  (ThetaLowerSegment.join cell1544012032 cell1544143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1544274176 cell1544405248)
                  (ThetaLowerSegment.join cell1544536320 cell1544667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1544798464 cell1544929536)
                (ThetaLowerSegment.join cell1545060608 cell1545191680))
              (ThetaLowerSegment.join cell1545322752 cell1545339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
