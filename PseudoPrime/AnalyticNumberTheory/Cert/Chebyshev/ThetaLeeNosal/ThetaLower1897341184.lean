/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1897341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1865341184 :
    ThetaLowerSegment 1865341184 1865472256 (186528645797453 / 100000)
      (93270885938567 / 50000) := by
  exact
    packedTile65536 1865341184 1865472256 14 6149 43189 31 _ _ (2134669 / 100000) (133417 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865472256 :
    ThetaLowerSegment 1865472256 1865603328 (93270885938567 / 50000) (37310955692819 / 20000) := by
  exact
    packedTile65536 1865472256 1865603328 14 6093 43191 31 _ _ (2134677 / 100000) (53367 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865603328 :
    ThetaLowerSegment 1865603328 1865734400 (37310955692819 / 20000)
      (186567772285603 / 100000) := by
  exact
    packedTile65536 1865603328 1865734400 14 6087 43192 31 _ _ (533671 / 25000) (2134687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865734400 :
    ThetaLowerSegment 1865734400 1865865472 (186567772285603 / 100000)
      (186580887827107 / 100000) := by
  exact
    packedTile65536 1865734400 1865865472 14 6144 43194 31 _ _ (2134691 / 100000) (1067347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865865472 :
    ThetaLowerSegment 1865865472 1865996544 (186580887827107 / 100000)
      (186593896676719 / 100000) := by
  exact
    packedTile65536 1865865472 1865996544 14 6094 43195 31 _ _ (1067349 / 50000) (2134701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865996544 :
    ThetaLowerSegment 1865996544 1866127616 (186593896676719 / 100000)
      (186606978148959 / 100000) := by
  exact
    packedTile65536 1865996544 1866127616 14 6128 43197 31 _ _ (426941 / 20000) (533677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866127616 :
    ThetaLowerSegment 1866127616 1866258688 (186606978148959 / 100000)
      (37324005528683 / 20000) := by
  exact
    packedTile65536 1866127616 1866258688 14 6113 43198 31 _ _ (266839 / 12500) (426943 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866258688 :
    ThetaLowerSegment 1866258688 1866389760 (37324005528683 / 20000)
      (186633066507067 / 100000) := by
  exact
    packedTile65536 1866258688 1866389760 14 6108 43200 31 _ _ (2134719 / 100000) (1067361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866389760 :
    ThetaLowerSegment 1866389760 1866520832 (186633066507067 / 100000)
      (186646312481897 / 100000) := by
  exact
    packedTile65536 1866389760 1866520832 14 6205 43201 31 _ _ (1067363 / 50000) (2134729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866520832 :
    ThetaLowerSegment 1866520832 1866651904 (186646312481897 / 100000)
      (93329787789013 / 50000) := by
  exact
    packedTile65536 1866520832 1866651904 14 6213 43203 31 _ _ (2134733 / 100000) (133421 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866651904 :
    ThetaLowerSegment 1866651904 1866782976 (93329787789013 / 50000) (93336404415643 / 50000) := by
  exact
    packedTile65536 1866651904 1866782976 14 6199 43204 31 _ _ (106737 / 5000) (2134743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866782976 :
    ThetaLowerSegment 1866782976 1866914048 (93336404415643 / 50000) (93342953819439 / 50000) := by
  exact
    packedTile65536 1866782976 1866914048 14 6136 43206 31 _ _ (2134747 / 100000) (8539 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1866914048 :
    ThetaLowerSegment 1866914048 1867045120 (93342953819439 / 50000) (3733979361277 / 2000) := by
  exact
    packedTile65536 1866914048 1867045120 14 6118 43207 31 _ _ (1067377 / 50000) (2134757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867045120 :
    ThetaLowerSegment 1867045120 1867176192 (3733979361277 / 2000) (93355999322497 / 50000) := by
  exact
    packedTile65536 1867045120 1867176192 14 6104 43209 31 _ _ (2134761 / 100000) (533691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867176192 :
    ThetaLowerSegment 1867176192 1867307264 (93355999322497 / 50000) (93362474073841 / 50000) := by
  exact
    packedTile65536 1867176192 1867307264 14 6066 43210 31 _ _ (133423 / 6250) (2134771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867307264 :
    ThetaLowerSegment 1867307264 1867438336 (93362474073841 / 50000) (93369010754891 / 50000) := by
  exact
    packedTile65536 1867307264 1867438336 14 6124 43212 31 _ _ (85391 / 4000) (1067389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867438336 :
    ThetaLowerSegment 1867438336 1867569408 (93369010754891 / 50000) (5835975918938 / 3125) := by
  exact
    packedTile65536 1867438336 1867569408 14 6187 43213 31 _ _ (1067391 / 50000) (426957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867569408 :
    ThetaLowerSegment 1867569408 1867700480 (5835975918938 / 3125) (5836383663637 / 3125) := by
  exact
    packedTile65536 1867569408 1867700480 14 6112 43215 31 _ _ (2134789 / 100000) (266849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867700480 :
    ThetaLowerSegment 1867700480 1867831552 (5836383663637 / 3125) (46694338215471 / 25000) := by
  exact
    packedTile65536 1867700480 1867831552 14 6125 43216 31 _ _ (533699 / 25000) (2134799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867831552 :
    ThetaLowerSegment 1867831552 1867962624 (46694338215471 / 25000) (93395198254107 / 50000) := by
  exact
    packedTile65536 1867831552 1867962624 14 6110 43218 31 _ _ (2134803 / 100000) (1067403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1867962624 :
    ThetaLowerSegment 1867962624 1868093696 (93395198254107 / 50000) (46700866987461 / 25000) := by
  exact
    packedTile65536 1867962624 1868093696 14 6123 43219 31 _ _ (213481 / 10000) (2134813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868093696 :
    ThetaLowerSegment 1868093696 1868224768 (46700866987461 / 25000) (93408302806831 / 50000) := by
  exact
    packedTile65536 1868093696 1868224768 14 6154 43221 31 _ _ (2134817 / 100000) (106741 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868224768 :
    ThetaLowerSegment 1868224768 1868355840 (93408302806831 / 50000) (93414818289679 / 50000) := by
  exact
    packedTile65536 1868224768 1868355840 14 6104 43222 31 _ _ (266853 / 12500) (2134827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868355840 :
    ThetaLowerSegment 1868355840 1868486912 (93414818289679 / 50000) (93421436265779 / 50000) := by
  exact
    packedTile65536 1868355840 1868486912 14 6200 43224 31 _ _ (2134831 / 100000) (1067417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868486912 :
    ThetaLowerSegment 1868486912 1868617984 (93421436265779 / 50000) (3737117217719 / 2000) := by
  exact
    packedTile65536 1868486912 1868617984 14 6084 43225 31 _ _ (1067419 / 50000) (2134841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868617984 :
    ThetaLowerSegment 1868617984 1868749056 (3737117217719 / 2000) (3737381084561 / 2000) := by
  exact
    packedTile65536 1868617984 1868749056 14 6180 43227 31 _ _ (426969 / 20000) (66714 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868749056 :
    ThetaLowerSegment 1868749056 1868880128 (3737381084561 / 2000) (18688225828767 / 10000) := by
  exact
    packedTile65536 1868749056 1868880128 14 6185 43229 31 _ _ (533713 / 25000) (426971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1868880128 :
    ThetaLowerSegment 1868880128 1869011200 (18688225828767 / 10000) (23361914919379 / 12500) := by
  exact
    packedTile65536 1868880128 1869011200 14 6118 43230 31 _ _ (2134859 / 100000) (1067431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869011200 :
    ThetaLowerSegment 1869011200 1869142272 (23361914919379 / 12500) (46727060958449 / 25000) := by
  exact
    packedTile65536 1869011200 1869142272 14 6054 43232 31 _ _ (1067433 / 50000) (2134869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869142272 :
    ThetaLowerSegment 1869142272 1869273344 (46727060958449 / 25000) (93460686651373 / 50000) := by
  exact
    packedTile65536 1869142272 1869273344 14 6150 43233 31 _ _ (2134873 / 100000) (533719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869273344 :
    ThetaLowerSegment 1869273344 1869404416 (93460686651373 / 50000) (93467268486413 / 50000) := by
  exact
    packedTile65536 1869273344 1869404416 14 6166 43235 31 _ _ (13343 / 625) (2134883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869404416 :
    ThetaLowerSegment 1869404416 1869535488 (93467268486413 / 50000) (93473767082441 / 50000) := by
  exact
    packedTile65536 1869404416 1869535488 14 6088 43236 31 _ _ (2134887 / 100000) (213489 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869535488 :
    ThetaLowerSegment 1869535488 1869666560 (93473767082441 / 50000) (93480404467887 / 50000) := by
  exact
    packedTile65536 1869535488 1869666560 14 6218 43238 31 _ _ (1067447 / 50000) (2134897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869666560 :
    ThetaLowerSegment 1869666560 1869797632 (93480404467887 / 50000) (93486962883759 / 50000) := by
  exact
    packedTile65536 1869666560 1869797632 14 6144 43239 31 _ _ (2134901 / 100000) (266863 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869797632 :
    ThetaLowerSegment 1869797632 1869928704 (93486962883759 / 50000) (93493497837147 / 50000) := by
  exact
    packedTile65536 1869797632 1869928704 14 6122 43241 31 _ _ (533727 / 25000) (2134911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1869928704 :
    ThetaLowerSegment 1869928704 1870059776 (93493497837147 / 50000) (93500124613307 / 50000) := by
  exact
    packedTile65536 1869928704 1870059776 14 6208 43242 31 _ _ (426983 / 20000) (1067459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870059776 :
    ThetaLowerSegment 1870059776 1870190848 (93500124613307 / 50000) (2337667317521 / 1250) := by
  exact
    packedTile65536 1870059776 1870190848 14 6153 43244 31 _ _ (1067461 / 50000) (85397 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870190848 :
    ThetaLowerSegment 1870190848 1870321920 (2337667317521 / 1250) (187026380714503 / 100000) := by
  exact
    packedTile65536 1870190848 1870321920 14 6087 43245 31 _ _ (2134929 / 100000) (533733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870321920 :
    ThetaLowerSegment 1870321920 1870452992 (187026380714503 / 100000)
      (187039358990447 / 100000) := by
  exact
    packedTile65536 1870321920 1870452992 14 6079 43247 31 _ _ (266867 / 12500) (2134939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870452992 :
    ThetaLowerSegment 1870452992 1870584064 (187039358990447 / 100000)
      (93526140900213 / 50000) := by
  exact
    packedTile65536 1870452992 1870584064 14 6053 43248 31 _ _ (2134943 / 100000) (1067473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870584064 :
    ThetaLowerSegment 1870584064 1870715136 (93526140900213 / 50000) (23383184740797 / 12500) := by
  exact
    packedTile65536 1870584064 1870715136 14 6181 43250 31 _ _ (42699 / 2000) (2134953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870715136 :
    ThetaLowerSegment 1870715136 1870846208 (23383184740797 / 12500) (37415733111153 / 20000) := by
  exact
    packedTile65536 1870715136 1870846208 14 6177 43251 31 _ _ (2134957 / 100000) (26687 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870846208 :
    ThetaLowerSegment 1870846208 1870977280 (37415733111153 / 20000) (37418382601477 / 20000) := by
  exact
    packedTile65536 1870846208 1870977280 14 6205 43253 31 _ _ (533741 / 25000) (2134967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870977280 :
    ThetaLowerSegment 1870977280 1871108352 (37418382601477 / 20000) (11694071463917 / 6250) := by
  exact
    packedTile65536 1870977280 1871108352 14 6197 43254 31 _ _ (2134971 / 100000) (1067487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871108352 :
    ThetaLowerSegment 1871108352 1871239424 (11694071463917 / 6250) (46779591869101 / 25000) := by
  exact
    packedTile65536 1871108352 1871239424 14 6194 43256 31 _ _ (1067489 / 50000) (2134981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871239424 :
    ThetaLowerSegment 1871239424 1871370496 (46779591869101 / 25000)
      (187131200871239 / 100000) := by
  exact
    packedTile65536 1871239424 1871370496 14 6011 43257 31 _ _ (426997 / 20000) (533747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871370496 :
    ThetaLowerSegment 1871370496 1871501568 (187131200871239 / 100000)
      (187144162407671 / 100000) := by
  exact
    packedTile65536 1871370496 1871501568 14 6071 43259 31 _ _ (133437 / 6250) (426999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871501568 :
    ThetaLowerSegment 1871501568 1871632640 (187144162407671 / 100000)
      (93578602558281 / 50000) := by
  exact
    packedTile65536 1871501568 1871632640 14 6109 43260 31 _ _ (2134999 / 100000) (1067501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871632640 :
    ThetaLowerSegment 1871632640 1871763712 (93578602558281 / 50000) (93585203996833 / 50000) := by
  exact
    packedTile65536 1871632640 1871763712 14 6184 43262 31 _ _ (1067503 / 50000) (2135009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871763712 :
    ThetaLowerSegment 1871763712 1871894784 (93585203996833 / 50000) (93591694436353 / 50000) := by
  exact
    packedTile65536 1871763712 1871894784 14 6080 43263 31 _ _ (2135013 / 100000) (266877 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1871894784 :
    ThetaLowerSegment 1871894784 1872025856 (93591694436353 / 50000) (93598302323253 / 50000) := by
  exact
    packedTile65536 1871894784 1872025856 14 6190 43265 31 _ _ (106751 / 5000) (2135023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872025856 :
    ThetaLowerSegment 1872025856 1872156928 (93598302323253 / 50000) (93604822695711 / 50000) := by
  exact
    packedTile65536 1872025856 1872156928 14 6108 43266 31 _ _ (2135027 / 100000) (213503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872156928 :
    ThetaLowerSegment 1872156928 1872288000 (93604822695711 / 50000) (93611308929003 / 50000) := by
  exact
    packedTile65536 1872156928 1872288000 14 6076 43268 31 _ _ (1067517 / 50000) (2135037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872288000 :
    ThetaLowerSegment 1872288000 1872419072 (93611308929003 / 50000) (23404476017663 / 12500) := by
  exact
    packedTile65536 1872288000 1872419072 14 6178 43269 31 _ _ (2135041 / 100000) (533761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872419072 :
    ThetaLowerSegment 1872419072 1872550144 (23404476017663 / 12500) (4681219303819 / 2500) := by
  exact
    packedTile65536 1872419072 1872550144 14 6072 43271 31 _ _ (266881 / 12500) (2135051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872550144 :
    ThetaLowerSegment 1872550144 1872681216 (4681219303819 / 2500) (37452376705103 / 20000) := by
  exact
    packedTile65536 1872550144 1872681216 14 6141 43272 31 _ _ (427011 / 20000) (1067529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872681216 :
    ThetaLowerSegment 1872681216 1872812288 (37452376705103 / 20000)
      (187275112369667 / 100000) := by
  exact
    packedTile65536 1872681216 1872812288 14 6196 43274 31 _ _ (1067531 / 50000) (427013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872812288 :
    ThetaLowerSegment 1872812288 1872943360 (187275112369667 / 100000)
      (187288405309261 / 100000) := by
  exact
    packedTile65536 1872812288 1872943360 14 6226 43276 31 _ _ (2135069 / 100000) (66721 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1872943360 :
    ThetaLowerSegment 1872943360 1873074432 (187288405309261 / 100000)
      (187301390841493 / 100000) := by
  exact
    packedTile65536 1872943360 1873074432 14 6082 43277 31 _ _ (533769 / 25000) (2135079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873074432 :
    ThetaLowerSegment 1873074432 1873205504 (187301390841493 / 100000) (4682859784047 / 2500) := by
  exact
    packedTile65536 1873074432 1873205504 14 6089 43279 31 _ _ (2135083 / 100000) (1067543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873205504 :
    ThetaLowerSegment 1873205504 1873336576 (4682859784047 / 2500) (18732762678479 / 10000) := by
  exact
    packedTile65536 1873205504 1873336576 14 6199 43280 31 _ _ (213509 / 10000) (2135093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873336576 :
    ThetaLowerSegment 1873336576 1873467648 (18732762678479 / 10000)
      (187340781117407 / 100000) := by
  exact
    packedTile65536 1873336576 1873467648 14 6161 43282 31 _ _ (2135097 / 100000) (21351 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873467648 :
    ThetaLowerSegment 1873467648 1873598720 (187340781117407 / 100000)
      (187353877845343 / 100000) := by
  exact
    packedTile65536 1873467648 1873598720 14 6134 43283 31 _ _ (66722 / 3125) (2135107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873598720 :
    ThetaLowerSegment 1873598720 1873729792 (187353877845343 / 100000) (11710438182069 / 6250) := by
  exact
    packedTile65536 1873598720 1873729792 14 6151 43285 31 _ _ (2135111 / 100000) (1067557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873729792 :
    ThetaLowerSegment 1873729792 1873860864 (11710438182069 / 6250) (3747604844787 / 2000) := by
  exact
    packedTile65536 1873729792 1873860864 14 6197 43286 31 _ _ (1067559 / 50000) (2135121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873860864 :
    ThetaLowerSegment 1873860864 1873991936 (3747604844787 / 2000) (7495734161679 / 4000) := by
  exact
    packedTile65536 1873860864 1873991936 14 6141 43288 31 _ _ (17081 / 800) (266891 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1873991936 :
    ThetaLowerSegment 1873991936 1874123008 (7495734161679 / 4000) (187406476563247 / 100000) := by
  exact
    packedTile65536 1873991936 1874123008 14 6146 43289 31 _ _ (533783 / 25000) (427027 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874123008 :
    ThetaLowerSegment 1874123008 1874254080 (187406476563247 / 100000) (9370986468551 / 5000) := by
  exact
    packedTile65536 1874123008 1874254080 14 6207 43291 31 _ _ (2135139 / 100000) (1067571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874254080 :
    ThetaLowerSegment 1874254080 1874385152 (9370986468551 / 5000) (93716397164697 / 50000) := by
  exact
    packedTile65536 1874254080 1874385152 14 6119 43292 31 _ _ (1067573 / 50000) (2135149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874385152 :
    ThetaLowerSegment 1874385152 1874516224 (93716397164697 / 50000) (37489141119917 / 20000) := by
  exact
    packedTile65536 1874385152 1874516224 14 6047 43294 31 _ _ (2135153 / 100000) (533789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874516224 :
    ThetaLowerSegment 1874516224 1874647296 (37489141119917 / 20000) (37491773772197 / 20000) := by
  exact
    packedTile65536 1874516224 1874647296 14 6165 43295 31 _ _ (53379 / 2500) (2135163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874647296 :
    ThetaLowerSegment 1874647296 1874778368 (37491773772197 / 20000) (5858499136902 / 3125) := by
  exact
    packedTile65536 1874647296 1874778368 14 6137 43297 31 _ _ (2135167 / 100000) (213517 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874778368 :
    ThetaLowerSegment 1874778368 1874909440 (5858499136902 / 3125) (46871303682503 / 25000) := by
  exact
    packedTile65536 1874778368 1874909440 14 6202 43298 31 _ _ (1067587 / 50000) (2135177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874909440 :
    ThetaLowerSegment 1874909440 1875040512 (46871303682503 / 25000) (23437290592669 / 12500) := by
  exact
    packedTile65536 1874909440 1875040512 14 6140 43300 31 _ _ (2135181 / 100000) (133449 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875040512 :
    ThetaLowerSegment 1875040512 1875171584 (23437290592669 / 12500) (5859729268032 / 3125) := by
  exact
    packedTile65536 1875040512 1875171584 14 6094 43301 31 _ _ (533797 / 25000) (2135191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875171584 :
    ThetaLowerSegment 1875171584 1875302656 (5859729268032 / 3125) (5860137090277 / 3125) := by
  exact
    packedTile65536 1875171584 1875302656 14 6112 43303 31 _ _ (427039 / 20000) (1067599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875302656 :
    ThetaLowerSegment 1875302656 1875433728 (5860137090277 / 3125) (93768764528587 / 50000) := by
  exact
    packedTile65536 1875302656 1875433728 14 6155 43304 31 _ _ (1067601 / 50000) (427041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875433728 :
    ThetaLowerSegment 1875433728 1875564800 (93768764528587 / 50000) (7502025484209 / 4000) := by
  exact
    packedTile65536 1875433728 1875564800 14 6139 43306 31 _ _ (2135209 / 100000) (533803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875564800 :
    ThetaLowerSegment 1875564800 1875695872 (7502025484209 / 4000) (187563589325481 / 100000) := by
  exact
    packedTile65536 1875564800 1875695872 14 6066 43307 31 _ _ (133451 / 6250) (2135219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875695872 :
    ThetaLowerSegment 1875695872 1875826944 (187563589325481 / 100000)
      (187576639808457 / 100000) := by
  exact
    packedTile65536 1875695872 1875826944 14 6112 43309 31 _ _ (2135223 / 100000) (1067613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875826944 :
    ThetaLowerSegment 1875826944 1875958016 (187576639808457 / 100000)
      (187589626277317 / 100000) := by
  exact
    packedTile65536 1875826944 1875958016 14 6082 43310 31 _ _ (213523 / 10000) (2135233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1875958016 :
    ThetaLowerSegment 1875958016 1876089088 (187589626277317 / 100000)
      (23450362096909 / 12500) := by
  exact
    packedTile65536 1875958016 1876089088 14 6215 43312 31 _ _ (2135237 / 100000) (53381 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876089088 :
    ThetaLowerSegment 1876089088 1876220160 (23450362096909 / 12500) (5862997955473 / 3125) := by
  exact
    packedTile65536 1876089088 1876220160 14 6106 43313 31 _ _ (533811 / 25000) (2135247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876220160 :
    ThetaLowerSegment 1876220160 1876351232 (5862997955473 / 3125) (1172681584733 / 625) := by
  exact
    packedTile65536 1876220160 1876351232 14 6144 43315 31 _ _ (2135251 / 100000) (1067627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876351232 :
    ThetaLowerSegment 1876351232 1876482304 (1172681584733 / 625) (93821155687101 / 50000) := by
  exact
    packedTile65536 1876351232 1876482304 14 6209 43316 31 _ _ (1067629 / 50000) (2135261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876482304 :
    ThetaLowerSegment 1876482304 1876613376 (93821155687101 / 50000) (93827796361251 / 50000) := by
  exact
    packedTile65536 1876482304 1876613376 14 6220 43318 31 _ _ (427053 / 20000) (533817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876613376 :
    ThetaLowerSegment 1876613376 1876744448 (93827796361251 / 50000) (93834304670307 / 50000) := by
  exact
    packedTile65536 1876613376 1876744448 14 6096 43319 31 _ _ (266909 / 12500) (85411 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876744448 :
    ThetaLowerSegment 1876744448 1876875520 (93834304670307 / 50000) (11730110966933 / 6250) := by
  exact
    packedTile65536 1876744448 1876875520 14 6166 43321 31 _ _ (2135279 / 100000) (1067641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1876875520 :
    ThetaLowerSegment 1876875520 1877006592 (11730110966933 / 6250) (46923675623093 / 25000) := by
  exact
    packedTile65536 1876875520 1877006592 14 6054 43322 31 _ _ (1067643 / 50000) (2135289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877006592 :
    ThetaLowerSegment 1877006592 1877137664 (46923675623093 / 25000) (938539663839 / 500) := by
  exact
    packedTile65536 1877006592 1877137664 14 6196 43324 31 _ _ (2135293 / 100000) (66728 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877137664 :
    ThetaLowerSegment 1877137664 1877268736 (938539663839 / 500) (1877210029391 / 1000) := by
  exact
    packedTile65536 1877137664 1877268736 14 6121 43325 31 _ _ (21353 / 1000) (2135303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877268736 :
    ThetaLowerSegment 1877268736 1877399808 (1877210029391 / 1000) (187734367825613 / 100000) := by
  exact
    packedTile65536 1877268736 1877399808 14 6259 43327 31 _ _ (2135307 / 100000) (213531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877399808 :
    ThetaLowerSegment 1877399808 1877530880 (187734367825613 / 100000)
      (187747361211303 / 100000) := by
  exact
    packedTile65536 1877399808 1877530880 14 6085 43328 31 _ _ (1067657 / 50000) (2135317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877530880 :
    ThetaLowerSegment 1877530880 1877661952 (187747361211303 / 100000)
      (187760399481329 / 100000) := by
  exact
    packedTile65536 1877530880 1877661952 14 6106 43330 31 _ _ (2135321 / 100000) (533831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877661952 :
    ThetaLowerSegment 1877661952 1877793024 (187760399481329 / 100000)
      (187773467688689 / 100000) := by
  exact
    packedTile65536 1877661952 1877793024 14 6120 43331 31 _ _ (66729 / 3125) (2135331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877793024 :
    ThetaLowerSegment 1877793024 1877924096 (187773467688689 / 100000)
      (93893258360437 / 50000) := by
  exact
    packedTile65536 1877793024 1877924096 14 6111 43333 31 _ _ (427067 / 20000) (1067669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1877924096 :
    ThetaLowerSegment 1877924096 1878055168 (93893258360437 / 50000) (46949932020457 / 25000) := by
  exact
    packedTile65536 1877924096 1878055168 14 6187 43335 31 _ _ (1067671 / 50000) (427069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878055168 :
    ThetaLowerSegment 1878055168 1878186240 (46949932020457 / 25000) (46953233270011 / 25000) := by
  exact
    packedTile65536 1878055168 1878186240 14 6184 43336 31 _ _ (2135349 / 100000) (266919 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878186240 :
    ThetaLowerSegment 1878186240 1878317312 (46953233270011 / 25000) (23478244043197 / 12500) := by
  exact
    packedTile65536 1878186240 1878317312 14 6097 43338 31 _ _ (533839 / 25000) (2135359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878317312 :
    ThetaLowerSegment 1878317312 1878448384 (23478244043197 / 12500) (93919512518931 / 50000) := by
  exact
    packedTile65536 1878317312 1878448384 14 6122 43339 31 _ _ (2135363 / 100000) (1067683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878448384 :
    ThetaLowerSegment 1878448384 1878579456 (93919512518931 / 50000) (93926157790371 / 50000) := by
  exact
    packedTile65536 1878448384 1878579456 14 6224 43341 31 _ _ (213537 / 10000) (2135373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878579456 :
    ThetaLowerSegment 1878579456 1878710528 (93926157790371 / 50000)
      (187865377681851 / 100000) := by
  exact
    packedTile65536 1878579456 1878710528 14 6117 43342 31 _ _ (2135377 / 100000) (106769 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878710528 :
    ThetaLowerSegment 1878710528 1878841600 (187865377681851 / 100000)
      (37575681131927 / 20000) := by
  exact
    packedTile65536 1878710528 1878841600 14 6101 43344 31 _ _ (266923 / 12500) (2135387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878841600 :
    ThetaLowerSegment 1878841600 1878972672 (37575681131927 / 20000) (93945797984921 / 50000) := by
  exact
    packedTile65536 1878841600 1878972672 14 6177 43345 31 _ _ (2135391 / 100000) (1067697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1878972672 :
    ThetaLowerSegment 1878972672 1879103744 (93945797984921 / 50000) (18790489095779 / 10000) := by
  exact
    packedTile65536 1878972672 1879103744 14 6226 43347 31 _ _ (1067699 / 50000) (2135401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879103744 :
    ThetaLowerSegment 1879103744 1879234816 (18790489095779 / 10000) (3758360559387 / 2000) := by
  exact
    packedTile65536 1879103744 1879234816 14 6152 43348 31 _ _ (427081 / 20000) (133463 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879234816 :
    ThetaLowerSegment 1879234816 1879365888 (3758360559387 / 2000) (93965493892389 / 50000) := by
  exact
    packedTile65536 1879234816 1879365888 14 6069 43350 31 _ _ (533853 / 25000) (427083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879365888 :
    ThetaLowerSegment 1879365888 1879496960 (93965493892389 / 50000)
      (187944250872187 / 100000) := by
  exact
    packedTile65536 1879365888 1879496960 14 6211 43351 31 _ _ (2135419 / 100000) (1067711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879496960 :
    ThetaLowerSegment 1879496960 1879628032 (187944250872187 / 100000)
      (187957210772581 / 100000) := by
  exact
    packedTile65536 1879496960 1879628032 14 6069 43353 31 _ _ (1067713 / 50000) (2135429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879628032 :
    ThetaLowerSegment 1879628032 1879759104 (187957210772581 / 100000)
      (187970174980253 / 100000) := by
  exact
    packedTile65536 1879628032 1879759104 14 6071 43354 31 _ _ (266929 / 12500) (427087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879759104 :
    ThetaLowerSegment 1879759104 1879890176 (187970174980253 / 100000)
      (37596647919211 / 20000) := by
  exact
    packedTile65536 1879759104 1879890176 14 6118 43356 31 _ _ (2135439 / 100000) (1067721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1879890176 :
    ThetaLowerSegment 1879890176 1880021248 (37596647919211 / 20000)
      (187996357640833 / 100000) := by
  exact
    packedTile65536 1879890176 1880021248 14 6143 43357 31 _ _ (1067723 / 50000) (2135449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880021248 :
    ThetaLowerSegment 1880021248 1880152320 (187996357640833 / 100000)
      (37601865676471 / 20000) := by
  exact
    packedTile65536 1880021248 1880152320 14 6074 43359 31 _ _ (2135453 / 100000) (66733 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880152320 :
    ThetaLowerSegment 1880152320 1880283392 (37601865676471 / 20000) (1504180323787 / 800) := by
  exact
    packedTile65536 1880152320 1880283392 14 6187 43360 31 _ _ (106773 / 5000) (2135463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880283392 :
    ThetaLowerSegment 1880283392 1880414464 (1504180323787 / 800) (188035622344217 / 100000) := by
  exact
    packedTile65536 1880283392 1880414464 14 6126 43362 31 _ _ (2135467 / 100000) (213547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880414464 :
    ThetaLowerSegment 1880414464 1880545536 (188035622344217 / 100000)
      (188048691445097 / 100000) := by
  exact
    packedTile65536 1880414464 1880545536 14 6120 43363 31 _ _ (1067737 / 50000) (2135477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880545536 :
    ThetaLowerSegment 1880545536 1880676608 (188048691445097 / 100000) (235077048583 / 125) := by
  exact
    packedTile65536 1880545536 1880676608 14 6063 43365 31 _ _ (2135481 / 100000) (533871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880676608 :
    ThetaLowerSegment 1880676608 1880807680 (235077048583 / 125) (5877334359719 / 3125) := by
  exact
    packedTile65536 1880676608 1880807680 14 6116 43366 31 _ _ (66734 / 3125) (2135491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880807680 :
    ThetaLowerSegment 1880807680 1880938752 (5877334359719 / 3125) (188087749520953 / 100000) := by
  exact
    packedTile65536 1880807680 1880938752 14 6111 43368 31 _ _ (427099 / 20000) (1067749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1880938752 :
    ThetaLowerSegment 1880938752 1881069824 (188087749520953 / 100000)
      (188101043020903 / 100000) := by
  exact
    packedTile65536 1880938752 1881069824 14 6225 43369 31 _ _ (1067751 / 50000) (427101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881069824 :
    ThetaLowerSegment 1881069824 1881200896 (188101043020903 / 100000)
      (188114240466523 / 100000) := by
  exact
    packedTile65536 1881069824 1881200896 14 6180 43371 31 _ _ (2135509 / 100000) (266939 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881200896 :
    ThetaLowerSegment 1881200896 1881331968 (188114240466523 / 100000)
      (188127448632983 / 100000) := by
  exact
    packedTile65536 1881200896 1881331968 14 6185 43372 31 _ _ (533879 / 25000) (2135519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881331968 :
    ThetaLowerSegment 1881331968 1881463040 (188127448632983 / 100000) (3762806474023 / 2000) := by
  exact
    packedTile65536 1881331968 1881463040 14 6029 43374 31 _ _ (2135523 / 100000) (1067763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881463040 :
    ThetaLowerSegment 1881463040 1881594112 (3762806474023 / 2000) (752613572579 / 400) := by
  exact
    packedTile65536 1881463040 1881594112 14 6120 43375 31 _ _ (213553 / 10000) (2135533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881594112 :
    ThetaLowerSegment 1881594112 1881725184 (752613572579 / 400) (188166332363433 / 100000) := by
  exact
    packedTile65536 1881594112 1881725184 14 6059 43377 31 _ _ (2135537 / 100000) (106777 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881725184 :
    ThetaLowerSegment 1881725184 1881856256 (188166332363433 / 100000)
      (37635894473133 / 20000) := by
  exact
    packedTile65536 1881725184 1881856256 14 6153 43378 31 _ _ (266943 / 12500) (2135547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881856256 :
    ThetaLowerSegment 1881856256 1881987328 (37635894473133 / 20000) (94096321154341 / 50000) := by
  exact
    packedTile65536 1881856256 1881987328 14 6167 43380 31 _ _ (2135551 / 100000) (1067777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1881987328 :
    ThetaLowerSegment 1881987328 1882118400 (94096321154341 / 50000) (47051425311463 / 25000) := by
  exact
    packedTile65536 1881987328 1882118400 14 6115 43381 31 _ _ (1067779 / 50000) (2135561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882118400 :
    ThetaLowerSegment 1882118400 1882249472 (47051425311463 / 25000) (94109319249311 / 50000) := by
  exact
    packedTile65536 1882118400 1882249472 14 6058 43383 31 _ _ (427113 / 20000) (133473 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882249472 :
    ThetaLowerSegment 1882249472 1882380544 (94109319249311 / 50000) (94115857302989 / 50000) := by
  exact
    packedTile65536 1882249472 1882380544 14 6123 43384 31 _ _ (533893 / 25000) (85423 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882380544 :
    ThetaLowerSegment 1882380544 1882511616 (94115857302989 / 50000) (47061190748417 / 25000) := by
  exact
    packedTile65536 1882380544 1882511616 14 6110 43386 31 _ _ (2135579 / 100000) (1067791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882511616 :
    ThetaLowerSegment 1882511616 1882642688 (47061190748417 / 25000) (47064458194997 / 25000) := by
  exact
    packedTile65536 1882511616 1882642688 14 6120 43387 31 _ _ (1067793 / 50000) (2135589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882642688 :
    ThetaLowerSegment 1882642688 1882773760 (47064458194997 / 25000)
      (188271020066763 / 100000) := by
  exact
    packedTile65536 1882642688 1882773760 14 6175 43389 31 _ _ (2135593 / 100000) (533899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882773760 :
    ThetaLowerSegment 1882773760 1882904832 (188271020066763 / 100000)
      (188284096345563 / 100000) := by
  exact
    packedTile65536 1882773760 1882904832 14 6123 43390 31 _ _ (5339 / 250) (2135603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882904832 :
    ThetaLowerSegment 1882904832 1883035904 (188284096345563 / 100000)
      (47074316658483 / 25000) := by
  exact
    packedTile65536 1882904832 1883035904 14 6167 43392 31 _ _ (2135607 / 100000) (213561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883035904 :
    ThetaLowerSegment 1883035904 1883166976 (47074316658483 / 25000) (94155288957997 / 50000) := by
  exact
    packedTile65536 1883035904 1883166976 14 6233 43393 31 _ _ (1067807 / 50000) (2135617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883166976 :
    ThetaLowerSegment 1883166976 1883298048 (94155288957997 / 50000)
      (188323867885477 / 100000) := by
  exact
    packedTile65536 1883166976 1883298048 14 6223 43395 31 _ _ (2135621 / 100000) (266953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883298048 :
    ThetaLowerSegment 1883298048 1883429120 (188323867885477 / 100000)
      (188336867453113 / 100000) := by
  exact
    packedTile65536 1883298048 1883429120 14 6087 43396 31 _ _ (533907 / 25000) (2135631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883429120 :
    ThetaLowerSegment 1883429120 1883560192 (188336867453113 / 100000)
      (188349852107833 / 100000) := by
  exact
    packedTile65536 1883429120 1883560192 14 6080 43398 31 _ _ (1067817 / 50000) (2135637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883560192 :
    ThetaLowerSegment 1883560192 1883691264 (188349852107833 / 100000) (11772679302483 / 6250) := by
  exact
    packedTile65536 1883560192 1883691264 14 6095 43400 31 _ _ (2135641 / 100000) (533911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883691264 :
    ThetaLowerSegment 1883691264 1883822336 (11772679302483 / 6250) (11773490982201 / 6250) := by
  exact
    packedTile65536 1883691264 1883822336 14 6081 43401 31 _ _ (66739 / 3125) (2135651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883822336 :
    ThetaLowerSegment 1883822336 1883953408 (11773490982201 / 6250) (94194563337693 / 50000) := by
  exact
    packedTile65536 1883822336 1883953408 14 6214 43403 31 _ _ (427131 / 20000) (1067829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1883953408 :
    ThetaLowerSegment 1883953408 1884084480 (94194563337693 / 50000) (4710051559503 / 2500) := by
  exact
    packedTile65536 1883953408 1884084480 14 6057 43404 31 _ _ (1067831 / 50000) (427133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884084480 :
    ThetaLowerSegment 1884084480 1884215552 (4710051559503 / 2500) (188415275764223 / 100000) := by
  exact
    packedTile65536 1884084480 1884215552 14 6187 43406 31 _ _ (2135669 / 100000) (266959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884215552 :
    ThetaLowerSegment 1884215552 1884346624 (188415275764223 / 100000)
      (188428282031063 / 100000) := by
  exact
    packedTile65536 1884215552 1884346624 14 6090 43407 31 _ _ (533919 / 25000) (2135679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884346624 :
    ThetaLowerSegment 1884346624 1884477696 (188428282031063 / 100000)
      (94220604660131 / 50000) := by
  exact
    packedTile65536 1884346624 1884477696 14 6053 43409 31 _ _ (2135683 / 100000) (1067843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884477696 :
    ThetaLowerSegment 1884477696 1884608768 (94220604660131 / 50000) (94227088614971 / 50000) := by
  exact
    packedTile65536 1884477696 1884608768 14 6072 43410 31 _ _ (213569 / 10000) (2135693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884608768 :
    ThetaLowerSegment 1884608768 1884739840 (94227088614971 / 50000)
      (188467198574551 / 100000) := by
  exact
    packedTile65536 1884608768 1884739840 14 6097 43412 31 _ _ (2135697 / 100000) (21357 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884739840 :
    ThetaLowerSegment 1884739840 1884870912 (188467198574551 / 100000)
      (188480382275343 / 100000) := by
  exact
    packedTile65536 1884739840 1884870912 14 6173 43413 31 _ _ (266963 / 12500) (2135707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1884870912 :
    ThetaLowerSegment 1884870912 1885001984 (188480382275343 / 100000)
      (37698721319571 / 20000) := by
  exact
    packedTile65536 1884870912 1885001984 14 6192 43415 31 _ _ (2135711 / 100000) (1067857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885001984 :
    ThetaLowerSegment 1885001984 1885133056 (37698721319571 / 20000)
      (188506657970553 / 100000) := by
  exact
    packedTile65536 1885001984 1885133056 14 6111 43416 31 _ _ (1067859 / 50000) (2135721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885133056 :
    ThetaLowerSegment 1885133056 1885264128 (188506657970553 / 100000)
      (188519848208153 / 100000) := by
  exact
    packedTile65536 1885133056 1885264128 14 6176 43418 31 _ _ (85429 / 4000) (133483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885264128 :
    ThetaLowerSegment 1885264128 1885395200 (188519848208153 / 100000)
      (188532882580549 / 100000) := by
  exact
    packedTile65536 1885264128 1885395200 14 6103 43419 31 _ _ (533933 / 25000) (427147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885395200 :
    ThetaLowerSegment 1885395200 1885526272 (188532882580549 / 100000)
      (188545966117663 / 100000) := by
  exact
    packedTile65536 1885395200 1885526272 14 6126 43421 31 _ _ (2135739 / 100000) (1067871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885526272 :
    ThetaLowerSegment 1885526272 1885657344 (188545966117663 / 100000)
      (188559143670483 / 100000) := by
  exact
    packedTile65536 1885526272 1885657344 14 6170 43422 31 _ _ (1067873 / 50000) (2135749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885657344 :
    ThetaLowerSegment 1885657344 1885788416 (188559143670483 / 100000) (3771445101163 / 2000) := by
  exact
    packedTile65536 1885657344 1885788416 14 6139 43424 31 _ _ (2135753 / 100000) (533939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885788416 :
    ThetaLowerSegment 1885788416 1885919488 (3771445101163 / 2000) (18858528532991 / 10000) := by
  exact
    packedTile65536 1885788416 1885919488 14 6101 43425 31 _ _ (26697 / 1250) (2135763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1885919488 :
    ThetaLowerSegment 1885919488 1886050560 (18858528532991 / 10000) (23574783315217 / 12500) := by
  exact
    packedTile65536 1885919488 1886050560 14 6078 43427 31 _ _ (2135767 / 100000) (213577 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886050560 :
    ThetaLowerSegment 1886050560 1886181632 (23574783315217 / 12500) (94305718919997 / 50000) := by
  exact
    packedTile65536 1886050560 1886181632 14 6167 43428 31 _ _ (1067887 / 50000) (2135777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886181632 :
    ThetaLowerSegment 1886181632 1886312704 (94305718919997 / 50000) (23578084426329 / 12500) := by
  exact
    packedTile65536 1886181632 1886312704 14 6198 43430 31 _ _ (2135781 / 100000) (266973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886312704 :
    ThetaLowerSegment 1886312704 1886443776 (23578084426329 / 12500)
      (188637603329343 / 100000) := by
  exact
    packedTile65536 1886312704 1886443776 14 6053 43431 31 _ _ (2135787 / 100000) (213579 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886443776 :
    ThetaLowerSegment 1886443776 1886574848 (188637603329343 / 100000)
      (188650544105189 / 100000) := by
  exact
    packedTile65536 1886443776 1886574848 14 6059 43433 31 _ _ (1067897 / 50000) (2135797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886574848 :
    ThetaLowerSegment 1886574848 1886705920 (188650544105189 / 100000)
      (18866361734311 / 10000) := by
  exact
    packedTile65536 1886574848 1886705920 14 6121 43434 31 _ _ (2135801 / 100000) (533951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886705920 :
    ThetaLowerSegment 1886705920 1886836992 (18866361734311 / 10000) (18867677392039 / 10000) := by
  exact
    packedTile65536 1886705920 1886836992 14 6160 43436 31 _ _ (66744 / 3125) (2135811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886836992 :
    ThetaLowerSegment 1886836992 1886968064 (18867677392039 / 10000) (37738001058863 / 20000) := by
  exact
    packedTile65536 1886836992 1886968064 14 6195 43437 31 _ _ (427163 / 20000) (1067909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886968064 :
    ThetaLowerSegment 1886968064 1887099136 (37738001058863 / 20000)
      (188703125648861 / 100000) := by
  exact
    packedTile65536 1886968064 1887099136 14 6143 43439 31 _ _ (1067911 / 50000) (85433 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887099136 :
    ThetaLowerSegment 1887099136 1887230208 (188703125648861 / 100000)
      (94358129430691 / 50000) := by
  exact
    packedTile65536 1887099136 1887230208 14 6149 43440 31 _ _ (2135829 / 100000) (266979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887230208 :
    ThetaLowerSegment 1887230208 1887361280 (94358129430691 / 50000) (18872927251013 / 10000) := by
  exact
    packedTile65536 1887230208 1887361280 14 6093 43442 31 _ _ (533959 / 25000) (2135839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887361280 :
    ThetaLowerSegment 1887361280 1887492352 (18872927251013 / 10000) (23592804196837 / 12500) := by
  exact
    packedTile65536 1887361280 1887492352 14 6162 43443 31 _ _ (2135843 / 100000) (1067923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887492352 :
    ThetaLowerSegment 1887492352 1887623424 (23592804196837 / 12500) (94377745012873 / 50000) := by
  exact
    packedTile65536 1887492352 1887623424 14 6113 43445 31 _ _ (42717 / 2000) (2135853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887623424 :
    ThetaLowerSegment 1887623424 1887754496 (94377745012873 / 50000)
      (188768674671007 / 100000) := by
  exact
    packedTile65536 1887623424 1887754496 14 6173 43446 31 _ _ (2135857 / 100000) (106793 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887754496 :
    ThetaLowerSegment 1887754496 1887885568 (188768674671007 / 100000)
      (37756328727443 / 20000) := by
  exact
    packedTile65536 1887754496 1887885568 14 6072 43448 31 _ _ (266983 / 12500) (2135867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1887885568 :
    ThetaLowerSegment 1887885568 1888016640 (37756328727443 / 20000) (47198714567773 / 25000) := by
  exact
    packedTile65536 1887885568 1888016640 14 6187 43449 31 _ _ (2135871 / 100000) (1067937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888016640 :
    ThetaLowerSegment 1888016640 1888147712 (47198714567773 / 25000) (94404012979481 / 50000) := by
  exact
    packedTile65536 1888016640 1888147712 14 6165 43451 31 _ _ (1067939 / 50000) (2135881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888147712 :
    ThetaLowerSegment 1888147712 1888278784 (94404012979481 / 50000) (47205352353593 / 25000) := by
  exact
    packedTile65536 1888147712 1888278784 14 6266 43452 31 _ _ (427177 / 20000) (133493 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888278784 :
    ThetaLowerSegment 1888278784 1888409856 (47205352353593 / 25000) (23604325352407 / 12500) := by
  exact
    packedTile65536 1888278784 1888409856 14 6177 43454 31 _ _ (533973 / 25000) (427179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888409856 :
    ThetaLowerSegment 1888409856 1888540928 (23604325352407 / 12500) (94423839396467 / 50000) := by
  exact
    packedTile65536 1888409856 1888540928 14 6122 43455 31 _ _ (2135899 / 100000) (1067951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888540928 :
    ThetaLowerSegment 1888540928 1888672000 (94423839396467 / 50000) (23607609035537 / 12500) := by
  exact
    packedTile65536 1888540928 1888672000 14 6177 43457 31 _ _ (1067953 / 50000) (2135909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888672000 :
    ThetaLowerSegment 1888672000 1888803072 (23607609035537 / 12500) (23609252619821 / 12500) := by
  exact
    packedTile65536 1888672000 1888803072 14 6156 43458 31 _ _ (266989 / 12500) (427183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888803072 :
    ThetaLowerSegment 1888803072 1888934144 (23609252619821 / 12500)
      (188887235889421 / 100000) := by
  exact
    packedTile65536 1888803072 1888934144 14 6187 43460 31 _ _ (2135919 / 100000) (1067961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1888934144 :
    ThetaLowerSegment 1888934144 1889065216 (188887235889421 / 100000)
      (188900361154691 / 100000) := by
  exact
    packedTile65536 1888934144 1889065216 14 6145 43461 31 _ _ (1067963 / 50000) (2135929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889065216 :
    ThetaLowerSegment 1889065216 1889196288 (188900361154691 / 100000)
      (188913574036229 / 100000) := by
  exact
    packedTile65536 1889065216 1889196288 14 6186 43463 31 _ _ (2135933 / 100000) (66748 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889196288 :
    ThetaLowerSegment 1889196288 1889327360 (188913574036229 / 100000)
      (188926701523469 / 100000) := by
  exact
    packedTile65536 1889196288 1889327360 14 6146 43464 31 _ _ (106797 / 5000) (2135943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889327360 :
    ThetaLowerSegment 1889327360 1889458432 (188926701523469 / 100000)
      (188939773519109 / 100000) := by
  exact
    packedTile65536 1889327360 1889458432 14 6120 43466 31 _ _ (2135947 / 100000) (42719 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889458432 :
    ThetaLowerSegment 1889458432 1889589504 (188939773519109 / 100000)
      (188952933131703 / 100000) := by
  exact
    packedTile65536 1889458432 1889589504 14 6161 43467 31 _ _ (1067977 / 50000) (2135957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889589504 :
    ThetaLowerSegment 1889589504 1889720576 (188952933131703 / 100000)
      (47241508245129 / 25000) := by
  exact
    packedTile65536 1889589504 1889720576 14 6133 43469 31 _ _ (2135961 / 100000) (533991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889720576 :
    ThetaLowerSegment 1889720576 1889851648 (47241508245129 / 25000) (47244797101857 / 25000) := by
  exact
    packedTile65536 1889720576 1889851648 14 6159 43470 31 _ _ (66749 / 3125) (2135971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889851648 :
    ThetaLowerSegment 1889851648 1889982720 (47244797101857 / 25000) (94496115335389 / 50000) := by
  exact
    packedTile65536 1889851648 1889982720 14 6106 43472 31 _ _ (85439 / 4000) (1067989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1889982720 :
    ThetaLowerSegment 1889982720 1890113792 (94496115335389 / 50000) (23625667399039 / 12500) := by
  exact
    packedTile65536 1889982720 1890113792 14 6137 43473 31 _ _ (1067991 / 50000) (427197 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890113792 :
    ThetaLowerSegment 1890113792 1890244864 (23625667399039 / 12500) (11813657123279 / 6250) := by
  exact
    packedTile65536 1890113792 1890244864 14 6168 43475 31 _ _ (2135989 / 100000) (266999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890244864 :
    ThetaLowerSegment 1890244864 1890375936 (11813657123279 / 6250) (47257888557011 / 25000) := by
  exact
    packedTile65536 1890244864 1890375936 14 6105 43476 31 _ _ (533999 / 25000) (2135999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890375936 :
    ThetaLowerSegment 1890375936 1890507008 (47257888557011 / 25000) (94522268427139 / 50000) := by
  exact
    packedTile65536 1890375936 1890507008 14 6078 43478 31 _ _ (2136003 / 100000) (1068003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890507008 :
    ThetaLowerSegment 1890507008 1890638080 (94522268427139 / 50000) (94528806753749 / 50000) := by
  exact
    packedTile65536 1890507008 1890638080 14 6122 43479 31 _ _ (213601 / 10000) (2136013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890638080 :
    ThetaLowerSegment 1890638080 1890769152 (94528806753749 / 50000) (94535407046279 / 50000) := by
  exact
    packedTile65536 1890638080 1890769152 14 6180 43481 31 _ _ (2136017 / 100000) (106801 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890769152 :
    ThetaLowerSegment 1890769152 1890900224 (94535407046279 / 50000) (18908393781787 / 10000) := by
  exact
    packedTile65536 1890769152 1890900224 14 6144 43482 31 _ _ (2136023 / 100000) (1068013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890900224 :
    ThetaLowerSegment 1890900224 1891031296 (18908393781787 / 10000) (3781937472311 / 2000) := by
  exact
    packedTile65536 1890900224 1891031296 14 6056 43484 31 _ _ (213603 / 10000) (2136033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891031296 :
    ThetaLowerSegment 1891031296 1891162368 (3781937472311 / 2000) (189109965386323 / 100000) := by
  exact
    packedTile65536 1891031296 1891162368 14 6129 43485 31 _ _ (2136037 / 100000) (53401 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891162368 :
    ThetaLowerSegment 1891162368 1891293440 (189109965386323 / 100000)
      (189123091376703 / 100000) := by
  exact
    packedTile65536 1891162368 1891293440 14 6145 43487 31 _ _ (534011 / 25000) (2136047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891293440 :
    ThetaLowerSegment 1891293440 1891424512 (189123091376703 / 100000)
      (189136185369333 / 100000) := by
  exact
    packedTile65536 1891293440 1891424512 14 6130 43489 31 _ _ (2136051 / 100000) (1068027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891424512 :
    ThetaLowerSegment 1891424512 1891555584 (189136185369333 / 100000) (7565962119309 / 4000) := by
  exact
    packedTile65536 1891424512 1891555584 14 6024 43490 31 _ _ (1068029 / 50000) (2136061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891555584 :
    ThetaLowerSegment 1891555584 1891686656 (7565962119309 / 4000) (18916241834143 / 10000) := by
  exact
    packedTile65536 1891555584 1891686656 14 6257 43492 31 _ _ (427213 / 20000) (534017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891686656 :
    ThetaLowerSegment 1891686656 1891817728 (18916241834143 / 10000) (94587764775683 / 50000) := by
  exact
    packedTile65536 1891686656 1891817728 14 6138 43493 31 _ _ (267009 / 12500) (85443 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891817728 :
    ThetaLowerSegment 1891817728 1891948800 (94587764775683 / 50000)
      (189188595946609 / 100000) := by
  exact
    packedTile65536 1891817728 1891948800 14 6117 43495 31 _ _ (2136079 / 100000) (1068041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1891948800 :
    ThetaLowerSegment 1891948800 1892079872 (189188595946609 / 100000)
      (37840357682749 / 20000) := by
  exact
    packedTile65536 1891948800 1892079872 14 6176 43496 31 _ _ (1068043 / 50000) (2136089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892079872 :
    ThetaLowerSegment 1892079872 1892210944 (37840357682749 / 20000) (37842997893697 / 20000) := by
  exact
    packedTile65536 1892079872 1892210944 14 6180 43498 31 _ _ (2136093 / 100000) (66753 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892210944 :
    ThetaLowerSegment 1892210944 1892342016 (37842997893697 / 20000) (37845642385497 / 20000) := by
  exact
    packedTile65536 1892210944 1892342016 14 6190 43499 31 _ _ (21361 / 1000) (2136103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892342016 :
    ThetaLowerSegment 1892342016 1892473088 (37845642385497 / 20000) (5913792356058 / 3125) := by
  exact
    packedTile65536 1892342016 1892473088 14 6153 43501 31 _ _ (2136107 / 100000) (213611 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892473088 :
    ThetaLowerSegment 1892473088 1892604160 (5913792356058 / 3125) (23656808891727 / 12500) := by
  exact
    packedTile65536 1892473088 1892604160 14 6140 43502 31 _ _ (1068057 / 50000) (2136117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892604160 :
    ThetaLowerSegment 1892604160 1892735232 (23656808891727 / 12500) (23658439819347 / 12500) := by
  exact
    packedTile65536 1892604160 1892735232 14 6108 43504 31 _ _ (53403 / 2500) (2136123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892735232 :
    ThetaLowerSegment 1892735232 1892866304 (23658439819347 / 12500) (11830045522759 / 6250) := by
  exact
    packedTile65536 1892735232 1892866304 14 6184 43505 31 _ _ (2136127 / 100000) (213613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892866304 :
    ThetaLowerSegment 1892866304 1892997376 (11830045522759 / 6250) (47323432218917 / 25000) := by
  exact
    packedTile65536 1892866304 1892997376 14 6086 43507 31 _ _ (1068067 / 50000) (2136137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1892997376 :
    ThetaLowerSegment 1892997376 1893128448 (47323432218917 / 25000) (37861371946879 / 20000) := by
  exact
    packedTile65536 1892997376 1893128448 14 6147 43508 31 _ _ (2136141 / 100000) (133509 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893128448 :
    ThetaLowerSegment 1893128448 1893259520 (37861371946879 / 20000)
      (189319903054083 / 100000) := by
  exact
    packedTile65536 1893128448 1893259520 14 6106 43510 31 _ _ (534037 / 25000) (2136151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893259520 :
    ThetaLowerSegment 1893259520 1893390592 (189319903054083 / 100000) (5916657579484 / 3125) := by
  exact
    packedTile65536 1893259520 1893390592 14 6151 43511 31 _ _ (427231 / 20000) (1068079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893390592 :
    ThetaLowerSegment 1893390592 1893521664 (5916657579484 / 3125) (47336530031813 / 25000) := by
  exact
    packedTile65536 1893390592 1893521664 14 6122 43513 31 _ _ (1068081 / 50000) (427233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893521664 :
    ThetaLowerSegment 1893521664 1893652736 (47336530031813 / 25000) (47339806915059 / 25000) := by
  exact
    packedTile65536 1893521664 1893652736 14 6136 43514 31 _ _ (2136169 / 100000) (534043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893652736 :
    ThetaLowerSegment 1893652736 1893783808 (47339806915059 / 25000) (47343049096183 / 25000) := by
  exact
    packedTile65536 1893652736 1893783808 14 6071 43516 31 _ _ (133511 / 6250) (2136179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893783808 :
    ThetaLowerSegment 1893783808 1893914880 (47343049096183 / 25000) (946927160873 / 500) := by
  exact
    packedTile65536 1893783808 1893914880 14 6196 43517 31 _ _ (2136183 / 100000) (1068093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1893914880 :
    ThetaLowerSegment 1893914880 1894045952 (946927160873 / 500) (18939850352121 / 10000) := by
  exact
    packedTile65536 1893914880 1894045952 14 6119 43519 31 _ _ (213619 / 10000) (2136193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894045952 :
    ThetaLowerSegment 1894045952 1894177024 (18939850352121 / 10000) (23676463686383 / 12500) := by
  exact
    packedTile65536 1894045952 1894177024 14 6182 43520 31 _ _ (2136197 / 100000) (10681 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894177024 :
    ThetaLowerSegment 1894177024 1894308096 (23676463686383 / 12500) (9471244386677 / 5000) := by
  exact
    packedTile65536 1894177024 1894308096 14 6169 43522 31 _ _ (534051 / 25000) (2136207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894308096 :
    ThetaLowerSegment 1894308096 1894439168 (9471244386677 / 5000) (18943786948171 / 10000) := by
  exact
    packedTile65536 1894308096 1894439168 14 6077 43523 31 _ _ (213621 / 10000) (2136213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894439168 :
    ThetaLowerSegment 1894439168 1894570240 (18943786948171 / 10000) (18945085768107 / 10000) := by
  exact
    packedTile65536 1894439168 1894570240 14 6080 43525 31 _ _ (2136217 / 100000) (106811 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894570240 :
    ThetaLowerSegment 1894570240 1894701312 (18945085768107 / 10000) (3789273286879 / 2000) := by
  exact
    packedTile65536 1894570240 1894701312 14 5995 43526 31 _ _ (66757 / 3125) (2136227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894701312 :
    ThetaLowerSegment 1894701312 1894832384 (3789273286879 / 2000) (189476868387761 / 100000) := by
  exact
    packedTile65536 1894701312 1894832384 14 6181 43528 31 _ _ (2136231 / 100000) (1068117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894832384 :
    ThetaLowerSegment 1894832384 1894963456 (189476868387761 / 100000)
      (189490042567507 / 100000) := by
  exact
    packedTile65536 1894832384 1894963456 14 6167 43529 31 _ _ (1068119 / 50000) (2136241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894963456 :
    ThetaLowerSegment 1894963456 1895094528 (189490042567507 / 100000)
      (47375798856993 / 25000) := by
  exact
    packedTile65536 1894963456 1895094528 14 6157 43531 31 _ _ (427249 / 20000) (267031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895094528 :
    ThetaLowerSegment 1895094528 1895225600 (47375798856993 / 25000) (47379088685073 / 25000) := by
  exact
    packedTile65536 1895094528 1895225600 14 6160 43532 31 _ _ (534063 / 25000) (427251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895225600 :
    ThetaLowerSegment 1895225600 1895356672 (47379088685073 / 25000) (5922793310006 / 3125) := by
  exact
    packedTile65536 1895225600 1895356672 14 6100 43534 31 _ _ (2136259 / 100000) (1068131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895356672 :
    ThetaLowerSegment 1895356672 1895487744 (5922793310006 / 3125) (94771239547253 / 50000) := by
  exact
    packedTile65536 1895356672 1895487744 14 6129 43535 31 _ _ (1068133 / 50000) (2136269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895487744 :
    ThetaLowerSegment 1895487744 1895618816 (94771239547253 / 50000)
      (189555465498073 / 100000) := by
  exact
    packedTile65536 1895487744 1895618816 14 6079 43537 31 _ _ (2136273 / 100000) (534069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895618816 :
    ThetaLowerSegment 1895618816 1895749888 (189555465498073 / 100000)
      (189568490397233 / 100000) := by
  exact
    packedTile65536 1895618816 1895749888 14 6097 43538 31 _ _ (53407 / 2500) (2136283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895749888 :
    ThetaLowerSegment 1895749888 1895880960 (189568490397233 / 100000)
      (23697712916541 / 12500) := by
  exact
    packedTile65536 1895749888 1895880960 14 6185 43540 31 _ _ (2136287 / 100000) (213629 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1895880960 :
    ThetaLowerSegment 1895880960 1896012032 (23697712916541 / 12500) (18959493553117 / 10000) := by
  exact
    packedTile65536 1895880960 1896012032 14 6194 43541 31 _ _ (2136293 / 100000) (267037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896012032 :
    ThetaLowerSegment 1896012032 1896143104 (18959493553117 / 10000) (18960797977897 / 10000) := by
  exact
    packedTile65536 1896012032 1896143104 14 6106 43543 31 _ _ (21363 / 1000) (2136303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896143104 :
    ThetaLowerSegment 1896143104 1896274176 (18960797977897 / 10000) (7584841731851 / 4000) := by
  exact
    packedTile65536 1896143104 1896274176 14 6115 43544 31 _ _ (2136307 / 100000) (213631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896274176 :
    ThetaLowerSegment 1896274176 1896405248 (7584841731851 / 4000) (189634119674269 / 100000) := by
  exact
    packedTile65536 1896274176 1896405248 14 6121 43546 31 _ _ (1068157 / 50000) (2136317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896405248 :
    ThetaLowerSegment 1896405248 1896536320 (189634119674269 / 100000)
      (94823657864543 / 50000) := by
  exact
    packedTile65536 1896405248 1896536320 14 6177 43547 31 _ _ (2136321 / 100000) (534081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896536320 :
    ThetaLowerSegment 1896536320 1896667392 (94823657864543 / 50000) (94830157642483 / 50000) := by
  exact
    packedTile65536 1896536320 1896667392 14 6085 43549 31 _ _ (267041 / 12500) (2136331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896667392 :
    ThetaLowerSegment 1896667392 1896798464 (94830157642483 / 50000) (47418348481959 / 25000) := by
  exact
    packedTile65536 1896667392 1896798464 14 6122 43550 31 _ _ (427267 / 20000) (1068169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896798464 :
    ThetaLowerSegment 1896798464 1896929536 (47418348481959 / 25000) (94843265147397 / 50000) := by
  exact
    packedTile65536 1896798464 1896929536 14 6149 43552 31 _ _ (1068171 / 50000) (427269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1896929536 :
    ThetaLowerSegment 1896929536 1897060608 (94843265147397 / 50000) (237124436507 / 125) := by
  exact
    packedTile65536 1896929536 1897060608 14 6094 43553 31 _ _ (2136349 / 100000) (66761 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897060608 :
    ThetaLowerSegment 1897060608 1897191680 (237124436507 / 125) (47428165005593 / 25000) := by
  exact
    packedTile65536 1897060608 1897191680 14 6137 43555 31 _ _ (534089 / 25000) (2136359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897191680 :
    ThetaLowerSegment 1897191680 1897322752 (47428165005593 / 25000) (4743149559551 / 2500) := by
  exact
    packedTile65536 1897191680 1897322752 14 6236 43556 31 _ _ (2136363 / 100000) (1068183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897322752 :
    ThetaLowerSegment 1897322752 1897339136 (4743149559551 / 2500) (7589104668173 / 4000) := by
  exact
    packedTile65536 1897322752 1897339136 11 765 43558 31 _ _ (2136369 / 100000) (534093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897339136 :
    ThetaLowerSegment 1897339136 1897341184 (7589104668173 / 4000) (37945564359169 / 20000) := by
  exact
    packedTile65536 1897339136 1897341184 8 96 43558 31 _ _ (213637 / 10000) (2136373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1865341184_1897341184 :
    ThetaLowerSegment 1865341184 1897341184 (186528645797453 / 100000)
      (37945564359169 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1865341184 cell1865472256)
                  (ThetaLowerSegment.join cell1865603328 cell1865734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1865865472 cell1865996544)
                  (ThetaLowerSegment.join cell1866127616 cell1866258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1866389760 cell1866520832)
                  (ThetaLowerSegment.join cell1866651904 cell1866782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1866914048 cell1867045120)
                  (ThetaLowerSegment.join cell1867176192 cell1867307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1867438336 cell1867569408)
                  (ThetaLowerSegment.join cell1867700480 cell1867831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1867962624 cell1868093696)
                  (ThetaLowerSegment.join cell1868224768 cell1868355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1868486912 cell1868617984)
                  (ThetaLowerSegment.join cell1868749056 cell1868880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1869011200 cell1869142272)
                  (ThetaLowerSegment.join cell1869273344 cell1869404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1869535488 cell1869666560)
                  (ThetaLowerSegment.join cell1869797632 cell1869928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1870059776 cell1870190848)
                  (ThetaLowerSegment.join cell1870321920 cell1870452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1870584064 cell1870715136)
                  (ThetaLowerSegment.join cell1870846208 cell1870977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1871108352 cell1871239424)
                  (ThetaLowerSegment.join cell1871370496 cell1871501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1871632640 cell1871763712)
                  (ThetaLowerSegment.join cell1871894784 cell1872025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1872156928 cell1872288000)
                  (ThetaLowerSegment.join cell1872419072 cell1872550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1872681216 cell1872812288)
                  (ThetaLowerSegment.join cell1872943360 cell1873074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1873205504 cell1873336576)
                  (ThetaLowerSegment.join cell1873467648 cell1873598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1873729792 cell1873860864)
                  (ThetaLowerSegment.join cell1873991936 cell1874123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1874254080 cell1874385152)
                  (ThetaLowerSegment.join cell1874516224 cell1874647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1874778368 cell1874909440)
                  (ThetaLowerSegment.join cell1875040512 cell1875171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1875302656 cell1875433728)
                  (ThetaLowerSegment.join cell1875564800 cell1875695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1875826944 cell1875958016)
                  (ThetaLowerSegment.join cell1876089088 cell1876220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1876351232 cell1876482304)
                  (ThetaLowerSegment.join cell1876613376 cell1876744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1876875520 cell1877006592)
                  (ThetaLowerSegment.join cell1877137664 cell1877268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1877399808 cell1877530880)
                  (ThetaLowerSegment.join cell1877661952 cell1877793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1877924096 cell1878055168)
                  (ThetaLowerSegment.join cell1878186240 cell1878317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1878448384 cell1878579456)
                  (ThetaLowerSegment.join cell1878710528 cell1878841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1878972672 cell1879103744)
                  (ThetaLowerSegment.join cell1879234816 cell1879365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1879496960 cell1879628032)
                  (ThetaLowerSegment.join cell1879759104 cell1879890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1880021248 cell1880152320)
                  (ThetaLowerSegment.join cell1880283392 cell1880414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1880545536 cell1880676608)
                  (ThetaLowerSegment.join cell1880807680 cell1880938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1881069824 cell1881200896)
                  (ThetaLowerSegment.join cell1881331968 cell1881463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1881594112 cell1881725184)
                  (ThetaLowerSegment.join cell1881856256 cell1881987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1882118400 cell1882249472)
                  (ThetaLowerSegment.join cell1882380544 cell1882511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1882642688 cell1882773760)
                  (ThetaLowerSegment.join cell1882904832 cell1883035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1883166976 cell1883298048)
                  (ThetaLowerSegment.join cell1883429120 cell1883560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1883691264 cell1883822336)
                  (ThetaLowerSegment.join cell1883953408 cell1884084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1884215552 cell1884346624)
                  (ThetaLowerSegment.join cell1884477696 cell1884608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1884739840 cell1884870912)
                  (ThetaLowerSegment.join cell1885001984 cell1885133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1885264128 cell1885395200)
                  (ThetaLowerSegment.join cell1885526272 cell1885657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1885788416 cell1885919488)
                  (ThetaLowerSegment.join cell1886050560 cell1886181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1886312704 cell1886443776)
                  (ThetaLowerSegment.join cell1886574848 cell1886705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1886836992 cell1886968064)
                  (ThetaLowerSegment.join cell1887099136 cell1887230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1887361280 cell1887492352)
                  (ThetaLowerSegment.join cell1887623424 cell1887754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1887885568 cell1888016640)
                  (ThetaLowerSegment.join cell1888147712 cell1888278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1888409856 cell1888540928)
                  (ThetaLowerSegment.join cell1888672000 cell1888803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1888934144 cell1889065216)
                  (ThetaLowerSegment.join cell1889196288 cell1889327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1889458432 cell1889589504)
                  (ThetaLowerSegment.join cell1889720576 cell1889851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1889982720 cell1890113792)
                  (ThetaLowerSegment.join cell1890244864 cell1890375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1890507008 cell1890638080)
                  (ThetaLowerSegment.join cell1890769152 cell1890900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1891031296 cell1891162368)
                  (ThetaLowerSegment.join cell1891293440 cell1891424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1891555584 cell1891686656)
                  (ThetaLowerSegment.join cell1891817728 cell1891948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1892079872 cell1892210944)
                  (ThetaLowerSegment.join cell1892342016 cell1892473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1892604160 cell1892735232)
                  (ThetaLowerSegment.join cell1892866304 cell1892997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1893128448 cell1893259520)
                  (ThetaLowerSegment.join cell1893390592 cell1893521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1893652736 cell1893783808)
                  (ThetaLowerSegment.join cell1893914880 cell1894045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1894177024 cell1894308096)
                  (ThetaLowerSegment.join cell1894439168 cell1894570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1894701312 cell1894832384)
                  (ThetaLowerSegment.join cell1894963456 cell1895094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1895225600 cell1895356672)
                  (ThetaLowerSegment.join cell1895487744 cell1895618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1895749888 cell1895880960)
                  (ThetaLowerSegment.join cell1896012032 cell1896143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1896274176 cell1896405248)
                  (ThetaLowerSegment.join cell1896536320 cell1896667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1896798464 cell1896929536)
                (ThetaLowerSegment.join cell1897060608 cell1897191680))
              (ThetaLowerSegment.join cell1897322752 cell1897339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
