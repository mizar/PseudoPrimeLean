/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2761341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2729341184 :
    ThetaLowerSegment 2729341184 2729472256 (1705800430283 / 625) (10917656811091 / 4000) := by
  exact
    packedTile65536 2729341184 2729472256 14 6145 52243 31 _ _ (2172731 / 100000) (1086367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729472256 :
    ThetaLowerSegment 2729472256 2729603328 (10917656811091 / 4000) (272954474075163 / 100000) := by
  exact
    packedTile65536 2729472256 2729603328 14 6008 52244 31 _ _ (67898 / 3125) (2172739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729603328 :
    ThetaLowerSegment 2729603328 2729734400 (272954474075163 / 100000)
      (272967462720861 / 100000) := by
  exact
    packedTile65536 2729603328 2729734400 14 5978 52245 31 _ _ (2172741 / 100000) (271593 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729734400 :
    ThetaLowerSegment 2729734400 2729865472 (272967462720861 / 100000)
      (272980436187227 / 100000) := by
  exact
    packedTile65536 2729734400 2729865472 14 5971 52246 31 _ _ (1086373 / 50000) (2172749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729865472 :
    ThetaLowerSegment 2729865472 2729996544 (272980436187227 / 100000)
      (272993481378227 / 100000) := by
  exact
    packedTile65536 2729865472 2729996544 14 6004 52248 31 _ _ (8691 / 400) (2172753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2729996544 :
    ThetaLowerSegment 2729996544 2730127616 (272993481378227 / 100000) (17062915924487 / 6250) := by
  exact
    packedTile65536 2729996544 2730127616 14 6063 52249 31 _ _ (434551 / 20000) (1086379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730127616 :
    ThetaLowerSegment 2730127616 2730258688 (17062915924487 / 6250) (17063733425437 / 6250) := by
  exact
    packedTile65536 2730127616 2730258688 14 6020 52250 31 _ _ (54319 / 2500) (2172763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730258688 :
    ThetaLowerSegment 2730258688 2730389760 (17063733425437 / 6250) (273032725768927 / 100000) := by
  exact
    packedTile65536 2730258688 2730389760 14 5979 52251 31 _ _ (434553 / 20000) (67899 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730389760 :
    ThetaLowerSegment 2730389760 2730520832 (273032725768927 / 100000)
      (273045792807707 / 100000) := by
  exact
    packedTile65536 2730389760 2730520832 14 6014 52253 31 _ _ (217277 / 10000) (2172773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730520832 :
    ThetaLowerSegment 2730520832 2730651904 (273045792807707 / 100000)
      (273058718640233 / 100000) := by
  exact
    packedTile65536 2730520832 2730651904 14 5949 52254 31 _ _ (1086387 / 50000) (2172777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730651904 :
    ThetaLowerSegment 2730651904 2730782976 (273058718640233 / 100000)
      (273071976937691 / 100000) := by
  exact
    packedTile65536 2730651904 2730782976 14 6102 52255 31 _ _ (2172779 / 100000) (1086391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730782976 :
    ThetaLowerSegment 2730782976 2730914048 (273071976937691 / 100000)
      (273085022332827 / 100000) := by
  exact
    packedTile65536 2730782976 2730914048 14 6004 52256 31 _ _ (135799 / 6250) (2172787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2730914048 :
    ThetaLowerSegment 2730914048 2731045120 (273085022332827 / 100000)
      (54619634410371 / 20000) := by
  exact
    packedTile65536 2730914048 2731045120 14 6052 52258 31 _ _ (2172789 / 100000) (271599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731045120 :
    ThetaLowerSegment 2731045120 2731176192 (54619634410371 / 20000)
      (273111302245997 / 100000) := by
  exact
    packedTile65536 2731045120 2731176192 14 6043 52259 31 _ _ (1086397 / 50000) (2172797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731176192 :
    ThetaLowerSegment 2731176192 2731307264 (273111302245997 / 100000)
      (273124610633747 / 100000) := by
  exact
    packedTile65536 2731176192 2731307264 14 6125 52260 31 _ _ (1086399 / 50000) (2172801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731307264 :
    ThetaLowerSegment 2731307264 2731438336 (273124610633747 / 100000)
      (273137912533713 / 100000) := by
  exact
    packedTile65536 2731307264 2731438336 14 6122 52261 31 _ _ (2172803 / 100000) (1086403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731438336 :
    ThetaLowerSegment 2731438336 2731569408 (273137912533713 / 100000)
      (273150929826441 / 100000) := by
  exact
    packedTile65536 2731438336 2731569408 14 5991 52263 31 _ _ (271601 / 12500) (2172811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731569408 :
    ThetaLowerSegment 2731569408 2731700480 (273150929826441 / 100000) (13658205179583 / 5000) := by
  exact
    packedTile65536 2731569408 2731700480 14 6063 52264 31 _ _ (2172813 / 100000) (135801 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731700480 :
    ThetaLowerSegment 2731700480 2731831552 (13658205179583 / 5000) (68294304680277 / 25000) := by
  exact
    packedTile65536 2731700480 2731831552 14 6036 52265 31 _ _ (1086409 / 50000) (2172821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731831552 :
    ThetaLowerSegment 2731831552 2731962624 (68294304680277 / 25000) (136595185406337 / 50000) := by
  exact
    packedTile65536 2731831552 2731962624 14 6053 52266 31 _ _ (1086411 / 50000) (86913 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2731962624 :
    ThetaLowerSegment 2731962624 2732093696 (136595185406337 / 50000)
      (136601803837379 / 50000) := by
  exact
    packedTile65536 2731962624 2732093696 14 6092 52268 31 _ _ (2172827 / 100000) (217283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732093696 :
    ThetaLowerSegment 2732093696 2732224768 (136601803837379 / 50000)
      (136608375567763 / 50000) := by
  exact
    packedTile65536 2732093696 2732224768 14 6049 52269 31 _ _ (67901 / 3125) (434567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732224768 :
    ThetaLowerSegment 2732224768 2732355840 (136608375567763 / 50000) (54645965019151 / 20000) := by
  exact
    packedTile65536 2732224768 2732355840 14 6017 52270 31 _ _ (2172837 / 100000) (54321 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732355840 :
    ThetaLowerSegment 2732355840 2732486912 (54645965019151 / 20000)
      (273242918641647 / 100000) := by
  exact
    packedTile65536 2732355840 2732486912 14 6026 52271 31 _ _ (1086421 / 50000) (434569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732486912 :
    ThetaLowerSegment 2732486912 2732617984 (273242918641647 / 100000)
      (273255938334879 / 100000) := by
  exact
    packedTile65536 2732486912 2732617984 14 5992 52273 31 _ _ (1086423 / 50000) (2172849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732617984 :
    ThetaLowerSegment 2732617984 2732749056 (273255938334879 / 100000)
      (273269157960363 / 100000) := by
  exact
    packedTile65536 2732617984 2732749056 14 6084 52274 31 _ _ (2172851 / 100000) (1086427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732749056 :
    ThetaLowerSegment 2732749056 2732880128 (273269157960363 / 100000)
      (273282179886371 / 100000) := by
  exact
    packedTile65536 2732749056 2732880128 14 5993 52275 31 _ _ (271607 / 12500) (2172859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2732880128 :
    ThetaLowerSegment 2732880128 2733011200 (273282179886371 / 100000)
      (136647568328257 / 50000) := by
  exact
    packedTile65536 2732880128 2733011200 14 5963 52276 31 _ _ (2172861 / 100000) (67902 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733011200 :
    ThetaLowerSegment 2733011200 2733142272 (136647568328257 / 50000)
      (136654099960447 / 50000) := by
  exact
    packedTile65536 2733011200 2733142272 14 6012 52278 31 _ _ (434573 / 20000) (543217 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733142272 :
    ThetaLowerSegment 2733142272 2733273344 (136654099960447 / 50000)
      (136660592496007 / 50000) := by
  exact
    packedTile65536 2733142272 2733273344 14 5976 52279 31 _ _ (217287 / 10000) (2172873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733273344 :
    ThetaLowerSegment 2733273344 2733404416 (136660592496007 / 50000) (68333574029941 / 25000) := by
  exact
    packedTile65536 2733273344 2733404416 14 6034 52280 31 _ _ (17383 / 800) (1086439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733404416 :
    ThetaLowerSegment 2733404416 2733535488 (68333574029941 / 25000) (68336871375341 / 25000) := by
  exact
    packedTile65536 2733404416 2733535488 14 6070 52281 31 _ _ (27161 / 1250) (2172883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733535488 :
    ThetaLowerSegment 2733535488 2733666560 (68336871375341 / 25000)
      (273360746618519 / 100000) := by
  exact
    packedTile65536 2733535488 2733666560 14 6103 52283 31 _ _ (434577 / 20000) (271611 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733666560 :
    ThetaLowerSegment 2733666560 2733797632 (273360746618519 / 100000)
      (273373862176523 / 100000) := by
  exact
    packedTile65536 2733666560 2733797632 14 6036 52284 31 _ _ (2172889 / 100000) (543223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733797632 :
    ThetaLowerSegment 2733797632 2733928704 (273373862176523 / 100000)
      (273386901713417 / 100000) := by
  exact
    packedTile65536 2733797632 2733928704 14 6001 52285 31 _ _ (1086447 / 50000) (2172897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2733928704 :
    ThetaLowerSegment 2733928704 2734059776 (273386901713417 / 100000)
      (273400034714973 / 100000) := by
  exact
    packedTile65536 2733928704 2734059776 14 6044 52286 31 _ _ (2172899 / 100000) (1086451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734059776 :
    ThetaLowerSegment 2734059776 2734190848 (273400034714973 / 100000)
      (273412939591829 / 100000) := by
  exact
    packedTile65536 2734059776 2734190848 14 5939 52288 31 _ _ (271613 / 12500) (2172907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734190848 :
    ThetaLowerSegment 2734190848 2734321920 (273412939591829 / 100000)
      (68356539349319 / 25000) := by
  exact
    packedTile65536 2734190848 2734321920 14 6083 52289 31 _ _ (2172909 / 100000) (135807 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734321920 :
    ThetaLowerSegment 2734321920 2734452992 (68356539349319 / 25000) (68359811756297 / 25000) := by
  exact
    packedTile65536 2734321920 2734452992 14 6024 52290 31 _ _ (2172913 / 100000) (543229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734452992 :
    ThetaLowerSegment 2734452992 2734584064 (68359811756297 / 25000) (27345234754781 / 10000) := by
  exact
    packedTile65536 2734452992 2734584064 14 6029 52291 31 _ _ (1086459 / 50000) (2172921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734584064 :
    ThetaLowerSegment 2734584064 2734715136 (27345234754781 / 10000) (13673276859521 / 5000) := by
  exact
    packedTile65536 2734584064 2734715136 14 6070 52293 31 _ _ (2172923 / 100000) (1086463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734715136 :
    ThetaLowerSegment 2734715136 2734846208 (13673276859521 / 5000) (68369662159493 / 25000) := by
  exact
    packedTile65536 2734715136 2734846208 14 6034 52294 31 _ _ (67904 / 3125) (2172931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734846208 :
    ThetaLowerSegment 2734846208 2734977280 (68369662159493 / 25000) (34186461865963 / 12500) := by
  exact
    packedTile65536 2734846208 2734977280 14 6004 52295 31 _ _ (2172933 / 100000) (271617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2734977280 :
    ThetaLowerSegment 2734977280 2735108352 (34186461865963 / 12500) (136752351064293 / 50000) := by
  exact
    packedTile65536 2734977280 2735108352 14 5986 52297 31 _ _ (2172937 / 100000) (108647 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735108352 :
    ThetaLowerSegment 2735108352 2735239424 (136752351064293 / 50000) (34189709052423 / 12500) := by
  exact
    packedTile65536 2735108352 2735239424 14 5969 52298 31 _ _ (1086471 / 50000) (434589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735239424 :
    ThetaLowerSegment 2735239424 2735370496 (34189709052423 / 12500)
      (273530725312013 / 100000) := by
  exact
    packedTile65536 2735239424 2735370496 14 6007 52299 31 _ _ (2172947 / 100000) (43459 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735370496 :
    ThetaLowerSegment 2735370496 2735501568 (273530725312013 / 100000)
      (273543702181357 / 100000) := by
  exact
    packedTile65536 2735370496 2735501568 14 5972 52300 31 _ _ (271619 / 12500) (434591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735501568 :
    ThetaLowerSegment 2735501568 2735632640 (273543702181357 / 100000)
      (273556852917121 / 100000) := by
  exact
    packedTile65536 2735501568 2735632640 14 6052 52302 31 _ _ (2172957 / 100000) (13581 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735632640 :
    ThetaLowerSegment 2735632640 2735763712 (273556852917121 / 100000)
      (273570077557767 / 100000) := by
  exact
    packedTile65536 2735632640 2735763712 14 6086 52303 31 _ _ (2172961 / 100000) (543241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735763712 :
    ThetaLowerSegment 2735763712 2735894784 (273570077557767 / 100000)
      (273583276153251 / 100000) := by
  exact
    packedTile65536 2735763712 2735894784 14 6074 52304 31 _ _ (1086483 / 50000) (2172969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2735894784 :
    ThetaLowerSegment 2735894784 2736025856 (273583276153251 / 100000)
      (273596266173889 / 100000) := by
  exact
    packedTile65536 2735894784 2736025856 14 5978 52305 31 _ _ (2172971 / 100000) (1086487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736025856 :
    ThetaLowerSegment 2736025856 2736156928 (273596266173889 / 100000)
      (273609384430001 / 100000) := by
  exact
    packedTile65536 2736025856 2736156928 14 6037 52307 31 _ _ (135811 / 6250) (2172979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736156928 :
    ThetaLowerSegment 2736156928 2736288000 (273609384430001 / 100000)
      (273622444045811 / 100000) := by
  exact
    packedTile65536 2736156928 2736288000 14 6010 52308 31 _ _ (2172981 / 100000) (271623 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736288000 :
    ThetaLowerSegment 2736288000 2736419072 (273622444045811 / 100000) (8551106977663 / 3125) := by
  exact
    packedTile65536 2736288000 2736419072 14 5973 52309 31 _ _ (434597 / 20000) (543247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736419072 :
    ThetaLowerSegment 2736419072 2736550144 (8551106977663 / 3125) (136824255601993 / 50000) := by
  exact
    packedTile65536 2736419072 2736550144 14 6023 52310 31 _ _ (217299 / 10000) (2172993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736550144 :
    ThetaLowerSegment 2736550144 2736681216 (136824255601993 / 50000)
      (136830800662933 / 50000) := by
  exact
    packedTile65536 2736550144 2736681216 14 6024 52312 31 _ _ (434599 / 20000) (1086499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736681216 :
    ThetaLowerSegment 2736681216 2736812288 (136830800662933 / 50000)
      (136837395717933 / 50000) := by
  exact
    packedTile65536 2736681216 2736812288 14 6070 52313 31 _ _ (2173 / 100) (2173003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736812288 :
    ThetaLowerSegment 2736812288 2736943360 (136837395717933 / 50000)
      (136843952757503 / 50000) := by
  exact
    packedTile65536 2736812288 2736943360 14 6035 52314 31 _ _ (543251 / 25000) (2173007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2736943360 :
    ThetaLowerSegment 2736943360 2737074432 (136843952757503 / 50000) (54740210878493 / 20000) := by
  exact
    packedTile65536 2736943360 2737074432 14 6051 52315 31 _ _ (2173009 / 100000) (543253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737074432 :
    ThetaLowerSegment 2737074432 2737205504 (54740210878493 / 20000)
      (273713979479737 / 100000) := by
  exact
    packedTile65536 2737074432 2737205504 14 5948 52317 31 _ _ (1086507 / 50000) (2173017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737205504 :
    ThetaLowerSegment 2737205504 2737336576 (273713979479737 / 100000) (3421588724943 / 1250) := by
  exact
    packedTile65536 2737205504 2737336576 14 6037 52318 31 _ _ (2173019 / 100000) (1086511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737336576 :
    ThetaLowerSegment 2737336576 2737467648 (3421588724943 / 1250) (17108762447321 / 6250) := by
  exact
    packedTile65536 2737336576 2737467648 14 6029 52319 31 _ _ (67907 / 3125) (2173027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737467648 :
    ThetaLowerSegment 2737467648 2737598720 (17108762447321 / 6250) (2737533742259 / 1000) := by
  exact
    packedTile65536 2737467648 2737598720 14 6063 52320 31 _ _ (543257 / 25000) (2173031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737598720 :
    ThetaLowerSegment 2737598720 2737729792 (2737533742259 / 1000) (27376656453621 / 10000) := by
  exact
    packedTile65536 2737598720 2737729792 14 6070 52322 31 _ _ (2173033 / 100000) (543259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737729792 :
    ThetaLowerSegment 2737729792 2737860864 (27376656453621 / 10000) (136889838323751 / 50000) := by
  exact
    packedTile65536 2737729792 2737860864 14 6034 52323 31 _ _ (1086519 / 50000) (2173041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737860864 :
    ThetaLowerSegment 2737860864 2737991936 (136889838323751 / 50000)
      (273792821384609 / 100000) := by
  exact
    packedTile65536 2737860864 2737991936 14 6049 52324 31 _ _ (2173043 / 100000) (1086523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2737991936 :
    ThetaLowerSegment 2737991936 2738123008 (273792821384609 / 100000)
      (273805985709393 / 100000) := by
  exact
    packedTile65536 2737991936 2738123008 14 6058 52325 31 _ _ (271631 / 12500) (2173051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738123008 :
    ThetaLowerSegment 2738123008 2738254080 (273805985709393 / 100000)
      (273819273922373 / 100000) := by
  exact
    packedTile65536 2738123008 2738254080 14 6115 52327 31 _ _ (543263 / 25000) (434611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738254080 :
    ThetaLowerSegment 2738254080 2738385152 (273819273922373 / 100000)
      (273832316610487 / 100000) := by
  exact
    packedTile65536 2738254080 2738385152 14 6002 52328 31 _ _ (2173057 / 100000) (108653 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738385152 :
    ThetaLowerSegment 2738385152 2738516224 (273832316610487 / 100000)
      (273845433212719 / 100000) := by
  exact
    packedTile65536 2738385152 2738516224 14 6036 52329 31 _ _ (1086531 / 50000) (434613 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738516224 :
    ThetaLowerSegment 2738516224 2738647296 (273845433212719 / 100000)
      (273858397730441 / 100000) := by
  exact
    packedTile65536 2738516224 2738647296 14 5966 52330 31 _ _ (2173067 / 100000) (217307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738647296 :
    ThetaLowerSegment 2738647296 2738778368 (273858397730441 / 100000)
      (273871353579743 / 100000) := by
  exact
    packedTile65536 2738647296 2738778368 14 5962 52332 31 _ _ (2173071 / 100000) (1086537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738778368 :
    ThetaLowerSegment 2738778368 2738909440 (273871353579743 / 100000)
      (273884550670291 / 100000) := by
  exact
    packedTile65536 2738778368 2738909440 14 6073 52333 31 _ _ (543269 / 25000) (2173079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2738909440 :
    ThetaLowerSegment 2738909440 2739040512 (273884550670291 / 100000)
      (273897862964497 / 100000) := by
  exact
    packedTile65536 2738909440 2739040512 14 6126 52334 31 _ _ (2173081 / 100000) (543271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739040512 :
    ThetaLowerSegment 2739040512 2739171584 (273897862964497 / 100000)
      (54782238100187 / 20000) := by
  exact
    packedTile65536 2739040512 2739171584 14 6133 52335 31 _ _ (1086543 / 50000) (2173089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739171584 :
    ThetaLowerSegment 2739171584 2739302656 (54782238100187 / 20000)
      (273924281201119 / 100000) := by
  exact
    packedTile65536 2739171584 2739302656 14 6024 52337 31 _ _ (2173091 / 100000) (1086547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739302656 :
    ThetaLowerSegment 2739302656 2739433728 (273924281201119 / 100000)
      (273937437118249 / 100000) := by
  exact
    packedTile65536 2739302656 2739433728 14 6054 52338 31 _ _ (434619 / 20000) (1086549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739433728 :
    ThetaLowerSegment 2739433728 2739564800 (273937437118249 / 100000)
      (273950599584949 / 100000) := by
  exact
    packedTile65536 2739433728 2739564800 14 6057 52339 31 _ _ (21731 / 1000) (2173103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739564800 :
    ThetaLowerSegment 2739564800 2739695872 (273950599584949 / 100000)
      (136981828886447 / 50000) := by
  exact
    packedTile65536 2739564800 2739695872 14 6009 52340 31 _ _ (434621 / 20000) (543277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739695872 :
    ThetaLowerSegment 2739695872 2739826944 (136981828886447 / 50000) (34247088955583 / 12500) := by
  exact
    packedTile65536 2739695872 2739826944 14 6007 52342 31 _ _ (217311 / 10000) (2173113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739826944 :
    ThetaLowerSegment 2739826944 2739958016 (34247088955583 / 12500)
      (273989709045479 / 100000) := by
  exact
    packedTile65536 2739826944 2739958016 14 5981 52343 31 _ _ (434623 / 20000) (1086559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2739958016 :
    ThetaLowerSegment 2739958016 2740089088 (273989709045479 / 100000)
      (274002695604623 / 100000) := by
  exact
    packedTile65536 2739958016 2740089088 14 5976 52344 31 _ _ (2173119 / 100000) (1086561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740089088 :
    ThetaLowerSegment 2740089088 2740220160 (274002695604623 / 100000)
      (274015836485451 / 100000) := by
  exact
    packedTile65536 2740089088 2740220160 14 6047 52345 31 _ _ (543281 / 25000) (2173127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740220160 :
    ThetaLowerSegment 2740220160 2740351232 (274015836485451 / 100000)
      (274029144727447 / 100000) := by
  exact
    packedTile65536 2740220160 2740351232 14 6124 52347 31 _ _ (2173129 / 100000) (543283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740351232 :
    ThetaLowerSegment 2740351232 2740482304 (274029144727447 / 100000)
      (274042266110539 / 100000) := by
  exact
    packedTile65536 2740351232 2740482304 14 6038 52348 31 _ _ (1086567 / 50000) (2173137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740482304 :
    ThetaLowerSegment 2740482304 2740613376 (274042266110539 / 100000)
      (274055448365647 / 100000) := by
  exact
    packedTile65536 2740482304 2740613376 14 6066 52349 31 _ _ (1086569 / 50000) (2173141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740613376 :
    ThetaLowerSegment 2740613376 2740744448 (274055448365647 / 100000)
      (274068687152803 / 100000) := by
  exact
    packedTile65536 2740613376 2740744448 14 6092 52350 31 _ _ (2173143 / 100000) (1086573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740744448 :
    ThetaLowerSegment 2740744448 2740875520 (274068687152803 / 100000)
      (274081736906543 / 100000) := by
  exact
    packedTile65536 2740744448 2740875520 14 6005 52352 31 _ _ (543287 / 25000) (2173151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2740875520 :
    ThetaLowerSegment 2740875520 2741006592 (274081736906543 / 100000)
      (274094901867417 / 100000) := by
  exact
    packedTile65536 2740875520 2741006592 14 6058 52353 31 _ _ (2173153 / 100000) (543289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741006592 :
    ThetaLowerSegment 2741006592 2741137664 (274094901867417 / 100000)
      (274107914737521 / 100000) := by
  exact
    packedTile65536 2741006592 2741137664 14 5988 52354 31 _ _ (1086579 / 50000) (2173161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741137664 :
    ThetaLowerSegment 2741137664 2741268736 (274107914737521 / 100000)
      (274121168852559 / 100000) := by
  exact
    packedTile65536 2741137664 2741268736 14 6099 52355 31 _ _ (1086581 / 50000) (434633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741268736 :
    ThetaLowerSegment 2741268736 2741399808 (274121168852559 / 100000)
      (137067174555207 / 50000) := by
  exact
    packedTile65536 2741268736 2741399808 14 6065 52357 31 _ _ (2173167 / 100000) (217317 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741399808 :
    ThetaLowerSegment 2741399808 2741530880 (137067174555207 / 50000) (27414760111327 / 10000) := by
  exact
    packedTile65536 2741399808 2741530880 14 6098 52358 31 _ _ (543293 / 25000) (86927 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741530880 :
    ThetaLowerSegment 2741530880 2741661952 (27414760111327 / 10000)
      (274160698851049 / 100000) := by
  exact
    packedTile65536 2741530880 2741661952 14 6027 52359 31 _ _ (2173177 / 100000) (108659 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741661952 :
    ThetaLowerSegment 2741661952 2741793024 (274160698851049 / 100000)
      (274173694479409 / 100000) := by
  exact
    packedTile65536 2741661952 2741793024 14 5980 52360 31 _ _ (1086591 / 50000) (434637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741793024 :
    ThetaLowerSegment 2741793024 2741924096 (274173694479409 / 100000)
      (274186918316219 / 100000) := by
  exact
    packedTile65536 2741793024 2741924096 14 6085 52362 31 _ _ (1086593 / 50000) (2173189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2741924096 :
    ThetaLowerSegment 2741924096 2742055168 (274186918316219 / 100000)
      (54839968021981 / 20000) := by
  exact
    packedTile65536 2741924096 2742055168 14 5946 52363 31 _ _ (2173191 / 100000) (1086597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742055168 :
    ThetaLowerSegment 2742055168 2742186240 (54839968021981 / 20000) (54842564991201 / 20000) := by
  exact
    packedTile65536 2742055168 2742186240 14 5975 52364 31 _ _ (543299 / 25000) (2173199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742186240 :
    ThetaLowerSegment 2742186240 2742317312 (54842564991201 / 20000)
      (274225938050839 / 100000) := by
  exact
    packedTile65536 2742186240 2742317312 14 6034 52365 31 _ _ (2173201 / 100000) (543301 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742317312 :
    ThetaLowerSegment 2742317312 2742448384 (274225938050839 / 100000)
      (68559792674021 / 25000) := by
  exact
    packedTile65536 2742317312 2742448384 14 6089 52367 31 _ _ (434641 / 20000) (271651 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742448384 :
    ThetaLowerSegment 2742448384 2742579456 (68559792674021 / 25000) (137126053907607 / 50000) := by
  exact
    packedTile65536 2742448384 2742579456 14 5953 52368 31 _ _ (217321 / 10000) (2173213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742579456 :
    ThetaLowerSegment 2742579456 2742710528 (137126053907607 / 50000) (34283131978773 / 12500) := by
  exact
    packedTile65536 2742579456 2742710528 14 5958 52369 31 _ _ (434643 / 20000) (1086609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742710528 :
    ThetaLowerSegment 2742710528 2742841600 (34283131978773 / 12500) (68569523244241 / 25000) := by
  exact
    packedTile65536 2742710528 2742841600 14 5999 52370 31 _ _ (108661 / 5000) (2173223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742841600 :
    ThetaLowerSegment 2742841600 2742972672 (68569523244241 / 25000)
      (274291256200789 / 100000) := by
  exact
    packedTile65536 2742841600 2742972672 14 6057 52372 31 _ _ (86929 / 4000) (543307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2742972672 :
    ThetaLowerSegment 2742972672 2743103744 (274291256200789 / 100000)
      (274304334692911 / 100000) := by
  exact
    packedTile65536 2742972672 2743103744 14 6018 52373 31 _ _ (2173229 / 100000) (135827 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743103744 :
    ThetaLowerSegment 2743103744 2743234816 (274304334692911 / 100000)
      (54863514372241 / 20000) := by
  exact
    packedTile65536 2743103744 2743234816 14 6091 52374 31 _ _ (1086617 / 50000) (2173237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743234816 :
    ThetaLowerSegment 2743234816 2743365888 (54863514372241 / 20000)
      (274330559137469 / 100000) := by
  exact
    packedTile65536 2743234816 2743365888 14 5976 52375 31 _ _ (2173239 / 100000) (1086621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743365888 :
    ThetaLowerSegment 2743365888 2743496960 (274330559137469 / 100000)
      (274343568176053 / 100000) := by
  exact
    packedTile65536 2743365888 2743496960 14 5986 52377 31 _ _ (543311 / 25000) (2173247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743496960 :
    ThetaLowerSegment 2743496960 2743628032 (274343568176053 / 100000)
      (274356592451317 / 100000) := by
  exact
    packedTile65536 2743496960 2743628032 14 5993 52378 31 _ _ (67914 / 3125) (2173251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743628032 :
    ThetaLowerSegment 2743628032 2743759104 (274356592451317 / 100000)
      (274369531999679 / 100000) := by
  exact
    packedTile65536 2743628032 2743759104 14 5954 52379 31 _ _ (2173253 / 100000) (271657 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743759104 :
    ThetaLowerSegment 2743759104 2743890176 (274369531999679 / 100000)
      (274382571547679 / 100000) := by
  exact
    packedTile65536 2743759104 2743890176 14 6000 52380 31 _ _ (1086629 / 50000) (2173261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2743890176 :
    ThetaLowerSegment 2743890176 2744021248 (274382571547679 / 100000)
      (274395784986719 / 100000) := by
  exact
    packedTile65536 2743890176 2744021248 14 6080 52382 31 _ _ (2173263 / 100000) (1086633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744021248 :
    ThetaLowerSegment 2744021248 2744152320 (274395784986719 / 100000)
      (274408744183803 / 100000) := by
  exact
    packedTile65536 2744021248 2744152320 14 5963 52383 31 _ _ (543317 / 25000) (2173271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744152320 :
    ThetaLowerSegment 2744152320 2744283392 (274408744183803 / 100000)
      (54884359371087 / 20000) := by
  exact
    packedTile65536 2744152320 2744283392 14 6006 52384 31 _ _ (271659 / 12500) (86931 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744283392 :
    ThetaLowerSegment 2744283392 2744414464 (54884359371087 / 20000) (137217417172079 / 50000) := by
  exact
    packedTile65536 2744283392 2744414464 14 5999 52385 31 _ _ (2173277 / 100000) (13583 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744414464 :
    ThetaLowerSegment 2744414464 2744545536 (137217417172079 / 50000)
      (137223882686029 / 50000) := by
  exact
    packedTile65536 2744414464 2744545536 14 5950 52387 31 _ _ (1086641 / 50000) (434657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744545536 :
    ThetaLowerSegment 2744545536 2744676608 (137223882686029 / 50000) (54892213612357 / 20000) := by
  exact
    packedTile65536 2744545536 2744676608 14 6121 52388 31 _ _ (2173287 / 100000) (217329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744676608 :
    ThetaLowerSegment 2744676608 2744807680 (54892213612357 / 20000) (137237018044591 / 50000) := by
  exact
    packedTile65536 2744676608 2744807680 14 5967 52389 31 _ _ (2173291 / 100000) (1086647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744807680 :
    ThetaLowerSegment 2744807680 2744938752 (137237018044591 / 50000)
      (137243615084599 / 50000) := by
  exact
    packedTile65536 2744807680 2744938752 14 6071 52390 31 _ _ (135831 / 6250) (2173299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2744938752 :
    ThetaLowerSegment 2744938752 2745069824 (137243615084599 / 50000) (68625109873169 / 25000) := by
  exact
    packedTile65536 2744938752 2745069824 14 6078 52392 31 _ _ (2173301 / 100000) (271663 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745069824 :
    ThetaLowerSegment 2745069824 2745200896 (68625109873169 / 25000) (137256853762903 / 50000) := by
  exact
    packedTile65536 2745069824 2745200896 14 6105 52393 31 _ _ (1086653 / 50000) (2173309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745200896 :
    ThetaLowerSegment 2745200896 2745331968 (137256853762903 / 50000)
      (137263473668209 / 50000) := by
  exact
    packedTile65536 2745200896 2745331968 14 6092 52394 31 _ _ (2173311 / 100000) (1086657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745331968 :
    ThetaLowerSegment 2745331968 2745463040 (137263473668209 / 50000)
      (274539967666583 / 100000) := by
  exact
    packedTile65536 2745331968 2745463040 14 5991 52395 31 _ _ (434663 / 20000) (1086659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745463040 :
    ThetaLowerSegment 2745463040 2745594112 (274539967666583 / 100000)
      (274552996719983 / 100000) := by
  exact
    packedTile65536 2745463040 2745594112 14 5995 52397 31 _ _ (54333 / 2500) (2173323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745594112 :
    ThetaLowerSegment 2745594112 2745725184 (274552996719983 / 100000)
      (274566019283383 / 100000) := by
  exact
    packedTile65536 2745594112 2745725184 14 5992 52398 31 _ _ (86933 / 4000) (135833 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745725184 :
    ThetaLowerSegment 2745725184 2745856256 (274566019283383 / 100000)
      (274579033183423 / 100000) := by
  exact
    packedTile65536 2745725184 2745856256 14 5988 52399 31 _ _ (217333 / 10000) (2173333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745856256 :
    ThetaLowerSegment 2745856256 2745987328 (274579033183423 / 100000)
      (274592051454083 / 100000) := by
  exact
    packedTile65536 2745856256 2745987328 14 5990 52400 31 _ _ (1086667 / 50000) (2173337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2745987328 :
    ThetaLowerSegment 2745987328 2746118400 (274592051454083 / 100000)
      (34325670937767 / 12500) := by
  exact
    packedTile65536 2745987328 2746118400 14 6127 52402 31 _ _ (2173339 / 100000) (1086671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746118400 :
    ThetaLowerSegment 2746118400 2746249472 (34325670937767 / 12500) (34327307465799 / 12500) := by
  exact
    packedTile65536 2746118400 2746249472 14 6024 52403 31 _ _ (67917 / 3125) (2173347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746249472 :
    ThetaLowerSegment 2746249472 2746380544 (34327307465799 / 12500)
      (274631593274399 / 100000) := by
  exact
    packedTile65536 2746249472 2746380544 14 6043 52404 31 _ _ (2173349 / 100000) (271669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746380544 :
    ThetaLowerSegment 2746380544 2746511616 (274631593274399 / 100000)
      (274644629045693 / 100000) := by
  exact
    packedTile65536 2746380544 2746511616 14 5998 52405 31 _ _ (2173353 / 100000) (543339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746511616 :
    ThetaLowerSegment 2746511616 2746642688 (274644629045693 / 100000)
      (54931559484363 / 20000) := by
  exact
    packedTile65536 2746511616 2746642688 14 6059 52407 31 _ _ (1086679 / 50000) (2173361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746642688 :
    ThetaLowerSegment 2746642688 2746773760 (54931559484363 / 20000) (137335463353849 / 50000) := by
  exact
    packedTile65536 2746642688 2746773760 14 6041 52408 31 _ _ (2173363 / 100000) (1086683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746773760 :
    ThetaLowerSegment 2746773760 2746904832 (137335463353849 / 50000)
      (137342041052101 / 50000) := by
  exact
    packedTile65536 2746773760 2746904832 14 6053 52409 31 _ _ (271671 / 12500) (2173371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2746904832 :
    ThetaLowerSegment 2746904832 2747035904 (137342041052101 / 50000) (54939390129147 / 20000) := by
  exact
    packedTile65536 2746904832 2747035904 14 5921 52410 31 _ _ (2173373 / 100000) (67918 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747035904 :
    ThetaLowerSegment 2747035904 2747166976 (54939390129147 / 20000) (27471002350839 / 10000) := by
  exact
    packedTile65536 2747035904 2747166976 14 6015 52412 31 _ _ (2173377 / 100000) (108669 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747166976 :
    ThetaLowerSegment 2747166976 2747298048 (27471002350839 / 10000) (137361503646229 / 50000) := by
  exact
    packedTile65536 2747166976 2747298048 14 5974 52413 31 _ _ (1086691 / 50000) (434677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747298048 :
    ThetaLowerSegment 2747298048 2747429120 (137361503646229 / 50000)
      (274736197578161 / 100000) := by
  exact
    packedTile65536 2747298048 2747429120 14 6069 52414 31 _ _ (2173387 / 100000) (217339 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747429120 :
    ThetaLowerSegment 2747429120 2747560192 (274736197578161 / 100000)
      (274749161861441 / 100000) := by
  exact
    packedTile65536 2747429120 2747560192 14 5965 52415 31 _ _ (135837 / 6250) (434679 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747560192 :
    ThetaLowerSegment 2747560192 2747691264 (274749161861441 / 100000)
      (274762280479697 / 100000) := by
  exact
    packedTile65536 2747560192 2747691264 14 6036 52417 31 _ _ (543349 / 25000) (2173399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747691264 :
    ThetaLowerSegment 2747691264 2747822336 (274762280479697 / 100000) (5495508721519 / 2000) := by
  exact
    packedTile65536 2747691264 2747822336 14 6053 52418 31 _ _ (2173401 / 100000) (543351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747822336 :
    ThetaLowerSegment 2747822336 2747953408 (5495508721519 / 2000) (8587137106322 / 3125) := by
  exact
    packedTile65536 2747822336 2747953408 14 5959 52419 31 _ _ (1086703 / 50000) (2173409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2747953408 :
    ThetaLowerSegment 2747953408 2748084480 (8587137106322 / 3125) (274801595220951 / 100000) := by
  exact
    packedTile65536 2747953408 2748084480 14 6077 52420 31 _ _ (2173411 / 100000) (1086707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748084480 :
    ThetaLowerSegment 2748084480 2748215552 (274801595220951 / 100000)
      (68703660557799 / 25000) := by
  exact
    packedTile65536 2748084480 2748215552 14 6003 52422 31 _ _ (434683 / 20000) (1086709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748215552 :
    ThetaLowerSegment 2748215552 2748346624 (68703660557799 / 25000) (17176726775981 / 6250) := by
  exact
    packedTile65536 2748215552 2748346624 14 5975 52423 31 _ _ (108671 / 5000) (2173423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748346624 :
    ThetaLowerSegment 2748346624 2748477696 (17176726775981 / 6250) (68710165067999 / 25000) := by
  exact
    packedTile65536 2748346624 2748477696 14 5996 52424 31 _ _ (86937 / 4000) (543357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748477696 :
    ThetaLowerSegment 2748477696 2748608768 (68710165067999 / 25000) (137426803697253 / 50000) := by
  exact
    packedTile65536 2748477696 2748608768 14 5957 52425 31 _ _ (217343 / 10000) (2173433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748608768 :
    ThetaLowerSegment 2748608768 2748739840 (137426803697253 / 50000)
      (137433393552173 / 50000) := by
  exact
    packedTile65536 2748608768 2748739840 14 6064 52427 31 _ _ (434687 / 20000) (1086719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748739840 :
    ThetaLowerSegment 2748739840 2748870912 (137433393552173 / 50000)
      (137440035581757 / 50000) := by
  exact
    packedTile65536 2748739840 2748870912 14 6112 52428 31 _ _ (2173439 / 100000) (1086721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2748870912 :
    ThetaLowerSegment 2748870912 2749001984 (137440035581757 / 50000)
      (137446643938239 / 50000) := by
  exact
    packedTile65536 2748870912 2749001984 14 6081 52429 31 _ _ (543361 / 25000) (2173447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749001984 :
    ThetaLowerSegment 2749001984 2749133056 (137446643938239 / 50000)
      (274906382906703 / 100000) := by
  exact
    packedTile65536 2749001984 2749133056 14 6025 52430 31 _ _ (2173449 / 100000) (543363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749133056 :
    ThetaLowerSegment 2749133056 2749264128 (274906382906703 / 100000)
      (274919338865997 / 100000) := by
  exact
    packedTile65536 2749133056 2749264128 14 5961 52432 31 _ _ (1086727 / 50000) (2173457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749264128 :
    ThetaLowerSegment 2749264128 2749395200 (274919338865997 / 100000)
      (274932557837553 / 100000) := by
  exact
    packedTile65536 2749264128 2749395200 14 6082 52433 31 _ _ (1086729 / 50000) (2173461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749395200 :
    ThetaLowerSegment 2749395200 2749526272 (274932557837553 / 100000) (6873642627881 / 2500) := by
  exact
    packedTile65536 2749395200 2749526272 14 6049 52434 31 _ _ (2173463 / 100000) (1086733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749526272 :
    ThetaLowerSegment 2749526272 2749657344 (6873642627881 / 2500) (68739688110911 / 25000) := by
  exact
    packedTile65536 2749526272 2749657344 14 6003 52435 31 _ _ (543367 / 25000) (2173471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749657344 :
    ThetaLowerSegment 2749657344 2749788416 (68739688110911 / 25000) (137485994447107 / 50000) := by
  exact
    packedTile65536 2749657344 2749788416 14 6090 52437 31 _ _ (2173473 / 100000) (543369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749788416 :
    ThetaLowerSegment 2749788416 2749919488 (137485994447107 / 50000) (17186558111017 / 6250) := by
  exact
    packedTile65536 2749788416 2749919488 14 5954 52438 31 _ _ (2173477 / 100000) (54337 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2749919488 :
    ThetaLowerSegment 2749919488 2750050560 (17186558111017 / 6250) (68749480712917 / 25000) := by
  exact
    packedTile65536 2749919488 2750050560 14 5978 52439 31 _ _ (1086741 / 50000) (434697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750050560 :
    ThetaLowerSegment 2750050560 2750181632 (68749480712917 / 25000) (13750545580499 / 5000) := by
  exact
    packedTile65536 2750050560 2750181632 14 5976 52440 31 _ _ (2173487 / 100000) (217349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750181632 :
    ThetaLowerSegment 2750181632 2750312704 (13750545580499 / 5000) (68755989227241 / 25000) := by
  exact
    packedTile65536 2750181632 2750312704 14 6002 52442 31 _ _ (543373 / 25000) (434699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750312704 :
    ThetaLowerSegment 2750312704 2750443776 (68755989227241 / 25000) (137518531547937 / 50000) := by
  exact
    packedTile65536 2750312704 2750443776 14 6030 52443 31 _ _ (2173497 / 100000) (4347 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750443776 :
    ThetaLowerSegment 2750443776 2750574848 (137518531547937 / 50000)
      (275050271461451 / 100000) := by
  exact
    packedTile65536 2750443776 2750574848 14 6077 52444 31 _ _ (2173501 / 100000) (67922 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750574848 :
    ThetaLowerSegment 2750574848 2750705920 (275050271461451 / 100000)
      (275063486377931 / 100000) := by
  exact
    packedTile65536 2750574848 2750705920 14 6080 52445 31 _ _ (1086753 / 50000) (2173509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750705920 :
    ThetaLowerSegment 2750705920 2750836992 (275063486377931 / 100000)
      (55015315921639 / 20000) := by
  exact
    packedTile65536 2750705920 2750836992 14 6024 52447 31 _ _ (2173511 / 100000) (1086757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750836992 :
    ThetaLowerSegment 2750836992 2750968064 (55015315921639 / 20000)
      (275089655480451 / 100000) := by
  exact
    packedTile65536 2750836992 2750968064 14 6016 52448 31 _ _ (543379 / 25000) (2173519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2750968064 :
    ThetaLowerSegment 2750968064 2751099136 (275089655480451 / 100000)
      (275102870482051 / 100000) := by
  exact
    packedTile65536 2750968064 2751099136 14 6080 52449 31 _ _ (27169 / 1250) (2173523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751099136 :
    ThetaLowerSegment 2751099136 2751230208 (275102870482051 / 100000)
      (275116207231451 / 100000) := by
  exact
    packedTile65536 2751099136 2751230208 14 6136 52450 31 _ _ (86941 / 4000) (271691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751230208 :
    ThetaLowerSegment 2751230208 2751361280 (275116207231451 / 100000)
      (275129324485001 / 100000) := by
  exact
    packedTile65536 2751230208 2751361280 14 6035 52452 31 _ _ (217353 / 10000) (2173533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751361280 :
    ThetaLowerSegment 2751361280 2751492352 (275129324485001 / 100000)
      (275142530883661 / 100000) := by
  exact
    packedTile65536 2751361280 2751492352 14 6076 52453 31 _ _ (434707 / 20000) (1086769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751492352 :
    ThetaLowerSegment 2751492352 2751623424 (275142530883661 / 100000)
      (68788908787573 / 25000) := by
  exact
    packedTile65536 2751492352 2751623424 14 6029 52454 31 _ _ (2173539 / 100000) (1086771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751623424 :
    ThetaLowerSegment 2751623424 2751754496 (68788908787573 / 25000) (68792157692467 / 25000) := by
  exact
    packedTile65536 2751623424 2751754496 14 5979 52455 31 _ _ (271693 / 12500) (2173547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751754496 :
    ThetaLowerSegment 2751754496 2751885568 (68792157692467 / 25000) (34397703574111 / 12500) := by
  exact
    packedTile65536 2751754496 2751885568 14 5980 52457 31 _ _ (2173549 / 100000) (135847 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2751885568 :
    ThetaLowerSegment 2751885568 2752016640 (34397703574111 / 12500) (137597364301423 / 50000) := by
  exact
    packedTile65536 2751885568 2752016640 14 6027 52458 31 _ _ (1086777 / 50000) (2173557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752016640 :
    ThetaLowerSegment 2752016640 2752147712 (137597364301423 / 50000)
      (137603917578793 / 50000) := by
  exact
    packedTile65536 2752016640 2752147712 14 6030 52459 31 _ _ (1086779 / 50000) (2173561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752147712 :
    ThetaLowerSegment 2752147712 2752278784 (137603917578793 / 50000) (55044163569877 / 20000) := by
  exact
    packedTile65536 2752147712 2752278784 14 5973 52460 31 _ _ (2173563 / 100000) (1086783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752278784 :
    ThetaLowerSegment 2752278784 2752409856 (55044163569877 / 20000) (55046821843541 / 20000) := by
  exact
    packedTile65536 2752278784 2752409856 14 6115 52462 31 _ _ (67924 / 3125) (2173571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752409856 :
    ThetaLowerSegment 2752409856 2752540928 (55046821843541 / 20000) (68811787120533 / 25000) := by
  exact
    packedTile65536 2752409856 2752540928 14 5999 52463 31 _ _ (2173573 / 100000) (271697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752540928 :
    ThetaLowerSegment 2752540928 2752672000 (68811787120533 / 25000) (68815086611937 / 25000) := by
  exact
    packedTile65536 2752540928 2752672000 14 6072 52464 31 _ _ (1086789 / 50000) (2173581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752672000 :
    ThetaLowerSegment 2752672000 2752803072 (68815086611937 / 25000) (13763675483017 / 5000) := by
  exact
    packedTile65536 2752672000 2752803072 14 6056 52465 31 _ _ (1086791 / 50000) (434717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752803072 :
    ThetaLowerSegment 2752803072 2752934144 (13763675483017 / 5000) (68821676920151 / 25000) := by
  exact
    packedTile65536 2752803072 2752934144 14 6072 52467 31 _ _ (2173587 / 100000) (217359 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2752934144 :
    ThetaLowerSegment 2752934144 2753065216 (68821676920151 / 25000) (68824932960967 / 25000) := by
  exact
    packedTile65536 2752934144 2753065216 14 5992 52468 31 _ _ (271699 / 12500) (434719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753065216 :
    ThetaLowerSegment 2753065216 2753196288 (68824932960967 / 25000) (17207046708919 / 6250) := by
  exact
    packedTile65536 2753065216 2753196288 14 5988 52469 31 _ _ (2173597 / 100000) (2717 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753196288 :
    ThetaLowerSegment 2753196288 2753327360 (17207046708919 / 6250) (275325712872669 / 100000) := by
  exact
    packedTile65536 2753196288 2753327360 14 5965 52470 31 _ _ (2173601 / 100000) (543401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753327360 :
    ThetaLowerSegment 2753327360 2753458432 (275325712872669 / 100000)
      (275338804501607 / 100000) := by
  exact
    packedTile65536 2753327360 2753458432 14 6023 52472 31 _ _ (1086803 / 50000) (2173609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753458432 :
    ThetaLowerSegment 2753458432 2753589504 (275338804501607 / 100000)
      (275352115695371 / 100000) := by
  exact
    packedTile65536 2753458432 2753589504 14 6124 52473 31 _ _ (2173611 / 100000) (1086807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753589504 :
    ThetaLowerSegment 2753589504 2753720576 (275352115695371 / 100000)
      (275365196516459 / 100000) := by
  exact
    packedTile65536 2753589504 2753720576 14 6018 52474 31 _ _ (135851 / 6250) (2173619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753720576 :
    ThetaLowerSegment 2753720576 2753851648 (275365196516459 / 100000)
      (275378146944419 / 100000) := by
  exact
    packedTile65536 2753720576 2753851648 14 5958 52475 31 _ _ (108681 / 5000) (2173623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753851648 :
    ThetaLowerSegment 2753851648 2753982720 (275378146944419 / 100000) (8605976073142 / 3125) := by
  exact
    packedTile65536 2753851648 2753982720 14 6021 52477 31 _ _ (17389 / 800) (543407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2753982720 :
    ThetaLowerSegment 2753982720 2754113792 (8605976073142 / 3125) (34425524733733 / 12500) := by
  exact
    packedTile65536 2753982720 2754113792 14 5964 52478 31 _ _ (217363 / 10000) (2173633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754113792 :
    ThetaLowerSegment 2754113792 2754244864 (34425524733733 / 12500)
      (275417163602639 / 100000) := by
  exact
    packedTile65536 2754113792 2754244864 14 5965 52479 31 _ _ (434727 / 20000) (1086819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754244864 :
    ThetaLowerSegment 2754244864 2754375936 (275417163602639 / 100000)
      (137715125541529 / 50000) := by
  exact
    packedTile65536 2754244864 2754375936 14 6021 52480 31 _ _ (2173639 / 100000) (1086821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754375936 :
    ThetaLowerSegment 2754375936 2754507008 (137715125541529 / 50000)
      (137721771458059 / 50000) := by
  exact
    packedTile65536 2754375936 2754507008 14 6115 52482 31 _ _ (543411 / 25000) (2173647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754507008 :
    ThetaLowerSegment 2754507008 2754638080 (137721771458059 / 50000)
      (137728331530741 / 50000) := by
  exact
    packedTile65536 2754507008 2754638080 14 6036 52483 31 _ _ (2173649 / 100000) (543413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754638080 :
    ThetaLowerSegment 2754638080 2754769152 (137728331530741 / 50000) (17216859957927 / 6250) := by
  exact
    packedTile65536 2754638080 2754769152 14 6025 52484 31 _ _ (1086827 / 50000) (2173657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754769152 :
    ThetaLowerSegment 2754769152 2754900224 (17216859957927 / 6250) (137741425634483 / 50000) := by
  exact
    packedTile65536 2754769152 2754900224 14 6023 52485 31 _ _ (1086829 / 50000) (2173661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2754900224 :
    ThetaLowerSegment 2754900224 2755031296 (137741425634483 / 50000)
      (275496043229713 / 100000) := by
  exact
    packedTile65536 2754900224 2755031296 14 6069 52487 31 _ _ (2173663 / 100000) (1086833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755031296 :
    ThetaLowerSegment 2755031296 2755162368 (275496043229713 / 100000)
      (275509106974393 / 100000) := by
  exact
    packedTile65536 2755031296 2755162368 14 6010 52488 31 _ _ (543417 / 25000) (2173671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755162368 :
    ThetaLowerSegment 2755162368 2755293440 (275509106974393 / 100000)
      (55104440236109 / 20000) := by
  exact
    packedTile65536 2755162368 2755293440 14 6024 52489 31 _ _ (2173673 / 100000) (543419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755293440 :
    ThetaLowerSegment 2755293440 2755424512 (55104440236109 / 20000) (55107052995863 / 20000) := by
  exact
    packedTile65536 2755293440 2755424512 14 6010 52490 31 _ _ (2173677 / 100000) (27171 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755424512 :
    ThetaLowerSegment 2755424512 2755555584 (55107052995863 / 20000) (55109676630037 / 20000) := by
  exact
    packedTile65536 2755424512 2755555584 14 6035 52492 31 _ _ (1086841 / 50000) (434737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755555584 :
    ThetaLowerSegment 2755555584 2755686656 (55109676630037 / 20000) (68890398161521 / 25000) := by
  exact
    packedTile65536 2755555584 2755686656 14 6077 52493 31 _ _ (2173687 / 100000) (217369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755686656 :
    ThetaLowerSegment 2755686656 2755817728 (68890398161521 / 25000) (34446839946509 / 12500) := by
  exact
    packedTile65536 2755686656 2755817728 14 6039 52494 31 _ _ (543423 / 25000) (434739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755817728 :
    ThetaLowerSegment 2755817728 2755948800 (34446839946509 / 12500) (27558779218583 / 10000) := by
  exact
    packedTile65536 2755817728 2755948800 14 6014 52495 31 _ _ (2173697 / 100000) (21737 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2755948800 :
    ThetaLowerSegment 2755948800 2756079872 (27558779218583 / 10000)
      (275600971334993 / 100000) := by
  exact
    packedTile65536 2755948800 2756079872 14 6063 52497 31 _ _ (2173701 / 100000) (271713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756079872 :
    ThetaLowerSegment 2756079872 2756210944 (275600971334993 / 100000)
      (275614352669129 / 100000) := by
  exact
    packedTile65536 2756079872 2756210944 14 6156 52498 31 _ _ (1086853 / 50000) (2173709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756210944 :
    ThetaLowerSegment 2756210944 2756342016 (275614352669129 / 100000)
      (27562746232017 / 10000) := by
  exact
    packedTile65536 2756210944 2756342016 14 6031 52499 31 _ _ (2173711 / 100000) (1086857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756342016 :
    ThetaLowerSegment 2756342016 2756473088 (27562746232017 / 10000) (137820156664581 / 50000) := by
  exact
    packedTile65536 2756342016 2756473088 14 5912 52500 31 _ _ (543429 / 25000) (2173719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756473088 :
    ThetaLowerSegment 2756473088 2756604160 (137820156664581 / 50000)
      (137826784336861 / 50000) := by
  exact
    packedTile65536 2756473088 2756604160 14 6098 52502 31 _ _ (54343 / 2500) (2173723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756604160 :
    ThetaLowerSegment 2756604160 2756735232 (137826784336861 / 50000)
      (137833327249111 / 50000) := by
  exact
    packedTile65536 2756604160 2756735232 14 6020 52503 31 _ _ (86949 / 4000) (67929 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756735232 :
    ThetaLowerSegment 2756735232 2756866304 (137833327249111 / 50000) (17229992059397 / 6250) := by
  exact
    packedTile65536 2756735232 2756866304 14 6081 52504 31 _ _ (217373 / 10000) (2173733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756866304 :
    ThetaLowerSegment 2756866304 2756997376 (17229992059397 / 6250) (68923261446113 / 25000) := by
  exact
    packedTile65536 2756866304 2756997376 14 6060 52505 31 _ _ (434747 / 20000) (1086869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2756997376 :
    ThetaLowerSegment 2756997376 2757128448 (68923261446113 / 25000) (137853120190091 / 50000) := by
  exact
    packedTile65536 2756997376 2757128448 14 6070 52507 31 _ _ (2173739 / 100000) (1086871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757128448 :
    ThetaLowerSegment 2757128448 2757259520 (137853120190091 / 50000)
      (137859712068771 / 50000) := by
  exact
    packedTile65536 2757128448 2757259520 14 6065 52508 31 _ _ (135859 / 6250) (2173747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757259520 :
    ThetaLowerSegment 2757259520 2757390592 (137859712068771 / 50000)
      (275732407940319 / 100000) := by
  exact
    packedTile65536 2757259520 2757390592 14 5973 52509 31 _ _ (2173749 / 100000) (271719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757390592 :
    ThetaLowerSegment 2757390592 2757521664 (275732407940319 / 100000)
      (275745576542051 / 100000) := by
  exact
    packedTile65536 2757390592 2757521664 14 6058 52510 31 _ _ (1086877 / 50000) (2173757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757521664 :
    ThetaLowerSegment 2757521664 2757652736 (275745576542051 / 100000)
      (275758653870179 / 100000) := by
  exact
    packedTile65536 2757521664 2757652736 14 6016 52512 31 _ _ (1086879 / 50000) (2173761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757652736 :
    ThetaLowerSegment 2757652736 2757783808 (275758653870179 / 100000)
      (34471490043221 / 12500) := by
  exact
    packedTile65536 2757652736 2757783808 14 6103 52513 31 _ _ (2173763 / 100000) (1086883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757783808 :
    ThetaLowerSegment 2757783808 2757914880 (34471490043221 / 12500) (17236567928659 / 6250) := by
  exact
    packedTile65536 2757783808 2757914880 14 6057 52514 31 _ _ (271721 / 12500) (2173771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2757914880 :
    ThetaLowerSegment 2757914880 2758045952 (17236567928659 / 6250) (137899040836769 / 50000) := by
  exact
    packedTile65536 2757914880 2758045952 14 5978 52515 31 _ _ (2173773 / 100000) (135861 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758045952 :
    ThetaLowerSegment 2758045952 2758177024 (137899040836769 / 50000)
      (275811174332409 / 100000) := by
  exact
    packedTile65536 2758045952 2758177024 14 6023 52517 31 _ _ (2173777 / 100000) (108689 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758177024 :
    ThetaLowerSegment 2758177024 2758308096 (275811174332409 / 100000)
      (275824293106779 / 100000) := by
  exact
    packedTile65536 2758177024 2758308096 14 6035 52518 31 _ _ (1086891 / 50000) (434757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758308096 :
    ThetaLowerSegment 2758308096 2758439168 (275824293106779 / 100000)
      (137918629873117 / 50000) := by
  exact
    packedTile65536 2758308096 2758439168 14 5965 52519 31 _ _ (2173787 / 100000) (217379 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758439168 :
    ThetaLowerSegment 2758439168 2758570240 (137918629873117 / 50000)
      (137925211028397 / 50000) := by
  exact
    packedTile65536 2758439168 2758570240 14 6055 52520 31 _ _ (67931 / 3125) (434759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758570240 :
    ThetaLowerSegment 2758570240 2758701312 (137925211028397 / 50000)
      (137931671550109 / 50000) := by
  exact
    packedTile65536 2758570240 2758701312 14 5944 52522 31 _ _ (543449 / 25000) (2173799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758701312 :
    ThetaLowerSegment 2758701312 2758832384 (137931671550109 / 50000) (55175315005381 / 20000) := by
  exact
    packedTile65536 2758701312 2758832384 14 6087 52523 31 _ _ (2173801 / 100000) (543451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758832384 :
    ThetaLowerSegment 2758832384 2758963456 (55175315005381 / 20000)
      (275889517867829 / 100000) := by
  exact
    packedTile65536 2758832384 2758963456 14 5954 52524 31 _ _ (1086903 / 50000) (2173809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2758963456 :
    ThetaLowerSegment 2758963456 2759094528 (275889517867829 / 100000)
      (275902643338647 / 100000) := by
  exact
    packedTile65536 2758963456 2759094528 14 6038 52525 31 _ _ (2173811 / 100000) (1086907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759094528 :
    ThetaLowerSegment 2759094528 2759225600 (275902643338647 / 100000)
      (275915781876507 / 100000) := by
  exact
    packedTile65536 2759094528 2759225600 14 6044 52527 31 _ _ (434763 / 20000) (1086909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759225600 :
    ThetaLowerSegment 2759225600 2759356672 (275915781876507 / 100000)
      (275928826970327 / 100000) := by
  exact
    packedTile65536 2759225600 2759356672 14 6001 52528 31 _ _ (108691 / 5000) (2173823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759356672 :
    ThetaLowerSegment 2759356672 2759487744 (275928826970327 / 100000)
      (275941761229077 / 100000) := by
  exact
    packedTile65536 2759356672 2759487744 14 5950 52529 31 _ _ (86953 / 4000) (543457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759487744 :
    ThetaLowerSegment 2759487744 2759618816 (275941761229077 / 100000)
      (275954862902487 / 100000) := by
  exact
    packedTile65536 2759487744 2759618816 14 6027 52530 31 _ _ (217383 / 10000) (2173833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759618816 :
    ThetaLowerSegment 2759618816 2759749888 (275954862902487 / 100000)
      (275967864603641 / 100000) := by
  exact
    packedTile65536 2759618816 2759749888 14 5981 52532 31 _ _ (1086917 / 50000) (2173837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759749888 :
    ThetaLowerSegment 2759749888 2759880960 (275967864603641 / 100000)
      (68995247017421 / 25000) := by
  exact
    packedTile65536 2759749888 2759880960 14 6037 52533 31 _ _ (2173839 / 100000) (1086921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2759880960 :
    ThetaLowerSegment 2759880960 2760012032 (68995247017421 / 25000) (68998508870343 / 25000) := by
  exact
    packedTile65536 2759880960 2760012032 14 6002 52534 31 _ _ (543461 / 25000) (2173847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760012032 :
    ThetaLowerSegment 2760012032 2760143104 (68998508870343 / 25000) (138003580590817 / 50000) := by
  exact
    packedTile65536 2760012032 2760143104 14 6038 52535 31 _ _ (2173849 / 100000) (543463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760143104 :
    ThetaLowerSegment 2760143104 2760274176 (138003580590817 / 50000)
      (276020254298253 / 100000) := by
  exact
    packedTile65536 2760143104 2760274176 14 6023 52537 31 _ _ (2173853 / 100000) (67933 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760274176 :
    ThetaLowerSegment 2760274176 2760405248 (276020254298253 / 100000)
      (276033271359957 / 100000) := by
  exact
    packedTile65536 2760274176 2760405248 14 5988 52538 31 _ _ (1086929 / 50000) (2173861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760405248 :
    ThetaLowerSegment 2760405248 2760536320 (276033271359957 / 100000)
      (276046210192533 / 100000) := by
  exact
    packedTile65536 2760405248 2760536320 14 5952 52539 31 _ _ (2173863 / 100000) (1086933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760536320 :
    ThetaLowerSegment 2760536320 2760667392 (276046210192533 / 100000)
      (276059405571293 / 100000) := by
  exact
    packedTile65536 2760536320 2760667392 14 6070 52540 31 _ _ (543467 / 25000) (2173871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760667392 :
    ThetaLowerSegment 2760667392 2760798464 (276059405571293 / 100000)
      (276072594452717 / 100000) := by
  exact
    packedTile65536 2760667392 2760798464 14 6067 52542 31 _ _ (135867 / 6250) (17391 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760798464 :
    ThetaLowerSegment 2760798464 2760929536 (276072594452717 / 100000)
      (276085750756321 / 100000) := by
  exact
    packedTile65536 2760798464 2760929536 14 6052 52543 31 _ _ (2173877 / 100000) (54347 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2760929536 :
    ThetaLowerSegment 2760929536 2761060608 (276085750756321 / 100000)
      (276099022305931 / 100000) := by
  exact
    packedTile65536 2760929536 2761060608 14 6105 52544 31 _ _ (1086941 / 50000) (434777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761060608 :
    ThetaLowerSegment 2761060608 2761191680 (276099022305931 / 100000)
      (69027959342449 / 25000) := by
  exact
    packedTile65536 2761060608 2761191680 14 5895 52545 31 _ _ (2173887 / 100000) (217389 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761191680 :
    ThetaLowerSegment 2761191680 2761322752 (69027959342449 / 25000)
      (276124695935061 / 100000) := by
  exact
    packedTile65536 2761191680 2761322752 14 5915 52547 31 _ _ (2173891 / 100000) (1086947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761322752 :
    ThetaLowerSegment 2761322752 2761339136 (276124695935061 / 100000)
      (276126352443813 / 100000) := by
  exact
    packedTile65536 2761322752 2761339136 11 762 52548 31 _ _ (271737 / 12500) (2173899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761339136 :
    ThetaLowerSegment 2761339136 2761341184 (276126352443813 / 100000)
      (55225316575379 / 20000) := by
  exact
    packedTile65536 2761339136 2761341184 8 106 52548 31 _ _ (2173897 / 100000) (21739 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2729341184_2761341184 :
    ThetaLowerSegment 2729341184 2761341184 (1705800430283 / 625) (55225316575379 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2729341184 cell2729472256)
                  (ThetaLowerSegment.join cell2729603328 cell2729734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2729865472 cell2729996544)
                  (ThetaLowerSegment.join cell2730127616 cell2730258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2730389760 cell2730520832)
                  (ThetaLowerSegment.join cell2730651904 cell2730782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2730914048 cell2731045120)
                  (ThetaLowerSegment.join cell2731176192 cell2731307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2731438336 cell2731569408)
                  (ThetaLowerSegment.join cell2731700480 cell2731831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2731962624 cell2732093696)
                  (ThetaLowerSegment.join cell2732224768 cell2732355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2732486912 cell2732617984)
                  (ThetaLowerSegment.join cell2732749056 cell2732880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2733011200 cell2733142272)
                  (ThetaLowerSegment.join cell2733273344 cell2733404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2733535488 cell2733666560)
                  (ThetaLowerSegment.join cell2733797632 cell2733928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2734059776 cell2734190848)
                  (ThetaLowerSegment.join cell2734321920 cell2734452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2734584064 cell2734715136)
                  (ThetaLowerSegment.join cell2734846208 cell2734977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2735108352 cell2735239424)
                  (ThetaLowerSegment.join cell2735370496 cell2735501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2735632640 cell2735763712)
                  (ThetaLowerSegment.join cell2735894784 cell2736025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2736156928 cell2736288000)
                  (ThetaLowerSegment.join cell2736419072 cell2736550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2736681216 cell2736812288)
                  (ThetaLowerSegment.join cell2736943360 cell2737074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2737205504 cell2737336576)
                  (ThetaLowerSegment.join cell2737467648 cell2737598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2737729792 cell2737860864)
                  (ThetaLowerSegment.join cell2737991936 cell2738123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2738254080 cell2738385152)
                  (ThetaLowerSegment.join cell2738516224 cell2738647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2738778368 cell2738909440)
                  (ThetaLowerSegment.join cell2739040512 cell2739171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2739302656 cell2739433728)
                  (ThetaLowerSegment.join cell2739564800 cell2739695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2739826944 cell2739958016)
                  (ThetaLowerSegment.join cell2740089088 cell2740220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2740351232 cell2740482304)
                  (ThetaLowerSegment.join cell2740613376 cell2740744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2740875520 cell2741006592)
                  (ThetaLowerSegment.join cell2741137664 cell2741268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2741399808 cell2741530880)
                  (ThetaLowerSegment.join cell2741661952 cell2741793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2741924096 cell2742055168)
                  (ThetaLowerSegment.join cell2742186240 cell2742317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2742448384 cell2742579456)
                  (ThetaLowerSegment.join cell2742710528 cell2742841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2742972672 cell2743103744)
                  (ThetaLowerSegment.join cell2743234816 cell2743365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2743496960 cell2743628032)
                  (ThetaLowerSegment.join cell2743759104 cell2743890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2744021248 cell2744152320)
                  (ThetaLowerSegment.join cell2744283392 cell2744414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2744545536 cell2744676608)
                  (ThetaLowerSegment.join cell2744807680 cell2744938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2745069824 cell2745200896)
                  (ThetaLowerSegment.join cell2745331968 cell2745463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2745594112 cell2745725184)
                  (ThetaLowerSegment.join cell2745856256 cell2745987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2746118400 cell2746249472)
                  (ThetaLowerSegment.join cell2746380544 cell2746511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2746642688 cell2746773760)
                  (ThetaLowerSegment.join cell2746904832 cell2747035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2747166976 cell2747298048)
                  (ThetaLowerSegment.join cell2747429120 cell2747560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2747691264 cell2747822336)
                  (ThetaLowerSegment.join cell2747953408 cell2748084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2748215552 cell2748346624)
                  (ThetaLowerSegment.join cell2748477696 cell2748608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2748739840 cell2748870912)
                  (ThetaLowerSegment.join cell2749001984 cell2749133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2749264128 cell2749395200)
                  (ThetaLowerSegment.join cell2749526272 cell2749657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2749788416 cell2749919488)
                  (ThetaLowerSegment.join cell2750050560 cell2750181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2750312704 cell2750443776)
                  (ThetaLowerSegment.join cell2750574848 cell2750705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2750836992 cell2750968064)
                  (ThetaLowerSegment.join cell2751099136 cell2751230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2751361280 cell2751492352)
                  (ThetaLowerSegment.join cell2751623424 cell2751754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2751885568 cell2752016640)
                  (ThetaLowerSegment.join cell2752147712 cell2752278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2752409856 cell2752540928)
                  (ThetaLowerSegment.join cell2752672000 cell2752803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2752934144 cell2753065216)
                  (ThetaLowerSegment.join cell2753196288 cell2753327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2753458432 cell2753589504)
                  (ThetaLowerSegment.join cell2753720576 cell2753851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2753982720 cell2754113792)
                  (ThetaLowerSegment.join cell2754244864 cell2754375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2754507008 cell2754638080)
                  (ThetaLowerSegment.join cell2754769152 cell2754900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2755031296 cell2755162368)
                  (ThetaLowerSegment.join cell2755293440 cell2755424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2755555584 cell2755686656)
                  (ThetaLowerSegment.join cell2755817728 cell2755948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2756079872 cell2756210944)
                  (ThetaLowerSegment.join cell2756342016 cell2756473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2756604160 cell2756735232)
                  (ThetaLowerSegment.join cell2756866304 cell2756997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2757128448 cell2757259520)
                  (ThetaLowerSegment.join cell2757390592 cell2757521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2757652736 cell2757783808)
                  (ThetaLowerSegment.join cell2757914880 cell2758045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2758177024 cell2758308096)
                  (ThetaLowerSegment.join cell2758439168 cell2758570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2758701312 cell2758832384)
                  (ThetaLowerSegment.join cell2758963456 cell2759094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2759225600 cell2759356672)
                  (ThetaLowerSegment.join cell2759487744 cell2759618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2759749888 cell2759880960)
                  (ThetaLowerSegment.join cell2760012032 cell2760143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2760274176 cell2760405248)
                  (ThetaLowerSegment.join cell2760536320 cell2760667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2760798464 cell2760929536)
                (ThetaLowerSegment.join cell2761060608 cell2761191680))
              (ThetaLowerSegment.join cell2761322752 cell2761339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
