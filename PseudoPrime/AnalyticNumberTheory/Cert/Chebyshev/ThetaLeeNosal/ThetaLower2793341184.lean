/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2793341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2761341184 :
    ThetaLowerSegment 2761341184 2761472256 (55225316575379 / 20000)
      (276139869735359 / 100000) := by
  exact
    packedTile65536 2761341184 2761472256 14 6112 52548 31 _ _ (2173897 / 100000) (21739 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761472256 :
    ThetaLowerSegment 2761472256 2761603328 (276139869735359 / 100000)
      (138076485918343 / 50000) := by
  exact
    packedTile65536 2761472256 2761603328 14 6027 52549 31 _ _ (2173901 / 100000) (135869 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761603328 :
    ThetaLowerSegment 2761603328 2761734400 (138076485918343 / 50000) (34520761963401 / 12500) := by
  exact
    packedTile65536 2761603328 2761734400 14 6037 52550 31 _ _ (1086953 / 50000) (2173909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761734400 :
    ThetaLowerSegment 2761734400 2761865472 (34520761963401 / 12500)
      (276179293520889 / 100000) := by
  exact
    packedTile65536 2761734400 2761865472 14 6071 52552 31 _ _ (2173911 / 100000) (1086957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761865472 :
    ThetaLowerSegment 2761865472 2761996544 (276179293520889 / 100000)
      (276192265277661 / 100000) := by
  exact
    packedTile65536 2761865472 2761996544 14 5967 52553 31 _ _ (543479 / 25000) (2173919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2761996544 :
    ThetaLowerSegment 2761996544 2762127616 (276192265277661 / 100000)
      (276205521841821 / 100000) := by
  exact
    packedTile65536 2761996544 2762127616 14 6098 52554 31 _ _ (13587 / 625) (2173923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762127616 :
    ThetaLowerSegment 2762127616 2762258688 (276205521841821 / 100000)
      (138109366392023 / 50000) := by
  exact
    packedTile65536 2762127616 2762258688 14 6077 52555 31 _ _ (86957 / 4000) (271741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762258688 :
    ThetaLowerSegment 2762258688 2762389760 (138109366392023 / 50000) (69057947895389 / 25000) := by
  exact
    packedTile65536 2762258688 2762389760 14 6007 52557 31 _ _ (217393 / 10000) (2173933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762389760 :
    ThetaLowerSegment 2762389760 2762520832 (69057947895389 / 25000)
      (276244741712351 / 100000) := by
  exact
    packedTile65536 2762389760 2762520832 14 5957 52558 31 _ _ (434787 / 20000) (1086969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762520832 :
    ThetaLowerSegment 2762520832 2762651904 (276244741712351 / 100000) (13812892636923 / 5000) := by
  exact
    packedTile65536 2762520832 2762651904 14 6031 52559 31 _ _ (2173939 / 100000) (1086971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762651904 :
    ThetaLowerSegment 2762651904 2762782976 (13812892636923 / 5000) (69067749644457 / 25000) := by
  exact
    packedTile65536 2762651904 2762782976 14 6047 52560 31 _ _ (271743 / 12500) (2173947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762782976 :
    ThetaLowerSegment 2762782976 2762914048 (69067749644457 / 25000) (17267762968247 / 6250) := by
  exact
    packedTile65536 2762782976 2762914048 14 6076 52562 31 _ _ (2173949 / 100000) (67936 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2762914048 :
    ThetaLowerSegment 2762914048 2763045120 (17267762968247 / 6250) (34537172706649 / 12500) := by
  exact
    packedTile65536 2762914048 2763045120 14 6060 52563 31 _ _ (1086977 / 50000) (2173957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763045120 :
    ThetaLowerSegment 2763045120 2763176192 (34537172706649 / 12500) (69077648742479 / 25000) := by
  exact
    packedTile65536 2763045120 2763176192 14 6078 52564 31 _ _ (1086979 / 50000) (2173961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763176192 :
    ThetaLowerSegment 2763176192 2763307264 (69077648742479 / 25000) (138161834591699 / 50000) := by
  exact
    packedTile65536 2763176192 2763307264 14 6014 52565 31 _ _ (2173963 / 100000) (1086983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763307264 :
    ThetaLowerSegment 2763307264 2763438336 (138161834591699 / 50000)
      (138168473889971 / 50000) := by
  exact
    packedTile65536 2763307264 2763438336 14 6108 52567 31 _ _ (135873 / 6250) (2173971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763438336 :
    ThetaLowerSegment 2763438336 2763569408 (138168473889971 / 50000) (34543742973817 / 12500) := by
  exact
    packedTile65536 2763438336 2763569408 14 5978 52568 31 _ _ (2173973 / 100000) (271747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763569408 :
    ThetaLowerSegment 2763569408 2763700480 (34543742973817 / 12500) (8636343907636 / 3125) := by
  exact
    packedTile65536 2763569408 2763700480 14 6008 52569 31 _ _ (2173977 / 100000) (108699 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763700480 :
    ThetaLowerSegment 2763700480 2763831552 (8636343907636 / 3125) (69094004625151 / 25000) := by
  exact
    packedTile65536 2763700480 2763831552 14 5986 52570 31 _ _ (1086991 / 50000) (434797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763831552 :
    ThetaLowerSegment 2763831552 2763962624 (69094004625151 / 25000) (27638910155437 / 10000) := by
  exact
    packedTile65536 2763831552 2763962624 14 6018 52572 31 _ _ (2173987 / 100000) (217399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2763962624 :
    ThetaLowerSegment 2763962624 2764093696 (27638910155437 / 10000) (138201035795321 / 50000) := by
  exact
    packedTile65536 2763962624 2764093696 14 5966 52573 31 _ _ (271749 / 12500) (434799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764093696 :
    ThetaLowerSegment 2764093696 2764224768 (138201035795321 / 50000)
      (138207595828251 / 50000) := by
  exact
    packedTile65536 2764093696 2764224768 14 6035 52574 31 _ _ (543499 / 25000) (2173999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764224768 :
    ThetaLowerSegment 2764224768 2764355840 (138207595828251 / 50000) (17276770435659 / 6250) := by
  exact
    packedTile65536 2764224768 2764355840 14 6042 52575 31 _ _ (2174001 / 100000) (543501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764355840 :
    ThetaLowerSegment 2764355840 2764486912 (17276770435659 / 6250) (8638795561462 / 3125) := by
  exact
    packedTile65536 2764355840 2764486912 14 6040 52577 31 _ _ (1087003 / 50000) (2174009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764486912 :
    ThetaLowerSegment 2764486912 2764617984 (8638795561462 / 3125) (276454682475697 / 100000) := by
  exact
    packedTile65536 2764486912 2764617984 14 6083 52578 31 _ _ (2174011 / 100000) (1087007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764617984 :
    ThetaLowerSegment 2764617984 2764749056 (276454682475697 / 100000)
      (138233814367511 / 50000) := by
  exact
    packedTile65536 2764617984 2764749056 14 5955 52579 31 _ _ (434803 / 20000) (1087009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764749056 :
    ThetaLowerSegment 2764749056 2764880128 (138233814367511 / 50000)
      (138240295121131 / 50000) := by
  exact
    packedTile65536 2764749056 2764880128 14 5962 52580 31 _ _ (108701 / 5000) (2174023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2764880128 :
    ThetaLowerSegment 2764880128 2765011200 (138240295121131 / 50000) (69123450991553 / 25000) := by
  exact
    packedTile65536 2764880128 2765011200 14 6078 52582 31 _ _ (86961 / 4000) (543507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765011200 :
    ThetaLowerSegment 2765011200 2765142272 (69123450991553 / 25000) (138253416464001 / 50000) := by
  exact
    packedTile65536 2765011200 2765142272 14 5993 52583 31 _ _ (217403 / 10000) (2174033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765142272 :
    ThetaLowerSegment 2765142272 2765273344 (138253416464001 / 50000) (69129937215999 / 25000) := by
  exact
    packedTile65536 2765142272 2765273344 14 5941 52584 31 _ _ (1087017 / 50000) (2174037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765273344 :
    ThetaLowerSegment 2765273344 2765404416 (69129937215999 / 25000)
      (276532938758609 / 100000) := by
  exact
    packedTile65536 2765273344 2765404416 14 6067 52585 31 _ _ (2174039 / 100000) (1087021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765404416 :
    ThetaLowerSegment 2765404416 2765535488 (276532938758609 / 100000)
      (55309230954417 / 20000) := by
  exact
    packedTile65536 2765404416 2765535488 14 6079 52587 31 _ _ (543511 / 25000) (2174047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765535488 :
    ThetaLowerSegment 2765535488 2765666560 (55309230954417 / 20000)
      (276559203414183 / 100000) := by
  exact
    packedTile65536 2765535488 2765666560 14 6002 52588 31 _ _ (2174049 / 100000) (543513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765666560 :
    ThetaLowerSegment 2765666560 2765797632 (276559203414183 / 100000)
      (276572225991653 / 100000) := by
  exact
    packedTile65536 2765666560 2765797632 14 5990 52589 31 _ _ (2174053 / 100000) (271757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765797632 :
    ThetaLowerSegment 2765797632 2765928704 (276572225991653 / 100000)
      (276585309472697 / 100000) := by
  exact
    packedTile65536 2765797632 2765928704 14 6018 52590 31 _ _ (1087029 / 50000) (2174061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2765928704 :
    ThetaLowerSegment 2765928704 2766059776 (276585309472697 / 100000) (5531968424933 / 2000) := by
  exact
    packedTile65536 2765928704 2766059776 14 6031 52592 31 _ _ (2174063 / 100000) (1087033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766059776 :
    ThetaLowerSegment 2766059776 2766190848 (5531968424933 / 2000) (276611598266737 / 100000) := by
  exact
    packedTile65536 2766059776 2766190848 14 6061 52593 31 _ _ (2174067 / 100000) (217407 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766190848 :
    ThetaLowerSegment 2766190848 2766321920 (276611598266737 / 100000)
      (55324938975293 / 20000) := by
  exact
    packedTile65536 2766190848 2766321920 14 6024 52594 31 _ _ (271759 / 12500) (86963 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766321920 :
    ThetaLowerSegment 2766321920 2766452992 (55324938975293 / 20000) (138318914237811 / 50000) := by
  exact
    packedTile65536 2766321920 2766452992 14 6041 52595 31 _ _ (2174077 / 100000) (13588 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766452992 :
    ThetaLowerSegment 2766452992 2766584064 (138318914237811 / 50000)
      (138325412568909 / 50000) := by
  exact
    packedTile65536 2766452992 2766584064 14 5978 52597 31 _ _ (1087041 / 50000) (434817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766584064 :
    ThetaLowerSegment 2766584064 2766715136 (138325412568909 / 50000)
      (138331993527231 / 50000) := by
  exact
    packedTile65536 2766584064 2766715136 14 6054 52598 31 _ _ (1087043 / 50000) (2174089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766715136 :
    ThetaLowerSegment 2766715136 2766846208 (138331993527231 / 50000) (69169263335343 / 25000) := by
  exact
    packedTile65536 2766715136 2766846208 14 6010 52599 31 _ _ (2174091 / 100000) (1087047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766846208 :
    ThetaLowerSegment 2766846208 2766977280 (69169263335343 / 25000) (13834511744271 / 5000) := by
  exact
    packedTile65536 2766846208 2766977280 14 6063 52600 31 _ _ (135881 / 6250) (2174099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2766977280 :
    ThetaLowerSegment 2766977280 2767108352 (13834511744271 / 5000) (442725090651 / 160) := by
  exact
    packedTile65536 2766977280 2767108352 14 5955 52602 31 _ _ (2174101 / 100000) (271763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767108352 :
    ThetaLowerSegment 2767108352 2767239424 (442725090651 / 160) (55343282651981 / 20000) := by
  exact
    packedTile65536 2767108352 2767239424 14 6086 52603 31 _ _ (434821 / 20000) (543527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767239424 :
    ThetaLowerSegment 2767239424 2767370496 (55343282651981 / 20000) (11069182404123 / 4000) := by
  exact
    packedTile65536 2767239424 2767370496 14 6047 52604 31 _ _ (217411 / 10000) (2174113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767370496 :
    ThetaLowerSegment 2767370496 2767501568 (11069182404123 / 4000) (27674269393179 / 10000) := by
  exact
    packedTile65536 2767370496 2767501568 14 6041 52605 31 _ _ (434823 / 20000) (1087059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767501568 :
    ThetaLowerSegment 2767501568 2767632640 (27674269393179 / 10000) (5535116642779 / 2000) := by
  exact
    packedTile65536 2767501568 2767632640 14 6043 52607 31 _ _ (54353 / 2500) (2174123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767632640 :
    ThetaLowerSegment 2767632640 2767763712 (5535116642779 / 2000) (138384364521259 / 50000) := by
  exact
    packedTile65536 2767632640 2767763712 14 5932 52608 31 _ _ (543531 / 25000) (2174127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767763712 :
    ThetaLowerSegment 2767763712 2767894784 (138384364521259 / 50000) (11071278170769 / 4000) := by
  exact
    packedTile65536 2767763712 2767894784 14 6083 52609 31 _ _ (2174129 / 100000) (543533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2767894784 :
    ThetaLowerSegment 2767894784 2768025856 (11071278170769 / 4000) (55359038949057 / 20000) := by
  exact
    packedTile65536 2767894784 2768025856 14 6090 52610 31 _ _ (1087067 / 50000) (2174137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768025856 :
    ThetaLowerSegment 2768025856 2768156928 (55359038949057 / 20000)
      (276808448296629 / 100000) := by
  exact
    packedTile65536 2768025856 2768156928 14 6096 52612 31 _ _ (2174139 / 100000) (1087071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768156928 :
    ThetaLowerSegment 2768156928 2768288000 (276808448296629 / 100000)
      (276821619254923 / 100000) := by
  exact
    packedTile65536 2768156928 2768288000 14 6058 52613 31 _ _ (2174143 / 100000) (1087073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768288000 :
    ThetaLowerSegment 2768288000 2768419072 (276821619254923 / 100000)
      (276834740238103 / 100000) := by
  exact
    packedTile65536 2768288000 2768419072 14 6035 52614 31 _ _ (543537 / 25000) (2174151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768419072 :
    ThetaLowerSegment 2768419072 2768550144 (276834740238103 / 100000)
      (276847763414573 / 100000) := by
  exact
    packedTile65536 2768419072 2768550144 14 5990 52615 31 _ _ (2174153 / 100000) (543539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768550144 :
    ThetaLowerSegment 2768550144 2768681216 (276847763414573 / 100000)
      (138430444400191 / 50000) := by
  exact
    packedTile65536 2768550144 2768681216 14 6037 52617 31 _ _ (2174157 / 100000) (27177 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768681216 :
    ThetaLowerSegment 2768681216 2768812288 (138430444400191 / 50000)
      (138437006021107 / 50000) := by
  exact
    packedTile65536 2768681216 2768812288 14 6036 52618 31 _ _ (1087081 / 50000) (434833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768812288 :
    ThetaLowerSegment 2768812288 2768943360 (138437006021107 / 50000) (34610885935319 / 12500) := by
  exact
    packedTile65536 2768812288 2768943360 14 6014 52619 31 _ _ (2174167 / 100000) (217417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2768943360 :
    ThetaLowerSegment 2768943360 2769074432 (34610885935319 / 12500) (55380063029 / 20) := by
  exact
    packedTile65536 2768943360 2769074432 14 6084 52620 31 _ _ (543543 / 25000) (86967 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769074432 :
    ThetaLowerSegment 2769074432 2769205504 (55380063029 / 20) (34614164317913 / 12500) := by
  exact
    packedTile65536 2769074432 2769205504 14 5979 52621 31 _ _ (67943 / 3125) (2174179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769205504 :
    ThetaLowerSegment 2769205504 2769336576 (34614164317913 / 12500)
      (276926261791159 / 100000) := by
  exact
    packedTile65536 2769205504 2769336576 14 5955 52623 31 _ _ (2174181 / 100000) (271773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769336576 :
    ThetaLowerSegment 2769336576 2769467648 (276926261791159 / 100000)
      (276939411268087 / 100000) := by
  exact
    packedTile65536 2769336576 2769467648 14 6048 52624 31 _ _ (1087093 / 50000) (2174189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769467648 :
    ThetaLowerSegment 2769467648 2769598720 (276939411268087 / 100000)
      (276952552078491 / 100000) := by
  exact
    packedTile65536 2769467648 2769598720 14 6044 52625 31 _ _ (2174191 / 100000) (1087097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769598720 :
    ThetaLowerSegment 2769598720 2769729792 (276952552078491 / 100000)
      (69241444426669 / 25000) := by
  exact
    packedTile65536 2769598720 2769729792 14 6083 52626 31 _ _ (434839 / 20000) (1087099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769729792 :
    ThetaLowerSegment 2769729792 2769860864 (69241444426669 / 25000) (69244745949369 / 25000) := by
  exact
    packedTile65536 2769729792 2769860864 14 6074 52628 31 _ _ (10871 / 500) (2174203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769860864 :
    ThetaLowerSegment 2769860864 2769991936 (69244745949369 / 25000) (69248002908459 / 25000) := by
  exact
    packedTile65536 2769860864 2769991936 14 5992 52629 31 _ _ (434841 / 20000) (67944 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2769991936 :
    ThetaLowerSegment 2769991936 2770123008 (69248002908459 / 25000) (34625625045547 / 12500) := by
  exact
    packedTile65536 2769991936 2770123008 14 5974 52630 31 _ _ (217421 / 10000) (2174213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770123008 :
    ThetaLowerSegment 2770123008 2770254080 (34625625045547 / 12500) (17313628396577 / 6250) := by
  exact
    packedTile65536 2770123008 2770254080 14 6004 52631 31 _ _ (1087107 / 50000) (2174217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770254080 :
    ThetaLowerSegment 2770254080 2770385152 (17313628396577 / 6250) (69257764043713 / 25000) := by
  exact
    packedTile65536 2770254080 2770385152 14 5980 52633 31 _ _ (2174219 / 100000) (1087111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770385152 :
    ThetaLowerSegment 2770385152 2770516224 (69257764043713 / 25000) (69261056905961 / 25000) := by
  exact
    packedTile65536 2770385152 2770516224 14 6058 52634 31 _ _ (135889 / 6250) (2174227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770516224 :
    ThetaLowerSegment 2770516224 2770647296 (69261056905961 / 25000) (69264350861381 / 25000) := by
  exact
    packedTile65536 2770516224 2770647296 14 6060 52635 31 _ _ (543557 / 25000) (2174231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770647296 :
    ThetaLowerSegment 2770647296 2770778368 (69264350861381 / 25000) (27707054016131 / 10000) := by
  exact
    packedTile65536 2770647296 2770778368 14 6042 52636 31 _ _ (2174233 / 100000) (543559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770778368 :
    ThetaLowerSegment 2770778368 2770909440 (27707054016131 / 10000) (27708371604359 / 10000) := by
  exact
    packedTile65536 2770778368 2770909440 14 6060 52638 31 _ _ (1087119 / 50000) (2174241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2770909440 :
    ThetaLowerSegment 2770909440 2771040512 (27708371604359 / 10000) (138548441629599 / 50000) := by
  exact
    packedTile65536 2770909440 2771040512 14 6056 52639 31 _ _ (2174243 / 100000) (1087123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771040512 :
    ThetaLowerSegment 2771040512 2771171584 (138548441629599 / 50000)
      (277110161385627 / 100000) := by
  exact
    packedTile65536 2771040512 2771171584 14 6107 52640 31 _ _ (2174247 / 100000) (8697 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771171584 :
    ThetaLowerSegment 2771171584 2771302656 (277110161385627 / 100000)
      (277123448239599 / 100000) := by
  exact
    packedTile65536 2771171584 2771302656 14 6111 52641 31 _ _ (543563 / 25000) (434851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771302656 :
    ThetaLowerSegment 2771302656 2771433728 (277123448239599 / 100000)
      (277136515524169 / 100000) := by
  exact
    packedTile65536 2771302656 2771433728 14 6010 52643 31 _ _ (2174257 / 100000) (108713 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771433728 :
    ThetaLowerSegment 2771433728 2771564800 (277136515524169 / 100000)
      (277149661112221 / 100000) := by
  exact
    packedTile65536 2771433728 2771564800 14 6046 52644 31 _ _ (1087131 / 50000) (434853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771564800 :
    ThetaLowerSegment 2771564800 2771695872 (277149661112221 / 100000)
      (55432566997983 / 20000) := by
  exact
    packedTile65536 2771564800 2771695872 14 6059 52645 31 _ _ (1087133 / 50000) (2174269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771695872 :
    ThetaLowerSegment 2771695872 2771826944 (55432566997983 / 20000) (138588045760101 / 50000) := by
  exact
    packedTile65536 2771695872 2771826944 14 6097 52646 31 _ _ (2174271 / 100000) (1087137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771826944 :
    ThetaLowerSegment 2771826944 2771958016 (138588045760101 / 50000) (27718900237109 / 10000) := by
  exact
    packedTile65536 2771826944 2771958016 14 5938 52648 31 _ _ (543569 / 25000) (2174279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2771958016 :
    ThetaLowerSegment 2771958016 2772089088 (27718900237109 / 10000) (27720220025069 / 10000) := by
  exact
    packedTile65536 2771958016 2772089088 14 6070 52649 31 _ _ (54357 / 2500) (2174283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772089088 :
    ThetaLowerSegment 2772089088 2772220160 (27720220025069 / 10000) (55443042669283 / 20000) := by
  exact
    packedTile65536 2772089088 2772220160 14 5985 52650 31 _ _ (434857 / 20000) (135893 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772220160 :
    ThetaLowerSegment 2772220160 2772351232 (55443042669283 / 20000) (2217826925013 / 800) := by
  exact
    packedTile65536 2772220160 2772351232 14 6049 52651 31 _ _ (217429 / 10000) (2174293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772351232 :
    ThetaLowerSegment 2772351232 2772482304 (2217826925013 / 800) (27724160925747 / 10000) := by
  exact
    packedTile65536 2772351232 2772482304 14 6091 52653 31 _ _ (434859 / 20000) (1087149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772482304 :
    ThetaLowerSegment 2772482304 2772613376 (27724160925747 / 10000) (34656848732251 / 12500) := by
  exact
    packedTile65536 2772482304 2772613376 14 6062 52654 31 _ _ (2174299 / 100000) (1087151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772613376 :
    ThetaLowerSegment 2772613376 2772744448 (34656848732251 / 12500) (34658489516407 / 12500) := by
  exact
    packedTile65536 2772613376 2772744448 14 6037 52655 31 _ _ (67947 / 3125) (2174307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772744448 :
    ThetaLowerSegment 2772744448 2772875520 (34658489516407 / 12500) (11091237696659 / 4000) := by
  exact
    packedTile65536 2772744448 2772875520 14 5991 52656 31 _ _ (2174309 / 100000) (271789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2772875520 :
    ThetaLowerSegment 2772875520 2773006592 (11091237696659 / 4000) (55458810705979 / 20000) := by
  exact
    packedTile65536 2772875520 2773006592 14 6030 52658 31 _ _ (1087157 / 50000) (2174317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773006592 :
    ThetaLowerSegment 2773006592 2773137664 (55458810705979 / 20000)
      (277307271209017 / 100000) := by
  exact
    packedTile65536 2773006592 2773137664 14 6079 52659 31 _ _ (1087159 / 50000) (2174321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773137664 :
    ThetaLowerSegment 2773137664 2773268736 (277307271209017 / 100000)
      (277320369330769 / 100000) := by
  exact
    packedTile65536 2773137664 2773268736 14 6024 52660 31 _ _ (2174323 / 100000) (1087163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773268736 :
    ThetaLowerSegment 2773268736 2773399808 (277320369330769 / 100000)
      (277333415298769 / 100000) := by
  exact
    packedTile65536 2773268736 2773399808 14 6000 52661 31 _ _ (271791 / 12500) (2174331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773399808 :
    ThetaLowerSegment 2773399808 2773530880 (277333415298769 / 100000)
      (277346556961377 / 100000) := by
  exact
    packedTile65536 2773399808 2773530880 14 6044 52663 31 _ _ (543583 / 25000) (434867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773530880 :
    ThetaLowerSegment 2773530880 2773661952 (277346556961377 / 100000)
      (277359781279011 / 100000) := by
  exact
    packedTile65536 2773530880 2773661952 14 6082 52664 31 _ _ (2174337 / 100000) (108717 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773661952 :
    ThetaLowerSegment 2773661952 2773793024 (277359781279011 / 100000)
      (277372833854037 / 100000) := by
  exact
    packedTile65536 2773661952 2773793024 14 6003 52665 31 _ _ (1087171 / 50000) (434869 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773793024 :
    ThetaLowerSegment 2773793024 2773924096 (277372833854037 / 100000)
      (277385753823911 / 100000) := by
  exact
    packedTile65536 2773793024 2773924096 14 5942 52666 31 _ _ (2174347 / 100000) (43487 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2773924096 :
    ThetaLowerSegment 2773924096 2774055168 (277385753823911 / 100000)
      (34674854068147 / 12500) := by
  exact
    packedTile65536 2773924096 2774055168 14 6015 52668 31 _ _ (2174351 / 100000) (1087177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774055168 :
    ThetaLowerSegment 2774055168 2774186240 (34674854068147 / 12500) (69352983260019 / 25000) := by
  exact
    packedTile65536 2774055168 2774186240 14 6025 52669 31 _ _ (543589 / 25000) (2174359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774186240 :
    ThetaLowerSegment 2774186240 2774317312 (69352983260019 / 25000)
      (277424959636827 / 100000) := by
  exact
    packedTile65536 2774186240 2774317312 14 5991 52670 31 _ _ (2174361 / 100000) (543591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774317312 :
    ThetaLowerSegment 2774317312 2774448384 (277424959636827 / 100000)
      (277438223269427 / 100000) := by
  exact
    packedTile65536 2774317312 2774448384 14 6100 52671 31 _ _ (1087183 / 50000) (2174369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774448384 :
    ThetaLowerSegment 2774448384 2774579456 (277438223269427 / 100000)
      (277451241222617 / 100000) := by
  exact
    packedTile65536 2774448384 2774579456 14 5987 52673 31 _ _ (217437 / 10000) (2174373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774579456 :
    ThetaLowerSegment 2774579456 2774710528 (277451241222617 / 100000)
      (69366065888623 / 25000) := by
  exact
    packedTile65536 2774579456 2774710528 14 5989 52674 31 _ _ (3479 / 160) (1087189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774710528 :
    ThetaLowerSegment 2774710528 2774841600 (69366065888623 / 25000) (69369364423083 / 25000) := by
  exact
    packedTile65536 2774710528 2774841600 14 6068 52675 31 _ _ (108719 / 5000) (2174383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774841600 :
    ThetaLowerSegment 2774841600 2774972672 (69369364423083 / 25000) (69372637414599 / 25000) := by
  exact
    packedTile65536 2774841600 2774972672 14 6021 52676 31 _ _ (135899 / 6250) (2174387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2774972672 :
    ThetaLowerSegment 2774972672 2775103744 (69372637414599 / 25000) (138751834960811 / 50000) := by
  exact
    packedTile65536 2774972672 2775103744 14 6034 52678 31 _ _ (2174389 / 100000) (271799 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775103744 :
    ThetaLowerSegment 2775103744 2775234816 (138751834960811 / 50000)
      (138758364665993 / 50000) := by
  exact
    packedTile65536 2775103744 2775234816 14 6006 52679 31 _ _ (1087197 / 50000) (2174397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775234816 :
    ThetaLowerSegment 2775234816 2775365888 (138758364665993 / 50000) (55505968626471 / 20000) := by
  exact
    packedTile65536 2775234816 2775365888 14 6031 52680 31 _ _ (2174399 / 100000) (1087201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775365888 :
    ThetaLowerSegment 2775365888 2775496960 (55505968626471 / 20000) (138771489350439 / 50000) := by
  exact
    packedTile65536 2775365888 2775496960 14 6041 52681 31 _ _ (2174403 / 100000) (1087203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775496960 :
    ThetaLowerSegment 2775496960 2775628032 (138771489350439 / 50000)
      (138778035405723 / 50000) := by
  exact
    packedTile65536 2775496960 2775628032 14 6021 52682 31 _ _ (271801 / 12500) (2174411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775628032 :
    ThetaLowerSegment 2775628032 2775759104 (138778035405723 / 50000)
      (277569158603293 / 100000) := by
  exact
    packedTile65536 2775628032 2775759104 14 6019 52684 31 _ _ (2174413 / 100000) (135901 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775759104 :
    ThetaLowerSegment 2775759104 2775890176 (277569158603293 / 100000)
      (277582198588039 / 100000) := by
  exact
    packedTile65536 2775759104 2775890176 14 5997 52685 31 _ _ (1087209 / 50000) (2174421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2775890176 :
    ThetaLowerSegment 2775890176 2776021248 (277582198588039 / 100000)
      (55519048154239 / 20000) := by
  exact
    packedTile65536 2775890176 2776021248 14 5998 52686 31 _ _ (1087211 / 50000) (86977 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776021248 :
    ThetaLowerSegment 2776021248 2776152320 (55519048154239 / 20000) (138804188242351 / 50000) := by
  exact
    packedTile65536 2776021248 2776152320 14 6041 52687 31 _ _ (2174427 / 100000) (217443 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776152320 :
    ThetaLowerSegment 2776152320 2776283392 (138804188242351 / 50000)
      (138810727846591 / 50000) := by
  exact
    packedTile65536 2776152320 2776283392 14 6015 52689 31 _ _ (67951 / 3125) (434887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776283392 :
    ThetaLowerSegment 2776283392 2776414464 (138810727846591 / 50000)
      (138817284858349 / 50000) := by
  exact
    packedTile65536 2776283392 2776414464 14 6031 52690 31 _ _ (543609 / 25000) (2174439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776414464 :
    ThetaLowerSegment 2776414464 2776545536 (138817284858349 / 50000)
      (277647905563351 / 100000) := by
  exact
    packedTile65536 2776414464 2776545536 14 6133 52691 31 _ _ (2174441 / 100000) (543611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776545536 :
    ThetaLowerSegment 2776545536 2776676608 (277647905563351 / 100000)
      (277661117497247 / 100000) := by
  exact
    packedTile65536 2776545536 2776676608 14 6076 52692 31 _ _ (1087223 / 50000) (2174449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776676608 :
    ThetaLowerSegment 2776676608 2776807680 (277661117497247 / 100000) (11106964654613 / 4000) := by
  exact
    packedTile65536 2776676608 2776807680 14 5978 52694 31 _ _ (2174451 / 100000) (1087227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776807680 :
    ThetaLowerSegment 2776807680 2776938752 (11106964654613 / 4000) (13884366091527 / 5000) := by
  exact
    packedTile65536 2776807680 2776938752 14 6073 52695 31 _ _ (434891 / 20000) (1087229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2776938752 :
    ThetaLowerSegment 2776938752 2777069824 (13884366091527 / 5000) (13885023865677 / 5000) := by
  exact
    packedTile65536 2776938752 2777069824 14 6050 52696 31 _ _ (108723 / 5000) (2174463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777069824 :
    ThetaLowerSegment 2777069824 2777200896 (13885023865677 / 5000) (1110854044227 / 400) := by
  exact
    packedTile65536 2777069824 2777200896 14 5994 52697 31 _ _ (434893 / 20000) (543617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777200896 :
    ThetaLowerSegment 2777200896 2777331968 (1110854044227 / 400) (55545352889061 / 20000) := by
  exact
    packedTile65536 2777200896 2777331968 14 6095 52699 31 _ _ (2174469 / 100000) (271809 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777331968 :
    ThetaLowerSegment 2777331968 2777463040 (55545352889061 / 20000) (55547977479179 / 20000) := by
  exact
    packedTile65536 2777331968 2777463040 14 6035 52700 31 _ _ (1087237 / 50000) (2174477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777463040 :
    ThetaLowerSegment 2777463040 2777594112 (55547977479179 / 20000) (5555060642429 / 2000) := by
  exact
    packedTile65536 2777463040 2777594112 14 6045 52701 31 _ _ (2174479 / 100000) (1087241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777594112 :
    ThetaLowerSegment 2777594112 2777725184 (5555060642429 / 2000) (138883091700341 / 50000) := by
  exact
    packedTile65536 2777594112 2777725184 14 6048 52702 31 _ _ (543621 / 25000) (2174487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777725184 :
    ThetaLowerSegment 2777725184 2777856256 (138883091700341 / 50000)
      (138889617338829 / 50000) := by
  exact
    packedTile65536 2777725184 2777856256 14 6002 52704 31 _ _ (271811 / 12500) (2174491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777856256 :
    ThetaLowerSegment 2777856256 2777987328 (138889617338829 / 50000) (69448062798189 / 25000) := by
  exact
    packedTile65536 2777856256 2777987328 14 5986 52705 31 _ _ (2174493 / 100000) (67953 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2777987328 :
    ThetaLowerSegment 2777987328 2778118400 (69448062798189 / 25000) (138902621909153 / 50000) := by
  exact
    packedTile65536 2777987328 2778118400 14 5975 52706 31 _ _ (1087249 / 50000) (2174501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778118400 :
    ThetaLowerSegment 2778118400 2778249472 (138902621909153 / 50000) (27781838215939 / 10000) := by
  exact
    packedTile65536 2778118400 2778249472 14 6042 52707 31 _ _ (1087251 / 50000) (434901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778249472 :
    ThetaLowerSegment 2778249472 2778380544 (27781838215939 / 10000) (34728941153589 / 12500) := by
  exact
    packedTile65536 2778249472 2778380544 14 6046 52709 31 _ _ (2174507 / 100000) (217451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778380544 :
    ThetaLowerSegment 2778380544 2778511616 (34728941153589 / 12500) (34730568504007 / 12500) := by
  exact
    packedTile65536 2778380544 2778511616 14 5987 52710 31 _ _ (135907 / 6250) (434903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778511616 :
    ThetaLowerSegment 2778511616 2778642688 (34730568504007 / 12500)
      (277857606006641 / 100000) := by
  exact
    packedTile65536 2778511616 2778642688 14 6005 52711 31 _ _ (2174517 / 100000) (54363 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778642688 :
    ThetaLowerSegment 2778642688 2778773760 (277857606006641 / 100000)
      (277870744462523 / 100000) := by
  exact
    packedTile65536 2778642688 2778773760 14 6042 52712 31 _ _ (2174521 / 100000) (543631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778773760 :
    ThetaLowerSegment 2778773760 2778904832 (277870744462523 / 100000)
      (277883982976811 / 100000) := by
  exact
    packedTile65536 2778773760 2778904832 14 6088 52714 31 _ _ (1087263 / 50000) (2174529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2778904832 :
    ThetaLowerSegment 2778904832 2779035904 (277883982976811 / 100000) (6947425699707 / 2500) := by
  exact
    packedTile65536 2778904832 2779035904 14 5999 52715 31 _ _ (2174531 / 100000) (1087267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779035904 :
    ThetaLowerSegment 2779035904 2779166976 (6947425699707 / 2500) (1389550723917 / 500) := by
  exact
    packedTile65536 2779035904 2779166976 14 6032 52716 31 _ _ (434907 / 20000) (1087269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779166976 :
    ThetaLowerSegment 2779166976 2779298048 (1389550723917 / 500) (55584655801 / 20) := by
  exact
    packedTile65536 2779166976 2779298048 14 6040 52717 31 _ _ (108727 / 5000) (2174543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779298048 :
    ThetaLowerSegment 2779298048 2779429120 (55584655801 / 20) (13896812399569 / 5000) := by
  exact
    packedTile65536 2779298048 2779429120 14 5964 52719 31 _ _ (434909 / 20000) (543637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779429120 :
    ThetaLowerSegment 2779429120 2779560192 (13896812399569 / 5000) (3474366462961 / 1250) := by
  exact
    packedTile65536 2779429120 2779560192 14 6010 52720 31 _ _ (43491 / 2000) (2174553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779560192 :
    ThetaLowerSegment 2779560192 2779691264 (3474366462961 / 1250) (138981291995417 / 50000) := by
  exact
    packedTile65536 2779560192 2779691264 14 6101 52721 31 _ _ (1087277 / 50000) (2174557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779691264 :
    ThetaLowerSegment 2779691264 2779822336 (138981291995417 / 50000) (69493950240109 / 25000) := by
  exact
    packedTile65536 2779691264 2779822336 14 6078 52722 31 _ _ (2174559 / 100000) (1087281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779822336 :
    ThetaLowerSegment 2779822336 2779953408 (69493950240109 / 25000) (69497210998827 / 25000) := by
  exact
    packedTile65536 2779822336 2779953408 14 5998 52724 31 _ _ (543641 / 25000) (2174567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2779953408 :
    ThetaLowerSegment 2779953408 2780084480 (69497210998827 / 25000) (13900101964 / 5) := by
  exact
    packedTile65536 2779953408 2780084480 14 6068 52725 31 _ _ (2174569 / 100000) (543643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780084480 :
    ThetaLowerSegment 2780084480 2780215552 (13900101964 / 5) (139007528136989 / 50000) := by
  exact
    packedTile65536 2780084480 2780215552 14 5986 52726 31 _ _ (2174573 / 100000) (135911 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780215552 :
    ThetaLowerSegment 2780215552 2780346624 (139007528136989 / 50000) (69507046050341 / 25000) := by
  exact
    packedTile65536 2780215552 2780346624 14 6037 52727 31 _ _ (1087289 / 50000) (2174581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780346624 :
    ThetaLowerSegment 2780346624 2780477696 (69507046050341 / 25000) (5560826460637 / 2000) := by
  exact
    packedTile65536 2780346624 2780477696 14 6042 52728 31 _ _ (2174583 / 100000) (1087293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780477696 :
    ThetaLowerSegment 2780477696 2780608768 (5560826460637 / 2000) (55610880634531 / 20000) := by
  exact
    packedTile65536 2780477696 2780608768 14 6015 52730 31 _ _ (2174587 / 100000) (217459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780608768 :
    ThetaLowerSegment 2780608768 2780739840 (55610880634531 / 20000) (55613498843299 / 20000) := by
  exact
    packedTile65536 2780608768 2780739840 14 6020 52731 31 _ _ (67956 / 3125) (434919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780739840 :
    ThetaLowerSegment 2780739840 2780870912 (55613498843299 / 20000)
      (278080402624287 / 100000) := by
  exact
    packedTile65536 2780739840 2780870912 14 5936 52732 31 _ _ (2174597 / 100000) (10873 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2780870912 :
    ThetaLowerSegment 2780870912 2781001984 (278080402624287 / 100000)
      (69523395720237 / 25000) := by
  exact
    packedTile65536 2780870912 2781001984 14 6061 52733 31 _ _ (2174601 / 100000) (543651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781001984 :
    ThetaLowerSegment 2781001984 2781133056 (69523395720237 / 25000) (34763308699513 / 12500) := by
  exact
    packedTile65536 2781001984 2781133056 14 5926 52735 31 _ _ (1087303 / 50000) (2174609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781133056 :
    ThetaLowerSegment 2781133056 2781264128 (34763308699513 / 12500) (34764957054651 / 12500) := by
  exact
    packedTile65536 2781133056 2781264128 14 6064 52736 31 _ _ (2174611 / 100000) (1087307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781264128 :
    ThetaLowerSegment 2781264128 2781395200 (34764957054651 / 12500) (34766614655697 / 12500) := by
  exact
    packedTile65536 2781264128 2781395200 14 6098 52737 31 _ _ (271827 / 12500) (2174619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781395200 :
    ThetaLowerSegment 2781395200 2781526272 (34766614655697 / 12500) (69536517880489 / 25000) := by
  exact
    packedTile65536 2781395200 2781526272 14 6049 52738 31 _ _ (108731 / 5000) (2174623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781526272 :
    ThetaLowerSegment 2781526272 2781657344 (69536517880489 / 25000) (34769895345557 / 12500) := by
  exact
    packedTile65536 2781526272 2781657344 14 6020 52740 31 _ _ (17397 / 800) (543657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781657344 :
    ThetaLowerSegment 2781657344 2781788416 (34769895345557 / 12500) (139086204217893 / 50000) := by
  exact
    packedTile65536 2781657344 2781788416 14 6091 52741 31 _ _ (217463 / 10000) (2174633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781788416 :
    ThetaLowerSegment 2781788416 2781919488 (139086204217893 / 50000) (27818546928759 / 10000) := by
  exact
    packedTile65536 2781788416 2781919488 14 6006 52742 31 _ _ (1087317 / 50000) (2174637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2781919488 :
    ThetaLowerSegment 2781919488 2782050560 (27818546928759 / 10000) (6954964559019 / 2500) := by
  exact
    packedTile65536 2781919488 2782050560 14 6030 52743 31 _ _ (2174639 / 100000) (1087321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782050560 :
    ThetaLowerSegment 2782050560 2782181632 (6954964559019 / 2500) (8694113036778 / 3125) := by
  exact
    packedTile65536 2782050560 2782181632 14 5994 52745 31 _ _ (543661 / 25000) (2174647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782181632 :
    ThetaLowerSegment 2782181632 2782312704 (8694113036778 / 3125) (139112343408693 / 50000) := by
  exact
    packedTile65536 2782181632 2782312704 14 6010 52746 31 _ _ (2174649 / 100000) (543663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782312704 :
    ThetaLowerSegment 2782312704 2782443776 (139112343408693 / 50000) (69559430421867 / 25000) := by
  exact
    packedTile65536 2782312704 2782443776 14 5994 52747 31 _ _ (2174653 / 100000) (67958 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782443776 :
    ThetaLowerSegment 2782443776 2782574848 (69559430421867 / 25000) (139125442446171 / 50000) := by
  exact
    packedTile65536 2782443776 2782574848 14 6053 52748 31 _ _ (1087329 / 50000) (2174661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782574848 :
    ThetaLowerSegment 2782574848 2782705920 (139125442446171 / 50000)
      (278263921997027 / 100000) := by
  exact
    packedTile65536 2782574848 2782705920 14 5995 52750 31 _ _ (2174663 / 100000) (1087333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782705920 :
    ThetaLowerSegment 2782705920 2782836992 (278263921997027 / 100000)
      (278277039588371 / 100000) := by
  exact
    packedTile65536 2782705920 2782836992 14 6032 52751 31 _ _ (2174667 / 100000) (217467 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782836992 :
    ThetaLowerSegment 2782836992 2782968064 (278277039588371 / 100000)
      (55658051014023 / 20000) := by
  exact
    packedTile65536 2782836992 2782968064 14 6077 52752 31 _ _ (135917 / 6250) (86987 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2782968064 :
    ThetaLowerSegment 2782968064 2783099136 (55658051014023 / 20000)
      (278303333577593 / 100000) := by
  exact
    packedTile65536 2782968064 2783099136 14 6014 52753 31 _ _ (2174677 / 100000) (54367 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783099136 :
    ThetaLowerSegment 2783099136 2783230208 (278303333577593 / 100000)
      (278316477355601 / 100000) := by
  exact
    packedTile65536 2783099136 2783230208 14 6044 52755 31 _ _ (1087341 / 50000) (434937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783230208 :
    ThetaLowerSegment 2783230208 2783361280 (278316477355601 / 100000)
      (278329564615949 / 100000) := by
  exact
    packedTile65536 2783230208 2783361280 14 6018 52756 31 _ _ (1087343 / 50000) (2174689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783361280 :
    ThetaLowerSegment 2783361280 2783492352 (278329564615949 / 100000)
      (278342721496499 / 100000) := by
  exact
    packedTile65536 2783361280 2783492352 14 6050 52757 31 _ _ (2174691 / 100000) (1087347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783492352 :
    ThetaLowerSegment 2783492352 2783623424 (278342721496499 / 100000)
      (55671152194743 / 20000) := by
  exact
    packedTile65536 2783492352 2783623424 14 5996 52758 31 _ _ (271837 / 12500) (2174699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783623424 :
    ThetaLowerSegment 2783623424 2783754496 (55671152194743 / 20000) (55673758790163 / 20000) := by
  exact
    packedTile65536 2783623424 2783754496 14 5993 52760 31 _ _ (21747 / 1000) (2174703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783754496 :
    ThetaLowerSegment 2783754496 2783885568 (55673758790163 / 20000) (55676375395219 / 20000) := by
  exact
    packedTile65536 2783754496 2783885568 14 6016 52761 31 _ _ (434941 / 20000) (543677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2783885568 :
    ThetaLowerSegment 2783885568 2784016640 (55676375395219 / 20000) (55678994181001 / 20000) := by
  exact
    packedTile65536 2783885568 2784016640 14 6021 52762 31 _ _ (217471 / 10000) (2174713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784016640 :
    ThetaLowerSegment 2784016640 2784147712 (55678994181001 / 20000) (5568163124041 / 2000) := by
  exact
    packedTile65536 2784016640 2784147712 14 6063 52763 31 _ _ (434943 / 20000) (1087359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784147712 :
    ThetaLowerSegment 2784147712 2784278784 (5568163124041 / 2000) (278421311077281 / 100000) := by
  exact
    packedTile65536 2784147712 2784278784 14 6049 52765 31 _ _ (2174719 / 100000) (1087361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784278784 :
    ThetaLowerSegment 2784278784 2784409856 (278421311077281 / 100000)
      (278434385517969 / 100000) := by
  exact
    packedTile65536 2784278784 2784409856 14 6012 52766 31 _ _ (543681 / 25000) (2174727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784409856 :
    ThetaLowerSegment 2784409856 2784540928 (278434385517969 / 100000)
      (278447394746847 / 100000) := by
  exact
    packedTile65536 2784409856 2784540928 14 5982 52767 31 _ _ (2174729 / 100000) (543683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784540928 :
    ThetaLowerSegment 2784540928 2784672000 (278447394746847 / 100000) (1113841694289 / 400) := by
  exact
    packedTile65536 2784540928 2784672000 14 5991 52768 31 _ _ (2174733 / 100000) (135921 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784672000 :
    ThetaLowerSegment 2784672000 2784803072 (1113841694289 / 400) (139236685981151 / 50000) := by
  exact
    packedTile65536 2784672000 2784803072 14 5954 52769 31 _ _ (1087369 / 50000) (2174741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784803072 :
    ThetaLowerSegment 2784803072 2784934144 (139236685981151 / 50000) (55697284519009 / 20000) := by
  exact
    packedTile65536 2784803072 2784934144 14 6001 52771 31 _ _ (2174743 / 100000) (1087373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2784934144 :
    ThetaLowerSegment 2784934144 2785065216 (55697284519009 / 20000)
      (278499571121453 / 100000) := by
  exact
    packedTile65536 2784934144 2785065216 14 6046 52772 31 _ _ (543687 / 25000) (2174751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785065216 :
    ThetaLowerSegment 2785065216 2785196288 (278499571121453 / 100000)
      (278512726196301 / 100000) := by
  exact
    packedTile65536 2785065216 2785196288 14 6049 52773 31 _ _ (67961 / 3125) (434951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785196288 :
    ThetaLowerSegment 2785196288 2785327360 (278512726196301 / 100000)
      (278525892175179 / 100000) := by
  exact
    packedTile65536 2785196288 2785327360 14 6054 52774 31 _ _ (2174757 / 100000) (54369 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785327360 :
    ThetaLowerSegment 2785327360 2785458432 (278525892175179 / 100000)
      (278539019038611 / 100000) := by
  exact
    packedTile65536 2785327360 2785458432 14 6036 52776 31 _ _ (1087381 / 50000) (434953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785458432 :
    ThetaLowerSegment 2785458432 2785589504 (278539019038611 / 100000)
      (278552254664487 / 100000) := by
  exact
    packedTile65536 2785458432 2785589504 14 6086 52777 31 _ _ (1087383 / 50000) (2174769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785589504 :
    ThetaLowerSegment 2785589504 2785720576 (278552254664487 / 100000) (5571308371067 / 2000) := by
  exact
    packedTile65536 2785589504 2785720576 14 6053 52778 31 _ _ (2174771 / 100000) (1087387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785720576 :
    ThetaLowerSegment 2785720576 2785851648 (5571308371067 / 2000) (139289223818183 / 50000) := by
  exact
    packedTile65536 2785720576 2785851648 14 5991 52779 31 _ _ (271847 / 12500) (2174779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785851648 :
    ThetaLowerSegment 2785851648 2785982720 (139289223818183 / 50000)
      (139295780779883 / 50000) := by
  exact
    packedTile65536 2785851648 2785982720 14 6030 52781 31 _ _ (108739 / 5000) (2174783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2785982720 :
    ThetaLowerSegment 2785982720 2786113792 (139295780779883 / 50000) (17412789501101 / 6250) := by
  exact
    packedTile65536 2785982720 2786113792 14 6010 52782 31 _ _ (434957 / 20000) (543697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786113792 :
    ThetaLowerSegment 2786113792 2786244864 (17412789501101 / 6250) (69654458248229 / 25000) := by
  exact
    packedTile65536 2786113792 2786244864 14 6070 52783 31 _ _ (217479 / 10000) (2174793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786244864 :
    ThetaLowerSegment 2786244864 2786375936 (69654458248229 / 25000)
      (278630940482381 / 100000) := by
  exact
    packedTile65536 2786244864 2786375936 14 6027 52784 31 _ _ (434959 / 20000) (1087399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786375936 :
    ThetaLowerSegment 2786375936 2786507008 (278630940482381 / 100000)
      (278643989276381 / 100000) := by
  exact
    packedTile65536 2786375936 2786507008 14 6000 52786 31 _ _ (2174799 / 100000) (1087401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786507008 :
    ThetaLowerSegment 2786507008 2786638080 (278643989276381 / 100000)
      (278657166413817 / 100000) := by
  exact
    packedTile65536 2786507008 2786638080 14 6059 52787 31 _ _ (543701 / 25000) (2174807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786638080 :
    ThetaLowerSegment 2786638080 2786769152 (278657166413817 / 100000)
      (278670250064761 / 100000) := by
  exact
    packedTile65536 2786638080 2786769152 14 6016 52788 31 _ _ (2174809 / 100000) (543703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786769152 :
    ThetaLowerSegment 2786769152 2786900224 (278670250064761 / 100000)
      (27868328371907 / 10000) := by
  exact
    packedTile65536 2786769152 2786900224 14 5993 52789 31 _ _ (2174813 / 100000) (67963 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2786900224 :
    ThetaLowerSegment 2786900224 2787031296 (27868328371907 / 10000) (69674106536061 / 25000) := by
  exact
    packedTile65536 2786900224 2787031296 14 6043 52791 31 _ _ (1087409 / 50000) (2174821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787031296 :
    ThetaLowerSegment 2787031296 2787162368 (69674106536061 / 25000) (34838705046099 / 12500) := by
  exact
    packedTile65536 2787031296 2787162368 14 6076 52792 31 _ _ (2174823 / 100000) (1087413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787162368 :
    ThetaLowerSegment 2787162368 2787293440 (34838705046099 / 12500) (139361346840223 / 50000) := by
  exact
    packedTile65536 2787162368 2787293440 14 6002 52793 31 _ _ (2174827 / 100000) (217483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787293440 :
    ThetaLowerSegment 2787293440 2787424512 (139361346840223 / 50000)
      (139367913745447 / 50000) := by
  exact
    packedTile65536 2787293440 2787424512 14 6039 52794 31 _ _ (135927 / 6250) (434967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787424512 :
    ThetaLowerSegment 2787424512 2787555584 (139367913745447 / 50000) (69687222390479 / 25000) := by
  exact
    packedTile65536 2787424512 2787555584 14 6006 52796 31 _ _ (2174837 / 100000) (54371 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787555584 :
    ThetaLowerSegment 2787555584 2787686656 (69687222390479 / 25000) (69690510751583 / 25000) := by
  exact
    packedTile65536 2787555584 2787686656 14 6048 52797 31 _ _ (1087421 / 50000) (434969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787686656 :
    ThetaLowerSegment 2787686656 2787817728 (69690510751583 / 25000) (17423441895867 / 6250) := by
  exact
    packedTile65536 2787686656 2787817728 14 5990 52798 31 _ _ (1087423 / 50000) (2174849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787817728 :
    ThetaLowerSegment 2787817728 2787948800 (17423441895867 / 6250) (278788308651909 / 100000) := by
  exact
    packedTile65536 2787817728 2787948800 14 6087 52799 31 _ _ (2174851 / 100000) (1087427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2787948800 :
    ThetaLowerSegment 2787948800 2788079872 (278788308651909 / 100000)
      (278801573098653 / 100000) := by
  exact
    packedTile65536 2787948800 2788079872 14 6099 52801 31 _ _ (271857 / 12500) (2174859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788079872 :
    ThetaLowerSegment 2788079872 2788210944 (278801573098653 / 100000)
      (278814557012853 / 100000) := by
  exact
    packedTile65536 2788079872 2788210944 14 5970 52802 31 _ _ (108743 / 5000) (2174863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788210944 :
    ThetaLowerSegment 2788210944 2788342016 (278814557012853 / 100000)
      (278827623601773 / 100000) := by
  exact
    packedTile65536 2788210944 2788342016 14 6008 52803 31 _ _ (434973 / 20000) (543717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788342016 :
    ThetaLowerSegment 2788342016 2788473088 (278827623601773 / 100000)
      (278840766341183 / 100000) := by
  exact
    packedTile65536 2788342016 2788473088 14 6043 52804 31 _ _ (217487 / 10000) (2174873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788473088 :
    ThetaLowerSegment 2788473088 2788604160 (278840766341183 / 100000)
      (278853980881683 / 100000) := by
  exact
    packedTile65536 2788473088 2788604160 14 6076 52805 31 _ _ (17399 / 800) (1087439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788604160 :
    ThetaLowerSegment 2788604160 2788735232 (278853980881683 / 100000)
      (278866921411733 / 100000) := by
  exact
    packedTile65536 2788604160 2788735232 14 5950 52807 31 _ _ (2174879 / 100000) (1087441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788735232 :
    ThetaLowerSegment 2788735232 2788866304 (278866921411733 / 100000)
      (278880072935281 / 100000) := by
  exact
    packedTile65536 2788735232 2788866304 14 6047 52808 31 _ _ (543721 / 25000) (2174887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788866304 :
    ThetaLowerSegment 2788866304 2788997376 (278880072935281 / 100000)
      (278893174466617 / 100000) := by
  exact
    packedTile65536 2788866304 2788997376 14 6024 52809 31 _ _ (2174889 / 100000) (543723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2788997376 :
    ThetaLowerSegment 2788997376 2789128448 (278893174466617 / 100000)
      (278906376067127 / 100000) := by
  exact
    packedTile65536 2788997376 2789128448 14 6070 52810 31 _ _ (2174893 / 100000) (135931 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789128448 :
    ThetaLowerSegment 2789128448 2789259520 (278906376067127 / 100000)
      (278919510276149 / 100000) := by
  exact
    packedTile65536 2789128448 2789259520 14 6039 52812 31 _ _ (1087449 / 50000) (2174901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789259520 :
    ThetaLowerSegment 2789259520 2789390592 (278919510276149 / 100000)
      (278932577093373 / 100000) := by
  exact
    packedTile65536 2789259520 2789390592 14 6008 52813 31 _ _ (2174903 / 100000) (1087453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789390592 :
    ThetaLowerSegment 2789390592 2789521664 (278932577093373 / 100000)
      (278945622185559 / 100000) := by
  exact
    packedTile65536 2789390592 2789521664 14 5998 52814 31 _ _ (2174907 / 100000) (217491 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789521664 :
    ThetaLowerSegment 2789521664 2789652736 (278945622185559 / 100000)
      (55791744336107 / 20000) := by
  exact
    packedTile65536 2789521664 2789652736 14 6023 52815 31 _ _ (67966 / 3125) (434983 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789652736 :
    ThetaLowerSegment 2789652736 2789783808 (55791744336107 / 20000) (34871470582223 / 12500) := by
  exact
    packedTile65536 2789652736 2789783808 14 5997 52817 31 _ _ (2174917 / 100000) (54373 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789783808 :
    ThetaLowerSegment 2789783808 2789914880 (34871470582223 / 12500)
      (278984842457757 / 100000) := by
  exact
    packedTile65536 2789783808 2789914880 14 6013 52818 31 _ _ (2174921 / 100000) (543731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2789914880 :
    ThetaLowerSegment 2789914880 2790045952 (278984842457757 / 100000)
      (278998153004877 / 100000) := by
  exact
    packedTile65536 2789914880 2790045952 14 6120 52819 31 _ _ (1087463 / 50000) (2174929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790045952 :
    ThetaLowerSegment 2790045952 2790177024 (278998153004877 / 100000)
      (27901107861981 / 10000) := by
  exact
    packedTile65536 2790045952 2790177024 14 5943 52820 31 _ _ (2174931 / 100000) (1087467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790177024 :
    ThetaLowerSegment 2790177024 2790308096 (27901107861981 / 10000) (139512067380309 / 50000) := by
  exact
    packedTile65536 2790177024 2790308096 14 6003 52822 31 _ _ (271867 / 12500) (2174939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790308096 :
    ThetaLowerSegment 2790308096 2790439168 (139512067380309 / 50000)
      (139518610687299 / 50000) := by
  exact
    packedTile65536 2790308096 2790439168 14 6017 52823 31 _ _ (108747 / 5000) (2174943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790439168 :
    ThetaLowerSegment 2790439168 2790570240 (139518610687299 / 50000)
      (279050281919323 / 100000) := by
  exact
    packedTile65536 2790439168 2790570240 14 6005 52824 31 _ _ (434989 / 20000) (543737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790570240 :
    ThetaLowerSegment 2790570240 2790701312 (279050281919323 / 100000)
      (279063353368823 / 100000) := by
  exact
    packedTile65536 2790570240 2790701312 14 6010 52825 31 _ _ (43499 / 2000) (2174953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790701312 :
    ThetaLowerSegment 2790701312 2790832384 (279063353368823 / 100000)
      (279076413967593 / 100000) := by
  exact
    packedTile65536 2790701312 2790832384 14 6005 52827 31 _ _ (1087477 / 50000) (2174957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790832384 :
    ThetaLowerSegment 2790832384 2790963456 (279076413967593 / 100000)
      (139544813421759 / 50000) := by
  exact
    packedTile65536 2790832384 2790963456 14 6075 52828 31 _ _ (2174959 / 100000) (1087481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2790963456 :
    ThetaLowerSegment 2790963456 2791094528 (139544813421759 / 50000)
      (139551331788867 / 50000) := by
  exact
    packedTile65536 2790963456 2791094528 14 5994 52829 31 _ _ (543741 / 25000) (2174967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791094528 :
    ThetaLowerSegment 2791094528 2791225600 (139551331788867 / 50000)
      (139557930641779 / 50000) := by
  exact
    packedTile65536 2791094528 2791225600 14 6068 52830 31 _ _ (271871 / 12500) (2174971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791225600 :
    ThetaLowerSegment 2791225600 2791356672 (139557930641779 / 50000) (34891142708587 / 12500) := by
  exact
    packedTile65536 2791225600 2791356672 14 6106 52832 31 _ _ (2174973 / 100000) (67968 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791356672 :
    ThetaLowerSegment 2791356672 2791487744 (34891142708587 / 12500) (139571129480507 / 50000) := by
  exact
    packedTile65536 2791356672 2791487744 14 6031 52833 31 _ _ (1087489 / 50000) (2174981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791487744 :
    ThetaLowerSegment 2791487744 2791618816 (139571129480507 / 50000)
      (279155402383283 / 100000) := by
  exact
    packedTile65536 2791487744 2791618816 14 6043 52834 31 _ _ (2174983 / 100000) (1087493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791618816 :
    ThetaLowerSegment 2791618816 2791749888 (279155402383283 / 100000)
      (279168300056193 / 100000) := by
  exact
    packedTile65536 2791618816 2791749888 14 5930 52835 31 _ _ (2174987 / 100000) (217499 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791749888 :
    ThetaLowerSegment 2791749888 2791880960 (279168300056193 / 100000)
      (55836287836573 / 20000) := by
  exact
    packedTile65536 2791749888 2791880960 14 6041 52837 31 _ _ (135937 / 6250) (434999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2791880960 :
    ThetaLowerSegment 2791880960 2792012032 (55836287836573 / 20000)
      (279194589214727 / 100000) := by
  exact
    packedTile65536 2791880960 2792012032 14 6046 52838 31 _ _ (2174997 / 100000) (87 / 4)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792012032 :
    ThetaLowerSegment 2792012032 2792143104 (279194589214727 / 100000)
      (139603805472857 / 50000) := by
  exact
    packedTile65536 2792012032 2792143104 14 5987 52839 31 _ _ (2175001 / 100000) (543751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792143104 :
    ThetaLowerSegment 2792143104 2792274176 (139603805472857 / 50000)
      (139610334840869 / 50000) := by
  exact
    packedTile65536 2792143104 2792274176 14 6004 52840 31 _ _ (1087503 / 50000) (2175009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792274176 :
    ThetaLowerSegment 2792274176 2792405248 (139610334840869 / 50000) (8726060403088 / 3125) := by
  exact
    packedTile65536 2792274176 2792405248 14 6098 52841 31 _ _ (2175011 / 100000) (1087507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792405248 :
    ThetaLowerSegment 2792405248 2792536320 (8726060403088 / 3125) (69811756622279 / 25000) := by
  exact
    packedTile65536 2792405248 2792536320 14 6020 52843 31 _ _ (435003 / 20000) (1087509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792536320 :
    ThetaLowerSegment 2792536320 2792667392 (69811756622279 / 25000) (69815006102159 / 25000) := by
  exact
    packedTile65536 2792536320 2792667392 14 5976 52844 31 _ _ (108751 / 5000) (2175023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792667392 :
    ThetaLowerSegment 2792667392 2792798464 (69815006102159 / 25000)
      (279273089783811 / 100000) := by
  exact
    packedTile65536 2792667392 2792798464 14 6007 52845 31 _ _ (87001 / 4000) (543757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792798464 :
    ThetaLowerSegment 2792798464 2792929536 (279273089783811 / 100000)
      (69821550758413 / 25000) := by
  exact
    packedTile65536 2792798464 2792929536 14 6029 52846 31 _ _ (2175029 / 100000) (271879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2792929536 :
    ThetaLowerSegment 2792929536 2793060608 (69821550758413 / 25000) (69824813309413 / 25000) := by
  exact
    packedTile65536 2792929536 2793060608 14 6000 52848 31 _ _ (1087517 / 50000) (2175037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793060608 :
    ThetaLowerSegment 2793060608 2793191680 (69824813309413 / 25000)
      (279312475299733 / 100000) := by
  exact
    packedTile65536 2793060608 2793191680 14 6079 52849 31 _ _ (2175039 / 100000) (1087521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793191680 :
    ThetaLowerSegment 2793191680 2793322752 (279312475299733 / 100000)
      (279325482062853 / 100000) := by
  exact
    packedTile65536 2793191680 2793322752 14 5980 52850 31 _ _ (543761 / 25000) (2175047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793322752 :
    ThetaLowerSegment 2793322752 2793339136 (279325482062853 / 100000)
      (279327135099333 / 100000) := by
  exact
    packedTile65536 2793322752 2793339136 11 760 52851 31 _ _ (271881 / 12500) (2175051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793339136 :
    ThetaLowerSegment 2793339136 2793341184 (279327135099333 / 100000)
      (55865469650827 / 20000) := by
  exact
    packedTile65536 2793339136 2793341184 8 98 52852 31 _ _ (2175049 / 100000) (543763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2761341184_2793341184 :
    ThetaLowerSegment 2761341184 2793341184 (55225316575379 / 20000) (55865469650827 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2761341184 cell2761472256)
                  (ThetaLowerSegment.join cell2761603328 cell2761734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2761865472 cell2761996544)
                  (ThetaLowerSegment.join cell2762127616 cell2762258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2762389760 cell2762520832)
                  (ThetaLowerSegment.join cell2762651904 cell2762782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2762914048 cell2763045120)
                  (ThetaLowerSegment.join cell2763176192 cell2763307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2763438336 cell2763569408)
                  (ThetaLowerSegment.join cell2763700480 cell2763831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2763962624 cell2764093696)
                  (ThetaLowerSegment.join cell2764224768 cell2764355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2764486912 cell2764617984)
                  (ThetaLowerSegment.join cell2764749056 cell2764880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2765011200 cell2765142272)
                  (ThetaLowerSegment.join cell2765273344 cell2765404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2765535488 cell2765666560)
                  (ThetaLowerSegment.join cell2765797632 cell2765928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2766059776 cell2766190848)
                  (ThetaLowerSegment.join cell2766321920 cell2766452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2766584064 cell2766715136)
                  (ThetaLowerSegment.join cell2766846208 cell2766977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2767108352 cell2767239424)
                  (ThetaLowerSegment.join cell2767370496 cell2767501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2767632640 cell2767763712)
                  (ThetaLowerSegment.join cell2767894784 cell2768025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2768156928 cell2768288000)
                  (ThetaLowerSegment.join cell2768419072 cell2768550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2768681216 cell2768812288)
                  (ThetaLowerSegment.join cell2768943360 cell2769074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2769205504 cell2769336576)
                  (ThetaLowerSegment.join cell2769467648 cell2769598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2769729792 cell2769860864)
                  (ThetaLowerSegment.join cell2769991936 cell2770123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2770254080 cell2770385152)
                  (ThetaLowerSegment.join cell2770516224 cell2770647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2770778368 cell2770909440)
                  (ThetaLowerSegment.join cell2771040512 cell2771171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2771302656 cell2771433728)
                  (ThetaLowerSegment.join cell2771564800 cell2771695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2771826944 cell2771958016)
                  (ThetaLowerSegment.join cell2772089088 cell2772220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2772351232 cell2772482304)
                  (ThetaLowerSegment.join cell2772613376 cell2772744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2772875520 cell2773006592)
                  (ThetaLowerSegment.join cell2773137664 cell2773268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2773399808 cell2773530880)
                  (ThetaLowerSegment.join cell2773661952 cell2773793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2773924096 cell2774055168)
                  (ThetaLowerSegment.join cell2774186240 cell2774317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2774448384 cell2774579456)
                  (ThetaLowerSegment.join cell2774710528 cell2774841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2774972672 cell2775103744)
                  (ThetaLowerSegment.join cell2775234816 cell2775365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2775496960 cell2775628032)
                  (ThetaLowerSegment.join cell2775759104 cell2775890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2776021248 cell2776152320)
                  (ThetaLowerSegment.join cell2776283392 cell2776414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2776545536 cell2776676608)
                  (ThetaLowerSegment.join cell2776807680 cell2776938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2777069824 cell2777200896)
                  (ThetaLowerSegment.join cell2777331968 cell2777463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2777594112 cell2777725184)
                  (ThetaLowerSegment.join cell2777856256 cell2777987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2778118400 cell2778249472)
                  (ThetaLowerSegment.join cell2778380544 cell2778511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2778642688 cell2778773760)
                  (ThetaLowerSegment.join cell2778904832 cell2779035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2779166976 cell2779298048)
                  (ThetaLowerSegment.join cell2779429120 cell2779560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2779691264 cell2779822336)
                  (ThetaLowerSegment.join cell2779953408 cell2780084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2780215552 cell2780346624)
                  (ThetaLowerSegment.join cell2780477696 cell2780608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2780739840 cell2780870912)
                  (ThetaLowerSegment.join cell2781001984 cell2781133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2781264128 cell2781395200)
                  (ThetaLowerSegment.join cell2781526272 cell2781657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2781788416 cell2781919488)
                  (ThetaLowerSegment.join cell2782050560 cell2782181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2782312704 cell2782443776)
                  (ThetaLowerSegment.join cell2782574848 cell2782705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2782836992 cell2782968064)
                  (ThetaLowerSegment.join cell2783099136 cell2783230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2783361280 cell2783492352)
                  (ThetaLowerSegment.join cell2783623424 cell2783754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2783885568 cell2784016640)
                  (ThetaLowerSegment.join cell2784147712 cell2784278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2784409856 cell2784540928)
                  (ThetaLowerSegment.join cell2784672000 cell2784803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2784934144 cell2785065216)
                  (ThetaLowerSegment.join cell2785196288 cell2785327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2785458432 cell2785589504)
                  (ThetaLowerSegment.join cell2785720576 cell2785851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2785982720 cell2786113792)
                  (ThetaLowerSegment.join cell2786244864 cell2786375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2786507008 cell2786638080)
                  (ThetaLowerSegment.join cell2786769152 cell2786900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2787031296 cell2787162368)
                  (ThetaLowerSegment.join cell2787293440 cell2787424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2787555584 cell2787686656)
                  (ThetaLowerSegment.join cell2787817728 cell2787948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2788079872 cell2788210944)
                  (ThetaLowerSegment.join cell2788342016 cell2788473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2788604160 cell2788735232)
                  (ThetaLowerSegment.join cell2788866304 cell2788997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2789128448 cell2789259520)
                  (ThetaLowerSegment.join cell2789390592 cell2789521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2789652736 cell2789783808)
                  (ThetaLowerSegment.join cell2789914880 cell2790045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2790177024 cell2790308096)
                  (ThetaLowerSegment.join cell2790439168 cell2790570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2790701312 cell2790832384)
                  (ThetaLowerSegment.join cell2790963456 cell2791094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2791225600 cell2791356672)
                  (ThetaLowerSegment.join cell2791487744 cell2791618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2791749888 cell2791880960)
                  (ThetaLowerSegment.join cell2792012032 cell2792143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2792274176 cell2792405248)
                  (ThetaLowerSegment.join cell2792536320 cell2792667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2792798464 cell2792929536)
                (ThetaLowerSegment.join cell2793060608 cell2793191680))
              (ThetaLowerSegment.join cell2793322752 cell2793339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
