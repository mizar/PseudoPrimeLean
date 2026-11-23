/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2089341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2057341184 :
    ThetaLowerSegment 2057341184 2057472256 (205728900255983 / 100000)
      (20574211231717 / 10000) := by
  exact
    packedTile65536 2057341184 2057472256 14 6161 45357 31 _ _ (2144467 / 100000) (214447 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057472256 :
    ThetaLowerSegment 2057472256 2057603328 (20574211231717 / 10000) (12859694507031 / 6250) := by
  exact
    packedTile65536 2057472256 2057603328 14 6062 45359 31 _ _ (2144473 / 100000) (536119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057603328 :
    ThetaLowerSegment 2057603328 2057734400 (12859694507031 / 6250) (205768062621177 / 100000) := by
  exact
    packedTile65536 2057603328 2057734400 14 6039 45360 31 _ _ (2144479 / 100000) (1072241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057734400 :
    ThetaLowerSegment 2057734400 2057865472 (205768062621177 / 100000)
      (205780938115121 / 100000) := by
  exact
    packedTile65536 2057734400 2057865472 14 6004 45362 31 _ _ (1072243 / 50000) (2144489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057865472 :
    ThetaLowerSegment 2057865472 2057996544 (205780938115121 / 100000)
      (205794043105733 / 100000) := by
  exact
    packedTile65536 2057865472 2057996544 14 6111 45363 31 _ _ (536123 / 25000) (428899 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057996544 :
    ThetaLowerSegment 2057996544 2058127616 (205794043105733 / 100000)
      (205806998018151 / 100000) := by
  exact
    packedTile65536 2057996544 2058127616 14 6041 45365 31 _ _ (1072249 / 50000) (2144501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058127616 :
    ThetaLowerSegment 2058127616 2058258688 (205806998018151 / 100000)
      (205820109521721 / 100000) := by
  exact
    packedTile65536 2058127616 2058258688 14 6114 45366 31 _ _ (428901 / 20000) (536127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058258688 :
    ThetaLowerSegment 2058258688 2058389760 (205820109521721 / 100000)
      (102916735984881 / 50000) := by
  exact
    packedTile65536 2058258688 2058389760 14 6231 45368 31 _ _ (2144511 / 100000) (1072257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058389760 :
    ThetaLowerSegment 2058389760 2058520832 (102916735984881 / 50000) (51461607285369 / 25000) := by
  exact
    packedTile65536 2058389760 2058520832 14 6042 45369 31 _ _ (2144517 / 100000) (53613 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058520832 :
    ThetaLowerSegment 2058520832 2058651904 (51461607285369 / 25000) (51464920574949 / 25000) := by
  exact
    packedTile65536 2058520832 2058651904 14 6180 45370 31 _ _ (536131 / 25000) (2144527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058651904 :
    ThetaLowerSegment 2058651904 2058782976 (51464920574949 / 25000) (102936353015243 / 50000) := by
  exact
    packedTile65536 2058651904 2058782976 14 6073 45372 31 _ _ (214453 / 10000) (2144533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058782976 :
    ThetaLowerSegment 2058782976 2058914048 (102936353015243 / 50000)
      (205885789850723 / 100000) := by
  exact
    packedTile65536 2058782976 2058914048 14 6101 45373 31 _ _ (2144537 / 100000) (107227 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2058914048 :
    ThetaLowerSegment 2058914048 2059045120 (205885789850723 / 100000)
      (102949415408353 / 50000) := by
  exact
    packedTile65536 2058914048 2059045120 14 6081 45375 31 _ _ (2144543 / 100000) (1072273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059045120 :
    ThetaLowerSegment 2059045120 2059176192 (102949415408353 / 50000)
      (205912004781213 / 100000) := by
  exact
    packedTile65536 2059045120 2059176192 14 6143 45376 31 _ _ (2144549 / 100000) (268069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059176192 :
    ThetaLowerSegment 2059176192 2059307264 (205912004781213 / 100000)
      (41184992437713 / 20000) := by
  exact
    packedTile65536 2059176192 2059307264 14 6042 45378 31 _ _ (536139 / 25000) (2144559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059307264 :
    ThetaLowerSegment 2059307264 2059438336 (41184992437713 / 20000)
      (205937973246219 / 100000) := by
  exact
    packedTile65536 2059307264 2059438336 14 6067 45379 31 _ _ (1072281 / 50000) (428913 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059438336 :
    ThetaLowerSegment 2059438336 2059569408 (205937973246219 / 100000)
      (205951194507939 / 100000) := by
  exact
    packedTile65536 2059438336 2059569408 14 6165 45381 31 _ _ (268071 / 12500) (2144571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059569408 :
    ThetaLowerSegment 2059569408 2059700480 (205951194507939 / 100000)
      (205964066247089 / 100000) := by
  exact
    packedTile65536 2059569408 2059700480 14 6002 45382 31 _ _ (85783 / 4000) (1072289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059700480 :
    ThetaLowerSegment 2059700480 2059831552 (205964066247089 / 100000)
      (205977294022697 / 100000) := by
  exact
    packedTile65536 2059700480 2059831552 14 6168 45383 31 _ _ (2144581 / 100000) (268073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059831552 :
    ThetaLowerSegment 2059831552 2059962624 (205977294022697 / 100000)
      (205990275213861 / 100000) := by
  exact
    packedTile65536 2059831552 2059962624 14 6053 45385 31 _ _ (536147 / 25000) (2144591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2059962624 :
    ThetaLowerSegment 2059962624 2060093696 (205990275213861 / 100000)
      (206003526660187 / 100000) := by
  exact
    packedTile65536 2059962624 2060093696 14 6179 45386 31 _ _ (1072297 / 50000) (2144597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060093696 :
    ThetaLowerSegment 2060093696 2060224768 (206003526660187 / 100000)
      (206016582984987 / 100000) := by
  exact
    packedTile65536 2060093696 2060224768 14 6088 45388 31 _ _ (10723 / 500) (2144603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060224768 :
    ThetaLowerSegment 2060224768 2060355840 (206016582984987 / 100000)
      (206029690822971 / 100000) := by
  exact
    packedTile65536 2060224768 2060355840 14 6112 45389 31 _ _ (2144607 / 100000) (214461 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060355840 :
    ThetaLowerSegment 2060355840 2060486912 (206029690822971 / 100000)
      (103021501217931 / 50000) := by
  exact
    packedTile65536 2060355840 2060486912 14 6207 45391 31 _ _ (2144613 / 100000) (268077 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060486912 :
    ThetaLowerSegment 2060486912 2060617984 (103021501217931 / 50000) (4121115344163 / 2000) := by
  exact
    packedTile65536 2060486912 2060617984 14 5952 45392 31 _ _ (2144619 / 100000) (1072311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060617984 :
    ThetaLowerSegment 2060617984 2060749056 (4121115344163 / 2000) (20606893521179 / 10000) := by
  exact
    packedTile65536 2060617984 2060749056 14 6140 45394 31 _ _ (1072313 / 50000) (2144629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060749056 :
    ThetaLowerSegment 2060749056 2060880128 (20606893521179 / 10000) (4121640563803 / 2000) := by
  exact
    packedTile65536 2060749056 2060880128 14 6105 45395 31 _ _ (268079 / 12500) (428927 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2060880128 :
    ThetaLowerSegment 2060880128 2061011200 (4121640563803 / 2000) (103047548807061 / 50000) := by
  exact
    packedTile65536 2060880128 2061011200 14 6094 45396 31 _ _ (1072319 / 50000) (2144641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061011200 :
    ThetaLowerSegment 2061011200 2061142272 (103047548807061 / 50000)
      (103054175760111 / 50000) := by
  exact
    packedTile65536 2061011200 2061142272 14 6180 45398 31 _ _ (428929 / 20000) (268081 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061142272 :
    ThetaLowerSegment 2061142272 2061273344 (103054175760111 / 50000) (51530323086089 / 25000) := by
  exact
    packedTile65536 2061142272 2061273344 14 6034 45399 31 _ _ (2144651 / 100000) (1072327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061273344 :
    ThetaLowerSegment 2061273344 2061404416 (51530323086089 / 25000)
      (206134394053969 / 100000) := by
  exact
    packedTile65536 2061273344 2061404416 14 6109 45401 31 _ _ (2144657 / 100000) (107233 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061404416 :
    ThetaLowerSegment 2061404416 2061535488 (206134394053969 / 100000)
      (206147663090137 / 100000) := by
  exact
    packedTile65536 2061404416 2061535488 14 6187 45402 31 _ _ (268083 / 12500) (2144667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061535488 :
    ThetaLowerSegment 2061535488 2061666560 (206147663090137 / 100000)
      (206160541833487 / 100000) := by
  exact
    packedTile65536 2061535488 2061666560 14 6005 45404 31 _ _ (214467 / 10000) (2144673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061666560 :
    ThetaLowerSegment 2061666560 2061797632 (206160541833487 / 100000)
      (103086721032821 / 50000) := by
  exact
    packedTile65536 2061666560 2061797632 14 6015 45405 31 _ _ (2144677 / 100000) (53617 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061797632 :
    ThetaLowerSegment 2061797632 2061928704 (103086721032821 / 50000)
      (206186616853311 / 100000) := by
  exact
    packedTile65536 2061797632 2061928704 14 6143 45407 31 _ _ (2144683 / 100000) (1072343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2061928704 :
    ThetaLowerSegment 2061928704 2062059776 (206186616853311 / 100000)
      (103099887260163 / 50000) := by
  exact
    packedTile65536 2061928704 2062059776 14 6135 45408 31 _ _ (2144689 / 100000) (536173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062059776 :
    ThetaLowerSegment 2062059776 2062190848 (103099887260163 / 50000) (20621299442647 / 10000) := by
  exact
    packedTile65536 2062059776 2062190848 14 6164 45409 31 _ _ (268087 / 12500) (2144699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062190848 :
    ThetaLowerSegment 2062190848 2062321920 (20621299442647 / 10000) (51556509089833 / 25000) := by
  exact
    packedTile65536 2062190848 2062321920 14 6081 45411 31 _ _ (1072351 / 50000) (428941 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062321920 :
    ThetaLowerSegment 2062321920 2062452992 (51556509089833 / 25000) (51559776552471 / 25000) := by
  exact
    packedTile65536 2062321920 2062452992 14 6094 45412 31 _ _ (536177 / 25000) (2144711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062452992 :
    ThetaLowerSegment 2062452992 2062584064 (51559776552471 / 25000)
      (206252199694959 / 100000) := by
  exact
    packedTile65536 2062452992 2062584064 14 6105 45414 31 _ _ (428943 / 20000) (1072359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062584064 :
    ThetaLowerSegment 2062584064 2062715136 (206252199694959 / 100000)
      (206265291071943 / 100000) := by
  exact
    packedTile65536 2062584064 2062715136 14 6104 45415 31 _ _ (2144721 / 100000) (536181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062715136 :
    ThetaLowerSegment 2062715136 2062846208 (206265291071943 / 100000)
      (103139299551489 / 50000) := by
  exact
    packedTile65536 2062715136 2062846208 14 6205 45417 31 _ _ (2144727 / 100000) (214473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062846208 :
    ThetaLowerSegment 2062846208 2062977280 (103139299551489 / 50000) (51572898511571 / 25000) := by
  exact
    packedTile65536 2062846208 2062977280 14 6059 45418 31 _ _ (1072367 / 50000) (2144737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2062977280 :
    ThetaLowerSegment 2062977280 2063108352 (51572898511571 / 25000) (51576186397991 / 25000) := by
  exact
    packedTile65536 2062977280 2063108352 14 6132 45420 31 _ _ (107237 / 5000) (2144743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063108352 :
    ThetaLowerSegment 2063108352 2063239424 (51576186397991 / 25000) (103158923922639 / 50000) := by
  exact
    packedTile65536 2063108352 2063239424 14 6109 45421 31 _ _ (1072373 / 50000) (2144749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063239424 :
    ThetaLowerSegment 2063239424 2063370496 (103158923922639 / 50000)
      (206330932983331 / 100000) := by
  exact
    packedTile65536 2063239424 2063370496 14 6101 45422 31 _ _ (2144753 / 100000) (536189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063370496 :
    ThetaLowerSegment 2063370496 2063501568 (206330932983331 / 100000)
      (206344011723713 / 100000) := by
  exact
    packedTile65536 2063370496 2063501568 14 6098 45424 31 _ _ (2144759 / 100000) (1072381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063501568 :
    ThetaLowerSegment 2063501568 2063632640 (206344011723713 / 100000)
      (206357137691633 / 100000) := by
  exact
    packedTile65536 2063501568 2063632640 14 6120 45425 31 _ _ (1072383 / 50000) (2144769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063632640 :
    ThetaLowerSegment 2063632640 2063763712 (206357137691633 / 100000)
      (206370242248553 / 100000) := by
  exact
    packedTile65536 2063632640 2063763712 14 6110 45427 31 _ _ (536193 / 25000) (85791 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063763712 :
    ThetaLowerSegment 2063763712 2063894784 (206370242248553 / 100000)
      (206383546306487 / 100000) := by
  exact
    packedTile65536 2063763712 2063894784 14 6203 45428 31 _ _ (1072389 / 50000) (2144781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2063894784 :
    ThetaLowerSegment 2063894784 2064025856 (206383546306487 / 100000)
      (206396852552627 / 100000) := by
  exact
    packedTile65536 2063894784 2064025856 14 6204 45430 31 _ _ (428957 / 20000) (536197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064025856 :
    ThetaLowerSegment 2064025856 2064156928 (206396852552627 / 100000)
      (206409837117341 / 100000) := by
  exact
    packedTile65536 2064025856 2064156928 14 6054 45431 31 _ _ (2144791 / 100000) (1072397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064156928 :
    ThetaLowerSegment 2064156928 2064288000 (206409837117341 / 100000)
      (206423001881327 / 100000) := by
  exact
    packedTile65536 2064156928 2064288000 14 6138 45432 31 _ _ (2144797 / 100000) (2681 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064288000 :
    ThetaLowerSegment 2064288000 2064419072 (206423001881327 / 100000)
      (206436198860339 / 100000) := by
  exact
    packedTile65536 2064288000 2064419072 14 6153 45434 31 _ _ (536201 / 25000) (2144807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064419072 :
    ThetaLowerSegment 2064419072 2064550144 (206436198860339 / 100000)
      (206449327242349 / 100000) := by
  exact
    packedTile65536 2064419072 2064550144 14 6121 45435 31 _ _ (214481 / 10000) (2144813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064550144 :
    ThetaLowerSegment 2064550144 2064681216 (206449327242349 / 100000)
      (41292495421849 / 20000) := by
  exact
    packedTile65536 2064550144 2064681216 14 6131 45437 31 _ _ (134051 / 6250) (2144819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064681216 :
    ThetaLowerSegment 2064681216 2064812288 (41292495421849 / 20000) (51618905682353 / 25000) := by
  exact
    packedTile65536 2064681216 2064812288 14 6129 45438 31 _ _ (2144823 / 100000) (1072413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064812288 :
    ThetaLowerSegment 2064812288 2064943360 (51618905682353 / 25000)
      (206488759807037 / 100000) := by
  exact
    packedTile65536 2064812288 2064943360 14 6125 45440 31 _ _ (2144829 / 100000) (67026 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2064943360 :
    ThetaLowerSegment 2064943360 2065074432 (206488759807037 / 100000)
      (206501929093937 / 100000) := by
  exact
    packedTile65536 2064943360 2065074432 14 6140 45441 31 _ _ (428967 / 20000) (1072419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065074432 :
    ThetaLowerSegment 2065074432 2065205504 (206501929093937 / 100000)
      (206514918257089 / 100000) := by
  exact
    packedTile65536 2065074432 2065205504 14 6056 45443 31 _ _ (1072421 / 50000) (428969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065205504 :
    ThetaLowerSegment 2065205504 2065336576 (206514918257089 / 100000)
      (206528055451089 / 100000) := by
  exact
    packedTile65536 2065205504 2065336576 14 6125 45444 31 _ _ (134053 / 6250) (2144851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065336576 :
    ThetaLowerSegment 2065336576 2065467648 (206528055451089 / 100000)
      (206541055411183 / 100000) := by
  exact
    packedTile65536 2065336576 2065467648 14 6061 45445 31 _ _ (1072427 / 50000) (2144857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065467648 :
    ThetaLowerSegment 2065467648 2065598720 (206541055411183 / 100000)
      (51638580344117 / 25000) := by
  exact
    packedTile65536 2065467648 2065598720 14 6185 45447 31 _ _ (2144861 / 100000) (67027 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065598720 :
    ThetaLowerSegment 2065598720 2065729792 (51638580344117 / 25000) (6455223901252 / 3125) := by
  exact
    packedTile65536 2065598720 2065729792 14 5988 45448 31 _ _ (2144867 / 100000) (214487 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065729792 :
    ThetaLowerSegment 2065729792 2065860864 (6455223901252 / 3125) (4131604199153 / 2000) := by
  exact
    packedTile65536 2065729792 2065860864 14 6082 45450 31 _ _ (2144873 / 100000) (536219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065860864 :
    ThetaLowerSegment 2065860864 2065991936 (4131604199153 / 2000) (20659314572893 / 10000) := by
  exact
    packedTile65536 2065860864 2065991936 14 6031 45451 31 _ _ (26811 / 1250) (2144883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2065991936 :
    ThetaLowerSegment 2065991936 2066123008 (20659314572893 / 10000) (10330325954657 / 5000) := by
  exact
    packedTile65536 2065991936 2066123008 14 6235 45453 31 _ _ (1072443 / 50000) (2144889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066123008 :
    ThetaLowerSegment 2066123008 2066254080 (10330325954657 / 5000) (25827472620047 / 12500) := by
  exact
    packedTile65536 2066123008 2066254080 14 6183 45454 31 _ _ (536223 / 25000) (428979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066254080 :
    ThetaLowerSegment 2066254080 2066385152 (25827472620047 / 12500) (20663287771367 / 10000) := by
  exact
    packedTile65536 2066254080 2066385152 14 6106 45456 31 _ _ (2144899 / 100000) (1072451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066385152 :
    ThetaLowerSegment 2066385152 2066516224 (20663287771367 / 10000) (10332302586009 / 5000) := by
  exact
    packedTile65536 2066385152 2066516224 14 6142 45457 31 _ _ (428981 / 20000) (536227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066516224 :
    ThetaLowerSegment 2066516224 2066647296 (10332302586009 / 5000) (10332961073993 / 5000) := by
  exact
    packedTile65536 2066516224 2066647296 14 6140 45458 31 _ _ (134057 / 6250) (428983 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066647296 :
    ThetaLowerSegment 2066647296 2066778368 (10332961073993 / 5000) (20667229475507 / 10000) := by
  exact
    packedTile65536 2066647296 2066778368 14 6095 45460 31 _ _ (1072459 / 50000) (2144921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066778368 :
    ThetaLowerSegment 2066778368 2066909440 (20667229475507 / 10000) (103342708700051 / 50000) := by
  exact
    packedTile65536 2066778368 2066909440 14 6118 45461 31 _ _ (536231 / 25000) (2144927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2066909440 :
    ThetaLowerSegment 2066909440 2067040512 (103342708700051 / 50000) (6459320261792 / 3125) := by
  exact
    packedTile65536 2066909440 2067040512 14 5982 45463 31 _ _ (2144931 / 100000) (1072467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067040512 :
    ThetaLowerSegment 2067040512 2067171584 (6459320261792 / 3125) (206711368956973 / 100000) := by
  exact
    packedTile65536 2067040512 2067171584 14 6117 45464 31 _ _ (2144937 / 100000) (107247 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067171584 :
    ThetaLowerSegment 2067171584 2067302656 (206711368956973 / 100000)
      (206724388760983 / 100000) := by
  exact
    packedTile65536 2067171584 2067302656 14 6070 45466 31 _ _ (2144943 / 100000) (1072473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067302656 :
    ThetaLowerSegment 2067302656 2067433728 (206724388760983 / 100000)
      (206737372143333 / 100000) := by
  exact
    packedTile65536 2067302656 2067433728 14 6053 45467 31 _ _ (42899 / 2000) (2144953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067433728 :
    ThetaLowerSegment 2067433728 2067564800 (206737372143333 / 100000)
      (206750411330857 / 100000) := by
  exact
    packedTile65536 2067433728 2067564800 14 6079 45469 31 _ _ (536239 / 25000) (2144959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067564800 :
    ThetaLowerSegment 2067564800 2067695872 (206750411330857 / 100000)
      (206763615716929 / 100000) := by
  exact
    packedTile65536 2067564800 2067695872 14 6156 45470 31 _ _ (1072481 / 50000) (428993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067695872 :
    ThetaLowerSegment 2067695872 2067826944 (206763615716929 / 100000)
      (206776627098883 / 100000) := by
  exact
    packedTile65536 2067695872 2067826944 14 6066 45471 31 _ _ (2144969 / 100000) (536243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067826944 :
    ThetaLowerSegment 2067826944 2067958016 (206776627098883 / 100000)
      (51697433760277 / 25000) := by
  exact
    packedTile65536 2067826944 2067958016 14 6111 45473 31 _ _ (85799 / 4000) (1072489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2067958016 :
    ThetaLowerSegment 2067958016 2068089088 (51697433760277 / 25000) (25850373877961 / 12500) := by
  exact
    packedTile65536 2067958016 2068089088 14 6180 45474 31 _ _ (2144981 / 100000) (268123 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068089088 :
    ThetaLowerSegment 2068089088 2068220160 (25850373877961 / 12500) (51703968991651 / 25000) := by
  exact
    packedTile65536 2068089088 2068220160 14 6007 45476 31 _ _ (536247 / 25000) (2144991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068220160 :
    ThetaLowerSegment 2068220160 2068351232 (51703968991651 / 25000) (51707244397489 / 25000) := by
  exact
    packedTile65536 2068220160 2068351232 14 6108 45477 31 _ _ (1072497 / 50000) (2144997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068351232 :
    ThetaLowerSegment 2068351232 2068482304 (51707244397489 / 25000) (51710502116239 / 25000) := by
  exact
    packedTile65536 2068351232 2068482304 14 6075 45479 31 _ _ (429 / 20) (2145003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068482304 :
    ThetaLowerSegment 2068482304 2068613376 (51710502116239 / 25000)
      (206855249593167 / 100000) := by
  exact
    packedTile65536 2068482304 2068613376 14 6173 45480 31 _ _ (2145007 / 100000) (214501 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068613376 :
    ThetaLowerSegment 2068613376 2068744448 (206855249593167 / 100000) (4137366297347 / 2000) := by
  exact
    packedTile65536 2068613376 2068744448 14 6091 45482 31 _ _ (2145013 / 100000) (268127 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068744448 :
    ThetaLowerSegment 2068744448 2068875520 (4137366297347 / 2000) (41376273461593 / 20000) := by
  exact
    packedTile65536 2068744448 2068875520 14 6085 45483 31 _ _ (2145019 / 100000) (1072511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2068875520 :
    ThetaLowerSegment 2068875520 2069006592 (41376273461593 / 20000)
      (206894610698489 / 100000) := by
  exact
    packedTile65536 2068875520 2069006592 14 6174 45484 31 _ _ (1072513 / 50000) (2145029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069006592 :
    ThetaLowerSegment 2069006592 2069137664 (206894610698489 / 100000)
      (41381542510789 / 20000) := by
  exact
    packedTile65536 2069006592 2069137664 14 6108 45486 31 _ _ (268129 / 12500) (429007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069137664 :
    ThetaLowerSegment 2069137664 2069268736 (41381542510789 / 20000) (8276837039521 / 4000) := by
  exact
    packedTile65536 2069137664 2069268736 14 6160 45487 31 _ _ (1072519 / 50000) (2145041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069268736 :
    ThetaLowerSegment 2069268736 2069399808 (8276837039521 / 4000) (20693414161027 / 10000) := by
  exact
    packedTile65536 2069268736 2069399808 14 6161 45489 31 _ _ (429009 / 20000) (268131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069399808 :
    ThetaLowerSegment 2069399808 2069530880 (20693414161027 / 10000)
      (206947250016931 / 100000) := by
  exact
    packedTile65536 2069399808 2069530880 14 6111 45490 31 _ _ (2145051 / 100000) (1072527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069530880 :
    ThetaLowerSegment 2069530880 2069661952 (206947250016931 / 100000)
      (103480037656367 / 50000) := by
  exact
    packedTile65536 2069530880 2069661952 14 5979 45492 31 _ _ (2145057 / 100000) (107253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069661952 :
    ThetaLowerSegment 2069661952 2069793024 (103480037656367 / 50000)
      (103486610132463 / 50000) := by
  exact
    packedTile65536 2069661952 2069793024 14 6128 45493 31 _ _ (268133 / 12500) (2145067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069793024 :
    ThetaLowerSegment 2069793024 2069924096 (103486610132463 / 50000)
      (103493212657923 / 50000) := by
  exact
    packedTile65536 2069793024 2069924096 14 6156 45494 31 _ _ (214507 / 10000) (2145073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2069924096 :
    ThetaLowerSegment 2069924096 2070055168 (103493212657923 / 50000)
      (103499803403933 / 50000) := by
  exact
    packedTile65536 2069924096 2070055168 14 6145 45496 31 _ _ (536269 / 25000) (2145079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070055168 :
    ThetaLowerSegment 2070055168 2070186240 (103499803403933 / 50000)
      (207012492321447 / 100000) := by
  exact
    packedTile65536 2070055168 2070186240 14 6007 45497 31 _ _ (2145083 / 100000) (1072543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070186240 :
    ThetaLowerSegment 2070186240 2070317312 (207012492321447 / 100000)
      (207025573074169 / 100000) := by
  exact
    packedTile65536 2070186240 2070317312 14 6098 45499 31 _ _ (2145089 / 100000) (536273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070317312 :
    ThetaLowerSegment 2070317312 2070448384 (207025573074169 / 100000)
      (25879855060843 / 12500) := by
  exact
    packedTile65536 2070317312 2070448384 14 6185 45500 31 _ _ (429019 / 20000) (1072549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070448384 :
    ThetaLowerSegment 2070448384 2070579456 (25879855060843 / 12500) (51762997490501 / 25000) := by
  exact
    packedTile65536 2070448384 2070579456 14 6130 45502 31 _ _ (1072551 / 50000) (429021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070579456 :
    ThetaLowerSegment 2070579456 2070710528 (51762997490501 / 25000) (51766274142971 / 25000) := by
  exact
    packedTile65536 2070579456 2070710528 14 6110 45503 31 _ _ (536277 / 25000) (2145111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070710528 :
    ThetaLowerSegment 2070710528 2070841600 (51766274142971 / 25000) (103539087665971 / 50000) := by
  exact
    packedTile65536 2070710528 2070841600 14 6097 45505 31 _ _ (1072557 / 50000) (2145117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070841600 :
    ThetaLowerSegment 2070841600 2070972672 (103539087665971 / 50000)
      (207091219812743 / 100000) := by
  exact
    packedTile65536 2070841600 2070972672 14 6081 45506 31 _ _ (2145121 / 100000) (536281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2070972672 :
    ThetaLowerSegment 2070972672 2071103744 (207091219812743 / 100000)
      (51776084316087 / 25000) := by
  exact
    packedTile65536 2070972672 2071103744 14 6115 45507 31 _ _ (2145127 / 100000) (214513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071103744 :
    ThetaLowerSegment 2071103744 2071234816 (51776084316087 / 25000) (20711736680219 / 10000) := by
  exact
    packedTile65536 2071103744 2071234816 14 6074 45509 31 _ _ (2145133 / 100000) (134071 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071234816 :
    ThetaLowerSegment 2071234816 2071365888 (20711736680219 / 10000) (20713046288189 / 10000) := by
  exact
    packedTile65536 2071234816 2071365888 14 6105 45510 31 _ _ (107257 / 5000) (2145143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071365888 :
    ThetaLowerSegment 2071365888 2071496960 (20713046288189 / 10000) (103571675459529 / 50000) := by
  exact
    packedTile65536 2071365888 2071496960 14 6008 45512 31 _ _ (1072573 / 50000) (2145149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071496960 :
    ThetaLowerSegment 2071496960 2071628032 (103571675459529 / 50000)
      (103578227826313 / 50000) := by
  exact
    packedTile65536 2071496960 2071628032 14 6109 45513 31 _ _ (67036 / 3125) (429031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071628032 :
    ThetaLowerSegment 2071628032 2071759104 (103578227826313 / 50000)
      (207169684848179 / 100000) := by
  exact
    packedTile65536 2071628032 2071759104 14 6167 45515 31 _ _ (2145159 / 100000) (1072581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071759104 :
    ThetaLowerSegment 2071759104 2071890176 (207169684848179 / 100000)
      (103591375524097 / 50000) := by
  exact
    packedTile65536 2071759104 2071890176 14 6091 45516 31 _ _ (429033 / 20000) (134073 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2071890176 :
    ThetaLowerSegment 2071890176 2072021248 (103591375524097 / 50000)
      (103597888263253 / 50000) := by
  exact
    packedTile65536 2071890176 2072021248 14 6072 45518 31 _ _ (2145171 / 100000) (1072587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072021248 :
    ThetaLowerSegment 2072021248 2072152320 (103597888263253 / 50000)
      (103604473959713 / 50000) := by
  exact
    packedTile65536 2072021248 2072152320 14 6140 45519 31 _ _ (1072589 / 50000) (2145181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072152320 :
    ThetaLowerSegment 2072152320 2072283392 (103604473959713 / 50000) (20722193915373 / 10000) := by
  exact
    packedTile65536 2072152320 2072283392 14 6056 45520 31 _ _ (67037 / 3125) (2145187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072283392 :
    ThetaLowerSegment 2072283392 2072414464 (20722193915373 / 10000) (20723499048969 / 10000) := by
  exact
    packedTile65536 2072283392 2072414464 14 6084 45522 31 _ _ (214519 / 10000) (2145193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072414464 :
    ThetaLowerSegment 2072414464 2072545536 (20723499048969 / 10000)
      (207248219919589 / 100000) := by
  exact
    packedTile65536 2072414464 2072545536 14 6167 45523 31 _ _ (2145197 / 100000) (5363 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072545536 :
    ThetaLowerSegment 2072545536 2072676608 (207248219919589 / 100000)
      (51815322660367 / 25000) := by
  exact
    packedTile65536 2072545536 2072676608 14 6093 45525 31 _ _ (2145203 / 100000) (1072603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072676608 :
    ThetaLowerSegment 2072676608 2072807680 (51815322660367 / 25000)
      (207274387142413 / 100000) := by
  exact
    packedTile65536 2072676608 2072807680 14 6105 45526 31 _ _ (2145209 / 100000) (536303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072807680 :
    ThetaLowerSegment 2072807680 2072938752 (207274387142413 / 100000)
      (207287425759183 / 100000) := by
  exact
    packedTile65536 2072807680 2072938752 14 6078 45528 31 _ _ (429043 / 20000) (1072609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2072938752 :
    ThetaLowerSegment 2072938752 2073069824 (207287425759183 / 100000)
      (207300498742051 / 100000) := by
  exact
    packedTile65536 2072938752 2073069824 14 6094 45529 31 _ _ (1072611 / 50000) (85809 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073069824 :
    ThetaLowerSegment 2073069824 2073200896 (207300498742051 / 100000)
      (207313584632851 / 100000) := by
  exact
    packedTile65536 2073069824 2073200896 14 6100 45530 31 _ _ (536307 / 25000) (2145231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073200896 :
    ThetaLowerSegment 2073200896 2073331968 (207313584632851 / 100000)
      (41465330250629 / 20000) := by
  exact
    packedTile65536 2073200896 2073331968 14 6091 45532 31 _ _ (1072617 / 50000) (2145237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073331968 :
    ThetaLowerSegment 2073331968 2073463040 (41465330250629 / 20000) (51834980964803 / 25000) := by
  exact
    packedTile65536 2073331968 2073463040 14 6187 45533 31 _ _ (2145241 / 100000) (536311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073463040 :
    ThetaLowerSegment 2073463040 2073594112 (51834980964803 / 25000)
      (207353209373883 / 100000) := by
  exact
    packedTile65536 2073463040 2073594112 14 6193 45535 31 _ _ (2145247 / 100000) (8581 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073594112 :
    ThetaLowerSegment 2073594112 2073725184 (207353209373883 / 100000)
      (20736633617699 / 10000) := by
  exact
    packedTile65536 2073594112 2073725184 14 6119 45536 31 _ _ (2145253 / 100000) (268157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073725184 :
    ThetaLowerSegment 2073725184 2073856256 (20736633617699 / 10000) (165903625337 / 80) := by
  exact
    packedTile65536 2073725184 2073856256 14 6151 45538 31 _ _ (107263 / 5000) (2145263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073856256 :
    ThetaLowerSegment 2073856256 2073987328 (165903625337 / 80) (51848187163769 / 25000) := by
  exact
    packedTile65536 2073856256 2073987328 14 6161 45539 31 _ _ (1072633 / 50000) (2145269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2073987328 :
    ThetaLowerSegment 2073987328 2074118400 (51848187163769 / 25000) (51851468893611 / 25000) := by
  exact
    packedTile65536 2073987328 2074118400 14 6119 45541 31 _ _ (268159 / 12500) (85811 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074118400 :
    ThetaLowerSegment 2074118400 2074249472 (51851468893611 / 25000)
      (207418890982137 / 100000) := by
  exact
    packedTile65536 2074118400 2074249472 14 6067 45542 31 _ _ (2145279 / 100000) (1072641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074249472 :
    ThetaLowerSegment 2074249472 2074380544 (207418890982137 / 100000) (6482245466856 / 3125) := by
  exact
    packedTile65536 2074249472 2074380544 14 6043 45543 31 _ _ (429057 / 20000) (268161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074380544 :
    ThetaLowerSegment 2074380544 2074511616 (6482245466856 / 3125) (6482657362728 / 3125) := by
  exact
    packedTile65536 2074380544 2074511616 14 6144 45545 31 _ _ (2145291 / 100000) (1072647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074511616 :
    ThetaLowerSegment 2074511616 2074642688 (6482657362728 / 3125) (103729111377051 / 50000) := by
  exact
    packedTile65536 2074511616 2074642688 14 6147 45546 31 _ _ (1072649 / 50000) (2145301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074642688 :
    ThetaLowerSegment 2074642688 2074773760 (103729111377051 / 50000)
      (103735671716683 / 50000) := by
  exact
    packedTile65536 2074642688 2074773760 14 6116 45548 31 _ _ (268163 / 12500) (2145307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074773760 :
    ThetaLowerSegment 2074773760 2074904832 (103735671716683 / 50000)
      (103742313596443 / 50000) := by
  exact
    packedTile65536 2074773760 2074904832 14 6192 45549 31 _ _ (214531 / 10000) (2145313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2074904832 :
    ThetaLowerSegment 2074904832 2075035904 (103742313596443 / 50000)
      (207497698609367 / 100000) := by
  exact
    packedTile65536 2074904832 2075035904 14 6093 45551 31 _ _ (2145317 / 100000) (53633 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075035904 :
    ThetaLowerSegment 2075035904 2075166976 (207497698609367 / 100000)
      (51877697878909 / 25000) := by
  exact
    packedTile65536 2075035904 2075166976 14 6103 45552 31 _ _ (2145323 / 100000) (1072663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075166976 :
    ThetaLowerSegment 2075166976 2075298048 (51877697878909 / 25000) (41504810358837 / 20000) := by
  exact
    packedTile65536 2075166976 2075298048 14 6181 45554 31 _ _ (2145329 / 100000) (536333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075298048 :
    ThetaLowerSegment 2075298048 2075429120 (41504810358837 / 20000) (41507464139469 / 20000) := by
  exact
    packedTile65536 2075298048 2075429120 14 6185 45555 31 _ _ (268167 / 12500) (2145339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075429120 :
    ThetaLowerSegment 2075429120 2075560192 (41507464139469 / 20000)
      (207550212057423 / 100000) := by
  exact
    packedTile65536 2075429120 2075560192 14 6009 45556 31 _ _ (1072671 / 50000) (429069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075560192 :
    ThetaLowerSegment 2075560192 2075691264 (207550212057423 / 100000)
      (41512631417451 / 20000) := by
  exact
    packedTile65536 2075560192 2075691264 14 6034 45558 31 _ _ (536337 / 25000) (2145351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075691264 :
    ThetaLowerSegment 2075691264 2075822336 (41512631417451 / 20000) (41515256473829 / 20000) := by
  exact
    packedTile65536 2075691264 2075822336 14 6118 45559 31 _ _ (429071 / 20000) (1072679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075822336 :
    ThetaLowerSegment 2075822336 2075953408 (41515256473829 / 20000) (25948695537387 / 12500) := by
  exact
    packedTile65536 2075822336 2075953408 14 6191 45561 31 _ _ (2145361 / 100000) (536341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2075953408 :
    ThetaLowerSegment 2075953408 2076084480 (25948695537387 / 12500) (51900654177981 / 25000) := by
  exact
    packedTile65536 2075953408 2076084480 14 6084 45562 31 _ _ (2145367 / 100000) (214537 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076084480 :
    ThetaLowerSegment 2076084480 2076215552 (51900654177981 / 25000) (41523130828729 / 20000) := by
  exact
    packedTile65536 2076084480 2076215552 14 6077 45564 31 _ _ (2145373 / 100000) (67043 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076215552 :
    ThetaLowerSegment 2076215552 2076346624 (41523130828729 / 20000) (41525749908633 / 20000) := by
  exact
    packedTile65536 2076215552 2076346624 14 6104 45565 31 _ _ (107269 / 5000) (2145383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076346624 :
    ThetaLowerSegment 2076346624 2076477696 (41525749908633 / 20000)
      (207641776326957 / 100000) := by
  exact
    packedTile65536 2076346624 2076477696 14 6072 45566 31 _ _ (1072693 / 50000) (2145389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076477696 :
    ThetaLowerSegment 2076477696 2076608768 (207641776326957 / 100000)
      (41530993668473 / 20000) := by
  exact
    packedTile65536 2076477696 2076608768 14 6149 45568 31 _ _ (134087 / 6250) (429079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076608768 :
    ThetaLowerSegment 2076608768 2076739840 (41530993668473 / 20000) (20766783000937 / 10000) := by
  exact
    packedTile65536 2076608768 2076739840 14 5995 45569 31 _ _ (2145399 / 100000) (1072701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076739840 :
    ThetaLowerSegment 2076739840 2076870912 (20766783000937 / 10000) (41536168378139 / 20000) := by
  exact
    packedTile65536 2076739840 2076870912 14 6065 45571 31 _ _ (429081 / 20000) (67044 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2076870912 :
    ThetaLowerSegment 2076870912 2077001984 (41536168378139 / 20000) (51923496705973 / 25000) := by
  exact
    packedTile65536 2076870912 2077001984 14 6127 45572 31 _ _ (2145411 / 100000) (1072707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077001984 :
    ThetaLowerSegment 2077001984 2077133056 (51923496705973 / 25000) (103853518700793 / 50000) := by
  exact
    packedTile65536 2077001984 2077133056 14 6083 45574 31 _ _ (1072709 / 50000) (2145421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077133056 :
    ThetaLowerSegment 2077133056 2077264128 (103853518700793 / 50000)
      (103860042935177 / 50000) := by
  exact
    packedTile65536 2077133056 2077264128 14 6082 45575 31 _ _ (134089 / 6250) (2145427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077264128 :
    ThetaLowerSegment 2077264128 2077395200 (103860042935177 / 50000) (25966652255923 / 12500) := by
  exact
    packedTile65536 2077264128 2077395200 14 6121 45577 31 _ _ (214543 / 10000) (2145433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077395200 :
    ThetaLowerSegment 2077395200 2077526272 (25966652255923 / 12500) (10387307537081 / 5000) := by
  exact
    packedTile65536 2077395200 2077526272 14 6028 45578 31 _ _ (2145437 / 100000) (13409 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077526272 :
    ThetaLowerSegment 2077526272 2077657344 (10387307537081 / 5000) (25969906888433 / 12500) := by
  exact
    packedTile65536 2077526272 2077657344 14 6108 45579 31 _ _ (2145443 / 100000) (1072723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077657344 :
    ThetaLowerSegment 2077657344 2077788416 (25969906888433 / 12500) (20777232947367 / 10000) := by
  exact
    packedTile65536 2077657344 2077788416 14 6094 45581 31 _ _ (2145449 / 100000) (536363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077788416 :
    ThetaLowerSegment 2077788416 2077919488 (20777232947367 / 10000) (41557085495289 / 20000) := by
  exact
    packedTile65536 2077788416 2077919488 14 6105 45582 31 _ _ (429091 / 20000) (1072729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2077919488 :
    ThetaLowerSegment 2077919488 2078050560 (41557085495289 / 20000)
      (207798624213207 / 100000) := by
  exact
    packedTile65536 2077919488 2078050560 14 6151 45584 31 _ _ (1072731 / 50000) (429093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078050560 :
    ThetaLowerSegment 2078050560 2078181632 (207798624213207 / 100000)
      (41562368488311 / 20000) := by
  exact
    packedTile65536 2078050560 2078181632 14 6161 45585 31 _ _ (536367 / 25000) (2145471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078181632 :
    ThetaLowerSegment 2078181632 2078312704 (41562368488311 / 20000)
      (207825103616349 / 100000) := by
  exact
    packedTile65536 2078181632 2078312704 14 6181 45587 31 _ _ (1072737 / 50000) (2145477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078312704 :
    ThetaLowerSegment 2078312704 2078443776 (207825103616349 / 100000)
      (207838088067361 / 100000) := by
  exact
    packedTile65536 2078312704 2078443776 14 6052 45588 31 _ _ (2145481 / 100000) (536371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078443776 :
    ThetaLowerSegment 2078443776 2078574848 (207838088067361 / 100000)
      (207851295685333 / 100000) := by
  exact
    packedTile65536 2078443776 2078574848 14 6156 45589 31 _ _ (2145487 / 100000) (214549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078574848 :
    ThetaLowerSegment 2078574848 2078705920 (207851295685333 / 100000) (2078646385063 / 1000) := by
  exact
    packedTile65536 2078574848 2078705920 14 6219 45591 31 _ _ (2145493 / 100000) (268187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078705920 :
    ThetaLowerSegment 2078705920 2078836992 (2078646385063 / 1000) (1039389198839 / 500) := by
  exact
    packedTile65536 2078705920 2078836992 14 6153 45592 31 _ _ (4291 / 200) (2145503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078836992 :
    ThetaLowerSegment 2078836992 2078968064 (1039389198839 / 500) (20789083080663 / 10000) := by
  exact
    packedTile65536 2078836992 2078968064 14 6055 45594 31 _ _ (1072753 / 50000) (2145509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2078968064 :
    ThetaLowerSegment 2078968064 2079099136 (20789083080663 / 10000) (103951944196331 / 50000) := by
  exact
    packedTile65536 2078968064 2079099136 14 6086 45595 31 _ _ (268189 / 12500) (429103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079099136 :
    ThetaLowerSegment 2079099136 2079230208 (103951944196331 / 50000)
      (207916879510207 / 100000) := by
  exact
    packedTile65536 2079099136 2079230208 14 6055 45597 31 _ _ (2145519 / 100000) (1072761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079230208 :
    ThetaLowerSegment 2079230208 2079361280 (207916879510207 / 100000)
      (103965038317241 / 50000) := by
  exact
    packedTile65536 2079230208 2079361280 14 6151 45598 31 _ _ (85821 / 4000) (268191 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079361280 :
    ThetaLowerSegment 2079361280 2079492352 (103965038317241 / 50000) (51985792166161 / 25000) := by
  exact
    packedTile65536 2079361280 2079492352 14 6102 45600 31 _ _ (2145531 / 100000) (1072767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079492352 :
    ThetaLowerSegment 2079492352 2079623424 (51985792166161 / 25000) (103978151821079 / 50000) := by
  exact
    packedTile65536 2079492352 2079623424 14 6122 45601 31 _ _ (2145537 / 100000) (107277 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079623424 :
    ThetaLowerSegment 2079623424 2079754496 (103978151821079 / 50000) (20796933353087 / 10000) := by
  exact
    packedTile65536 2079623424 2079754496 14 6073 45602 31 _ _ (268193 / 12500) (2145547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079754496 :
    ThetaLowerSegment 2079754496 2079885568 (20796933353087 / 10000) (20798246000577 / 10000) := by
  exact
    packedTile65536 2079754496 2079885568 14 6118 45604 31 _ _ (42911 / 2000) (2145553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2079885568 :
    ThetaLowerSegment 2079885568 2080016640 (20798246000577 / 10000) (20799563371961 / 10000) := by
  exact
    packedTile65536 2079885568 2080016640 14 6140 45605 31 _ _ (536389 / 25000) (2145559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080016640 :
    ThetaLowerSegment 2080016640 2080147712 (20799563371961 / 10000) (104004287877813 / 50000) := by
  exact
    packedTile65536 2080016640 2080147712 14 6032 45607 31 _ _ (2145563 / 100000) (1072783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080147712 :
    ThetaLowerSegment 2080147712 2080278784 (104004287877813 / 50000) (52005479225917 / 25000) := by
  exact
    packedTile65536 2080147712 2080278784 14 6218 45608 31 _ _ (2145569 / 100000) (536393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080278784 :
    ThetaLowerSegment 2080278784 2080409856 (52005479225917 / 25000)
      (208035002765593 / 100000) := by
  exact
    packedTile65536 2080278784 2080409856 14 6099 45610 31 _ _ (85823 / 4000) (1072789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080409856 :
    ThetaLowerSegment 2080409856 2080540928 (208035002765593 / 100000)
      (208047917023651 / 100000) := by
  exact
    packedTile65536 2080409856 2080540928 14 6019 45611 31 _ _ (1072791 / 50000) (429117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080540928 :
    ThetaLowerSegment 2080540928 2080672000 (208047917023651 / 100000)
      (208060985800159 / 100000) := by
  exact
    packedTile65536 2080540928 2080672000 14 6091 45612 31 _ _ (536397 / 25000) (2145591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080672000 :
    ThetaLowerSegment 2080672000 2080803072 (208060985800159 / 100000)
      (208074166184101 / 100000) := by
  exact
    packedTile65536 2080672000 2080803072 14 6143 45614 31 _ _ (1072797 / 50000) (2145597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080803072 :
    ThetaLowerSegment 2080803072 2080934144 (208074166184101 / 100000)
      (208087250052901 / 100000) := by
  exact
    packedTile65536 2080803072 2080934144 14 6098 45615 31 _ _ (2682 / 125) (2145603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2080934144 :
    ThetaLowerSegment 2080934144 2081065216 (208087250052901 / 100000) (8324007694173 / 4000) := by
  exact
    packedTile65536 2080934144 2081065216 14 6032 45617 31 _ _ (2145607 / 100000) (214561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081065216 :
    ThetaLowerSegment 2081065216 2081196288 (8324007694173 / 4000) (208113370709371 / 100000) := by
  exact
    packedTile65536 2081065216 2081196288 14 6142 45618 31 _ _ (2145613 / 100000) (134101 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081196288 :
    ThetaLowerSegment 2081196288 2081327360 (208113370709371 / 100000)
      (208126467567747 / 100000) := by
  exact
    packedTile65536 2081196288 2081327360 14 6104 45620 31 _ _ (2145619 / 100000) (1072811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081327360 :
    ThetaLowerSegment 2081327360 2081458432 (208126467567747 / 100000)
      (208139693206411 / 100000) := by
  exact
    packedTile65536 2081327360 2081458432 14 6164 45621 31 _ _ (1072813 / 50000) (2145629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081458432 :
    ThetaLowerSegment 2081458432 2081589504 (208139693206411 / 100000)
      (208152895280107 / 100000) := by
  exact
    packedTile65536 2081458432 2081589504 14 6153 45623 31 _ _ (67051 / 3125) (429127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081589504 :
    ThetaLowerSegment 2081589504 2081720576 (208152895280107 / 100000)
      (208166099536359 / 100000) := by
  exact
    packedTile65536 2081589504 2081720576 14 6154 45624 31 _ _ (1072819 / 50000) (2145641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081720576 :
    ThetaLowerSegment 2081720576 2081851648 (208166099536359 / 100000)
      (104089622951637 / 50000) := by
  exact
    packedTile65536 2081720576 2081851648 14 6127 45625 31 _ _ (429129 / 20000) (134103 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081851648 :
    ThetaLowerSegment 2081851648 2081982720 (104089622951637 / 50000)
      (104096137148073 / 50000) := by
  exact
    packedTile65536 2081851648 2081982720 14 6072 45627 31 _ _ (2145651 / 100000) (1072827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2081982720 :
    ThetaLowerSegment 2081982720 2082113792 (104096137148073 / 50000)
      (208205373532131 / 100000) := by
  exact
    packedTile65536 2081982720 2082113792 14 6105 45628 31 _ _ (2145657 / 100000) (107283 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082113792 :
    ThetaLowerSegment 2082113792 2082244864 (208205373532131 / 100000)
      (208218535028973 / 100000) := by
  exact
    packedTile65536 2082113792 2082244864 14 6134 45630 31 _ _ (2145663 / 100000) (1072833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082244864 :
    ThetaLowerSegment 2082244864 2082375936 (208218535028973 / 100000)
      (208231718025453 / 100000) := by
  exact
    packedTile65536 2082244864 2082375936 14 6144 45631 31 _ _ (214567 / 10000) (2145673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082375936 :
    ThetaLowerSegment 2082375936 2082507008 (208231718025453 / 100000)
      (208244798066349 / 100000) := by
  exact
    packedTile65536 2082375936 2082507008 14 6096 45633 31 _ _ (536419 / 25000) (2145679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082507008 :
    ThetaLowerSegment 2082507008 2082638080 (208244798066349 / 100000)
      (208257985427921 / 100000) := by
  exact
    packedTile65536 2082507008 2082638080 14 6146 45634 31 _ _ (1072841 / 50000) (429137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082638080 :
    ThetaLowerSegment 2082638080 2082769152 (208257985427921 / 100000)
      (41654213109613 / 20000) := by
  exact
    packedTile65536 2082638080 2082769152 14 6096 45635 31 _ _ (2145689 / 100000) (536423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082769152 :
    ThetaLowerSegment 2082769152 2082900224 (41654213109613 / 20000) (8331372866071 / 4000) := by
  exact
    packedTile65536 2082769152 2082900224 14 6178 45637 31 _ _ (429139 / 20000) (1072849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2082900224 :
    ThetaLowerSegment 2082900224 2083031296 (8331372866071 / 4000) (208297440467689 / 100000) := by
  exact
    packedTile65536 2082900224 2083031296 14 6114 45638 31 _ _ (2145701 / 100000) (268213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083031296 :
    ThetaLowerSegment 2083031296 2083162368 (208297440467689 / 100000)
      (208310636571889 / 100000) := by
  exact
    packedTile65536 2083031296 2083162368 14 6150 45640 31 _ _ (536427 / 25000) (2145711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083162368 :
    ThetaLowerSegment 2083162368 2083293440 (208310636571889 / 100000)
      (208323716844433 / 100000) := by
  exact
    packedTile65536 2083162368 2083293440 14 6096 45641 31 _ _ (1072857 / 50000) (2145717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083293440 :
    ThetaLowerSegment 2083293440 2083424512 (208323716844433 / 100000)
      (208336689867553 / 100000) := by
  exact
    packedTile65536 2083293440 2083424512 14 6046 45643 31 _ _ (53643 / 2500) (2145723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083424512 :
    ThetaLowerSegment 2083424512 2083555584 (208336689867553 / 100000)
      (208349806690591 / 100000) := by
  exact
    packedTile65536 2083424512 2083555584 14 6113 45644 31 _ _ (1072863 / 50000) (2145729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083555584 :
    ThetaLowerSegment 2083555584 2083686656 (208349806690591 / 100000)
      (104181442466613 / 50000) := by
  exact
    packedTile65536 2083555584 2083686656 14 6095 45645 31 _ _ (2145733 / 100000) (268217 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083686656 :
    ThetaLowerSegment 2083686656 2083817728 (104181442466613 / 50000)
      (208375984669821 / 100000) := by
  exact
    packedTile65536 2083686656 2083817728 14 6105 45647 31 _ _ (2145739 / 100000) (1072871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083817728 :
    ThetaLowerSegment 2083817728 2083948800 (208375984669821 / 100000)
      (208389155252631 / 100000) := by
  exact
    packedTile65536 2083817728 2083948800 14 6138 45648 31 _ _ (429149 / 20000) (536437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2083948800 :
    ThetaLowerSegment 2083948800 2084079872 (208389155252631 / 100000)
      (41680492641307 / 20000) := by
  exact
    packedTile65536 2083948800 2084079872 14 6202 45650 31 _ _ (268219 / 12500) (429151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084079872 :
    ThetaLowerSegment 2084079872 2084210944 (41680492641307 / 20000)
      (208415384961211 / 100000) := by
  exact
    packedTile65536 2084079872 2084210944 14 6022 45651 31 _ _ (1072879 / 50000) (2145761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084210944 :
    ThetaLowerSegment 2084210944 2084342016 (208415384961211 / 100000) (8337141196459 / 4000) := by
  exact
    packedTile65536 2084210944 2084342016 14 6126 45653 31 _ _ (536441 / 25000) (2145767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084342016 :
    ThetaLowerSegment 2084342016 2084473088 (8337141196459 / 4000) (41688312234537 / 20000) := by
  exact
    packedTile65536 2084342016 2084473088 14 6073 45654 31 _ _ (214577 / 10000) (2145773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084473088 :
    ThetaLowerSegment 2084473088 2084604160 (41688312234537 / 20000) (104227218990231 / 50000) := by
  exact
    packedTile65536 2084473088 2084604160 14 6001 45656 31 _ _ (2145777 / 100000) (107289 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084604160 :
    ThetaLowerSegment 2084604160 2084735232 (104227218990231 / 50000)
      (104233733587419 / 50000) := by
  exact
    packedTile65536 2084604160 2084735232 14 6072 45657 31 _ _ (2145783 / 100000) (1072893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084735232 :
    ThetaLowerSegment 2084735232 2084866304 (104233733587419 / 50000) (4169611473081 / 2000) := by
  exact
    packedTile65536 2084735232 2084866304 14 6108 45658 31 _ _ (2145789 / 100000) (67056 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084866304 :
    ThetaLowerSegment 2084866304 2084997376 (4169611473081 / 2000) (20849378102843 / 10000) := by
  exact
    packedTile65536 2084866304 2084997376 14 6155 45660 31 _ _ (536449 / 25000) (2145799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2084997376 :
    ThetaLowerSegment 2084997376 2085128448 (20849378102843 / 10000) (104253523188197 / 50000) := by
  exact
    packedTile65536 2084997376 2085128448 14 6182 45661 31 _ _ (1072901 / 50000) (429161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085128448 :
    ThetaLowerSegment 2085128448 2085259520 (104253523188197 / 50000)
      (104260095798101 / 50000) := by
  exact
    packedTile65536 2085128448 2085259520 14 6126 45663 31 _ _ (134113 / 6250) (2145811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085259520 :
    ThetaLowerSegment 2085259520 2085390592 (104260095798101 / 50000) (52133304708249 / 25000) := by
  exact
    packedTile65536 2085259520 2085390592 14 6071 45664 31 _ _ (1072907 / 50000) (2145817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085390592 :
    ThetaLowerSegment 2085390592 2085521664 (52133304708249 / 25000)
      (208546314778559 / 100000) := by
  exact
    packedTile65536 2085390592 2085521664 14 6103 45666 31 _ _ (2145821 / 100000) (67057 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085521664 :
    ThetaLowerSegment 2085521664 2085652736 (208546314778559 / 100000) (13034959417349 / 6250) := by
  exact
    packedTile65536 2085521664 2085652736 14 6075 45667 31 _ _ (2145827 / 100000) (214583 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085652736 :
    ThetaLowerSegment 2085652736 2085783808 (13034959417349 / 6250) (208572442404717 / 100000) := by
  exact
    packedTile65536 2085652736 2085783808 14 6101 45668 31 _ _ (2145833 / 100000) (536459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085783808 :
    ThetaLowerSegment 2085783808 2085914880 (208572442404717 / 100000)
      (208585429028397 / 100000) := by
  exact
    packedTile65536 2085783808 2085914880 14 6052 45670 31 _ _ (26823 / 1250) (2145843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2085914880 :
    ThetaLowerSegment 2085914880 2086045952 (208585429028397 / 100000)
      (208598598085299 / 100000) := by
  exact
    packedTile65536 2085914880 2086045952 14 6137 45671 31 _ _ (1072923 / 50000) (2145849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086045952 :
    ThetaLowerSegment 2086045952 2086177024 (208598598085299 / 100000)
      (208611664178127 / 100000) := by
  exact
    packedTile65536 2086045952 2086177024 14 6089 45673 31 _ _ (536463 / 25000) (429171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086177024 :
    ThetaLowerSegment 2086177024 2086308096 (208611664178127 / 100000)
      (208624640181453 / 100000) := by
  exact
    packedTile65536 2086177024 2086308096 14 6047 45674 31 _ _ (1072929 / 50000) (2145861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086308096 :
    ThetaLowerSegment 2086308096 2086439168 (208624640181453 / 100000)
      (208637725666223 / 100000) := by
  exact
    packedTile65536 2086308096 2086439168 14 6098 45676 31 _ _ (429173 / 20000) (536467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086439168 :
    ThetaLowerSegment 2086439168 2086570240 (208637725666223 / 100000)
      (208650832646291 / 100000) := by
  exact
    packedTile65536 2086439168 2086570240 14 6108 45677 31 _ _ (2145871 / 100000) (1072937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086570240 :
    ThetaLowerSegment 2086570240 2086701312 (208650832646291 / 100000)
      (41732755315271 / 20000) := by
  exact
    packedTile65536 2086570240 2086701312 14 6032 45678 31 _ _ (2145877 / 100000) (53647 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086701312 :
    ThetaLowerSegment 2086701312 2086832384 (41732755315271 / 20000)
      (208676907240551 / 100000) := by
  exact
    packedTile65536 2086701312 2086832384 14 6119 45680 31 _ _ (536471 / 25000) (2145887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086832384 :
    ThetaLowerSegment 2086832384 2086963456 (208676907240551 / 100000)
      (208690216050331 / 100000) := by
  exact
    packedTile65536 2086832384 2086963456 14 6202 45681 31 _ _ (214589 / 10000) (2145893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2086963456 :
    ThetaLowerSegment 2086963456 2087094528 (208690216050331 / 100000)
      (208703295286451 / 100000) := by
  exact
    packedTile65536 2086963456 2087094528 14 6095 45683 31 _ _ (268237 / 12500) (2145899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087094528 :
    ThetaLowerSegment 2087094528 2087225600 (208703295286451 / 100000)
      (208716353100121 / 100000) := by
  exact
    packedTile65536 2087094528 2087225600 14 6085 45684 31 _ _ (1072951 / 50000) (429181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087225600 :
    ThetaLowerSegment 2087225600 2087356672 (208716353100121 / 100000)
      (208729528981381 / 100000) := by
  exact
    packedTile65536 2087225600 2087356672 14 6140 45686 31 _ _ (2145909 / 100000) (268239 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087356672 :
    ThetaLowerSegment 2087356672 2087487744 (208729528981381 / 100000)
      (208742361553081 / 100000) := by
  exact
    packedTile65536 2087356672 2087487744 14 5980 45687 31 _ _ (429183 / 20000) (1072959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087487744 :
    ThetaLowerSegment 2087487744 2087618816 (208742361553081 / 100000)
      (208755421628287 / 100000) := by
  exact
    packedTile65536 2087487744 2087618816 14 6086 45689 31 _ _ (2145921 / 100000) (536481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087618816 :
    ThetaLowerSegment 2087618816 2087749888 (208755421628287 / 100000) (10438429773707 / 5000) := by
  exact
    packedTile65536 2087618816 2087749888 14 6139 45690 31 _ _ (2145927 / 100000) (214593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087749888 :
    ThetaLowerSegment 2087749888 2087880960 (10438429773707 / 5000) (4175638649079 / 2000) := by
  exact
    packedTile65536 2087749888 2087880960 14 6215 45691 31 _ _ (1072967 / 50000) (2145937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2087880960 :
    ThetaLowerSegment 2087880960 2088012032 (4175638649079 / 2000) (835180262427 / 400) := by
  exact
    packedTile65536 2087880960 2088012032 14 6120 45693 31 _ _ (107297 / 5000) (2145943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088012032 :
    ThetaLowerSegment 2088012032 2088143104 (835180262427 / 400) (13050504511591 / 6250) := by
  exact
    packedTile65536 2088012032 2088143104 14 6061 45694 31 _ _ (1072973 / 50000) (2145949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088143104 :
    ThetaLowerSegment 2088143104 2088274176 (13050504511591 / 6250) (208821259066641 / 100000) := by
  exact
    packedTile65536 2088143104 2088274176 14 6145 45696 31 _ _ (2145953 / 100000) (536489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088274176 :
    ThetaLowerSegment 2088274176 2088405248 (208821259066641 / 100000)
      (208834370876131 / 100000) := by
  exact
    packedTile65536 2088274176 2088405248 14 6110 45697 31 _ _ (2145959 / 100000) (1072981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088405248 :
    ThetaLowerSegment 2088405248 2088536320 (208834370876131 / 100000)
      (208847401175611 / 100000) := by
  exact
    packedTile65536 2088405248 2088536320 14 6072 45699 31 _ _ (429193 / 20000) (134123 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088536320 :
    ThetaLowerSegment 2088536320 2088667392 (208847401175611 / 100000)
      (26107568692491 / 12500) := by
  exact
    packedTile65536 2088536320 2088667392 14 6127 45700 31 _ _ (2145971 / 100000) (1072987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088667392 :
    ThetaLowerSegment 2088667392 2088798464 (26107568692491 / 12500) (104436821075853 / 50000) := by
  exact
    packedTile65536 2088667392 2088798464 14 6101 45701 31 _ _ (1072989 / 50000) (2145981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088798464 :
    ThetaLowerSegment 2088798464 2088929536 (104436821075853 / 50000)
      (104443287998637 / 50000) := by
  exact
    packedTile65536 2088798464 2088929536 14 6027 45703 31 _ _ (67062 / 3125) (2145987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2088929536 :
    ThetaLowerSegment 2088929536 2089060608 (104443287998637 / 50000)
      (104449893355857 / 50000) := by
  exact
    packedTile65536 2088929536 2089060608 14 6156 45704 31 _ _ (214599 / 10000) (2145993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089060608 :
    ThetaLowerSegment 2089060608 2089191680 (104449893355857 / 50000) (52228265462289 / 25000) := by
  exact
    packedTile65536 2089060608 2089191680 14 6186 45706 31 _ _ (2145997 / 100000) (1073 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089191680 :
    ThetaLowerSegment 2089191680 2089322752 (52228265462289 / 25000) (1671408756203 / 800) := by
  exact
    packedTile65536 2089191680 2089322752 14 6073 45707 31 _ _ (2146003 / 100000) (1073003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089322752 :
    ThetaLowerSegment 2089322752 2089339136 (1671408756203 / 800) (52231942639601 / 25000) := by
  exact
    packedTile65536 2089322752 2089339136 11 781 45709 31 _ _ (2146009 / 100000) (536503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2089339136 :
    ThetaLowerSegment 2089339136 2089341184 (52231942639601 / 25000) (104463976484627 / 50000) := by
  exact
    packedTile65536 2089339136 2089341184 8 85 45709 31 _ _ (214601 / 10000) (2146013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2057341184_2089341184 :
    ThetaLowerSegment 2057341184 2089341184 (205728900255983 / 100000)
      (104463976484627 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2057341184 cell2057472256)
                  (ThetaLowerSegment.join cell2057603328 cell2057734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2057865472 cell2057996544)
                  (ThetaLowerSegment.join cell2058127616 cell2058258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2058389760 cell2058520832)
                  (ThetaLowerSegment.join cell2058651904 cell2058782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2058914048 cell2059045120)
                  (ThetaLowerSegment.join cell2059176192 cell2059307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2059438336 cell2059569408)
                  (ThetaLowerSegment.join cell2059700480 cell2059831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2059962624 cell2060093696)
                  (ThetaLowerSegment.join cell2060224768 cell2060355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2060486912 cell2060617984)
                  (ThetaLowerSegment.join cell2060749056 cell2060880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2061011200 cell2061142272)
                  (ThetaLowerSegment.join cell2061273344 cell2061404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2061535488 cell2061666560)
                  (ThetaLowerSegment.join cell2061797632 cell2061928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2062059776 cell2062190848)
                  (ThetaLowerSegment.join cell2062321920 cell2062452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2062584064 cell2062715136)
                  (ThetaLowerSegment.join cell2062846208 cell2062977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2063108352 cell2063239424)
                  (ThetaLowerSegment.join cell2063370496 cell2063501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2063632640 cell2063763712)
                  (ThetaLowerSegment.join cell2063894784 cell2064025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2064156928 cell2064288000)
                  (ThetaLowerSegment.join cell2064419072 cell2064550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2064681216 cell2064812288)
                  (ThetaLowerSegment.join cell2064943360 cell2065074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2065205504 cell2065336576)
                  (ThetaLowerSegment.join cell2065467648 cell2065598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2065729792 cell2065860864)
                  (ThetaLowerSegment.join cell2065991936 cell2066123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2066254080 cell2066385152)
                  (ThetaLowerSegment.join cell2066516224 cell2066647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2066778368 cell2066909440)
                  (ThetaLowerSegment.join cell2067040512 cell2067171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2067302656 cell2067433728)
                  (ThetaLowerSegment.join cell2067564800 cell2067695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2067826944 cell2067958016)
                  (ThetaLowerSegment.join cell2068089088 cell2068220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2068351232 cell2068482304)
                  (ThetaLowerSegment.join cell2068613376 cell2068744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2068875520 cell2069006592)
                  (ThetaLowerSegment.join cell2069137664 cell2069268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2069399808 cell2069530880)
                  (ThetaLowerSegment.join cell2069661952 cell2069793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2069924096 cell2070055168)
                  (ThetaLowerSegment.join cell2070186240 cell2070317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2070448384 cell2070579456)
                  (ThetaLowerSegment.join cell2070710528 cell2070841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2070972672 cell2071103744)
                  (ThetaLowerSegment.join cell2071234816 cell2071365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2071496960 cell2071628032)
                  (ThetaLowerSegment.join cell2071759104 cell2071890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2072021248 cell2072152320)
                  (ThetaLowerSegment.join cell2072283392 cell2072414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2072545536 cell2072676608)
                  (ThetaLowerSegment.join cell2072807680 cell2072938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2073069824 cell2073200896)
                  (ThetaLowerSegment.join cell2073331968 cell2073463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2073594112 cell2073725184)
                  (ThetaLowerSegment.join cell2073856256 cell2073987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2074118400 cell2074249472)
                  (ThetaLowerSegment.join cell2074380544 cell2074511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2074642688 cell2074773760)
                  (ThetaLowerSegment.join cell2074904832 cell2075035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2075166976 cell2075298048)
                  (ThetaLowerSegment.join cell2075429120 cell2075560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2075691264 cell2075822336)
                  (ThetaLowerSegment.join cell2075953408 cell2076084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2076215552 cell2076346624)
                  (ThetaLowerSegment.join cell2076477696 cell2076608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2076739840 cell2076870912)
                  (ThetaLowerSegment.join cell2077001984 cell2077133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2077264128 cell2077395200)
                  (ThetaLowerSegment.join cell2077526272 cell2077657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2077788416 cell2077919488)
                  (ThetaLowerSegment.join cell2078050560 cell2078181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2078312704 cell2078443776)
                  (ThetaLowerSegment.join cell2078574848 cell2078705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2078836992 cell2078968064)
                  (ThetaLowerSegment.join cell2079099136 cell2079230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2079361280 cell2079492352)
                  (ThetaLowerSegment.join cell2079623424 cell2079754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2079885568 cell2080016640)
                  (ThetaLowerSegment.join cell2080147712 cell2080278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2080409856 cell2080540928)
                  (ThetaLowerSegment.join cell2080672000 cell2080803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2080934144 cell2081065216)
                  (ThetaLowerSegment.join cell2081196288 cell2081327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2081458432 cell2081589504)
                  (ThetaLowerSegment.join cell2081720576 cell2081851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2081982720 cell2082113792)
                  (ThetaLowerSegment.join cell2082244864 cell2082375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2082507008 cell2082638080)
                  (ThetaLowerSegment.join cell2082769152 cell2082900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2083031296 cell2083162368)
                  (ThetaLowerSegment.join cell2083293440 cell2083424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2083555584 cell2083686656)
                  (ThetaLowerSegment.join cell2083817728 cell2083948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2084079872 cell2084210944)
                  (ThetaLowerSegment.join cell2084342016 cell2084473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2084604160 cell2084735232)
                  (ThetaLowerSegment.join cell2084866304 cell2084997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2085128448 cell2085259520)
                  (ThetaLowerSegment.join cell2085390592 cell2085521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2085652736 cell2085783808)
                  (ThetaLowerSegment.join cell2085914880 cell2086045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2086177024 cell2086308096)
                  (ThetaLowerSegment.join cell2086439168 cell2086570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2086701312 cell2086832384)
                  (ThetaLowerSegment.join cell2086963456 cell2087094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2087225600 cell2087356672)
                  (ThetaLowerSegment.join cell2087487744 cell2087618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2087749888 cell2087880960)
                  (ThetaLowerSegment.join cell2088012032 cell2088143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2088274176 cell2088405248)
                  (ThetaLowerSegment.join cell2088536320 cell2088667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2088798464 cell2088929536)
                (ThetaLowerSegment.join cell2089060608 cell2089191680))
              (ThetaLowerSegment.join cell2089322752 cell2089339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
