/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2985341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2953341184 :
    ThetaLowerSegment 2953341184 2953472256 (295328588872647 / 100000) (5906835065391 / 2000) := by
  exact
    packedTile65536 2953341184 2953472256 14 6037 54344 31 _ _ (2180619 / 100000) (1090311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953472256 :
    ThetaLowerSegment 2953472256 2953603328 (5906835065391 / 2000) (295354900245617 / 100000) := by
  exact
    packedTile65536 2953472256 2953603328 14 6029 54345 31 _ _ (2180623 / 100000) (1090313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953603328 :
    ThetaLowerSegment 2953603328 2953734400 (295354900245617 / 100000)
      (295367809563377 / 100000) := by
  exact
    packedTile65536 2953603328 2953734400 14 5920 54347 31 _ _ (545157 / 25000) (2180631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953734400 :
    ThetaLowerSegment 2953734400 2953865472 (295367809563377 / 100000)
      (295381026373929 / 100000) := by
  exact
    packedTile65536 2953734400 2953865472 14 6061 54348 31 _ _ (272579 / 12500) (436127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953865472 :
    ThetaLowerSegment 2953865472 2953996544 (295381026373929 / 100000)
      (295394075305737 / 100000) := by
  exact
    packedTile65536 2953865472 2953996544 14 5984 54349 31 _ _ (2180637 / 100000) (13629 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953996544 :
    ThetaLowerSegment 2953996544 2954127616 (295394075305737 / 100000)
      (295407259461223 / 100000) := by
  exact
    packedTile65536 2953996544 2954127616 14 6046 54350 31 _ _ (2180641 / 100000) (545161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954127616 :
    ThetaLowerSegment 2954127616 2954258688 (295407259461223 / 100000) (18463767778363 / 6250) := by
  exact
    packedTile65536 2954127616 2954258688 14 5973 54351 31 _ _ (436129 / 20000) (272581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954258688 :
    ThetaLowerSegment 2954258688 2954389760 (18463767778363 / 6250) (73858295204477 / 25000) := by
  exact
    packedTile65536 2954258688 2954389760 14 5914 54353 31 _ _ (43613 / 2000) (2180653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954389760 :
    ThetaLowerSegment 2954389760 2954520832 (73858295204477 / 25000) (73861574908093 / 25000) := by
  exact
    packedTile65536 2954389760 2954520832 14 6016 54354 31 _ _ (1090327 / 50000) (2180657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954520832 :
    ThetaLowerSegment 2954520832 2954651904 (73861574908093 / 25000) (18466212019313 / 6250) := by
  exact
    packedTile65536 2954520832 2954651904 14 6004 54355 31 _ _ (2180659 / 100000) (1090331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954651904 :
    ThetaLowerSegment 2954651904 2954782976 (18466212019313 / 6250) (59094494821269 / 20000) := by
  exact
    packedTile65536 2954651904 2954782976 14 5999 54356 31 _ _ (2180663 / 100000) (1090333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954782976 :
    ThetaLowerSegment 2954782976 2954914048 (59094494821269 / 20000)
      (295485555933677 / 100000) := by
  exact
    packedTile65536 2954782976 2954914048 14 5999 54357 31 _ _ (545167 / 25000) (2180671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2954914048 :
    ThetaLowerSegment 2954914048 2955045120 (295485555933677 / 100000)
      (59099697027593 / 20000) := by
  exact
    packedTile65536 2954914048 2955045120 14 5929 54359 31 _ _ (68146 / 3125) (87227 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955045120 :
    ThetaLowerSegment 2955045120 2955176192 (59099697027593 / 20000)
      (295511643336949 / 100000) := by
  exact
    packedTile65536 2955045120 2955176192 14 6034 54360 31 _ _ (545169 / 25000) (2180679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955176192 :
    ThetaLowerSegment 2955176192 2955307264 (295511643336949 / 100000)
      (73881185671929 / 25000) := by
  exact
    packedTile65536 2955176192 2955307264 14 6007 54361 31 _ _ (2180681 / 100000) (545171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955307264 :
    ThetaLowerSegment 2955307264 2955438336 (73881185671929 / 25000)
      (295537724305521 / 100000) := by
  exact
    packedTile65536 2955307264 2955438336 14 5953 54362 31 _ _ (436137 / 20000) (136293 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955438336 :
    ThetaLowerSegment 2955438336 2955569408 (295537724305521 / 100000)
      (295550825891041 / 100000) := by
  exact
    packedTile65536 2955438336 2955569408 14 6008 54363 31 _ _ (218069 / 10000) (2180693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955569408 :
    ThetaLowerSegment 2955569408 2955700480 (295550825891041 / 100000) (11822553000319 / 4000) := by
  exact
    packedTile65536 2955569408 2955700480 14 5961 54365 31 _ _ (1090347 / 50000) (2180697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955700480 :
    ThetaLowerSegment 2955700480 2955831552 (11822553000319 / 4000) (73894174418543 / 25000) := by
  exact
    packedTile65536 2955700480 2955831552 14 5903 54366 31 _ _ (2180699 / 100000) (1090351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955831552 :
    ThetaLowerSegment 2955831552 2955962624 (73894174418543 / 25000) (147794993439127 / 50000) := by
  exact
    packedTile65536 2955831552 2955962624 14 6094 54367 31 _ _ (2180703 / 100000) (1090353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2955962624 :
    ThetaLowerSegment 2955962624 2956093696 (147794993439127 / 50000)
      (147801541014897 / 50000) := by
  exact
    packedTile65536 2955962624 2956093696 14 6005 54368 31 _ _ (545177 / 25000) (2180711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956093696 :
    ThetaLowerSegment 2956093696 2956224768 (147801541014897 / 50000)
      (147808122403713 / 50000) := by
  exact
    packedTile65536 2956093696 2956224768 14 6036 54369 31 _ _ (272589 / 12500) (436143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956224768 :
    ThetaLowerSegment 2956224768 2956355840 (147808122403713 / 50000)
      (147814779039303 / 50000) := by
  exact
    packedTile65536 2956224768 2956355840 14 6105 54371 31 _ _ (545179 / 25000) (2180719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956355840 :
    ThetaLowerSegment 2956355840 2956486912 (147814779039303 / 50000) (11825704736667 / 4000) := by
  exact
    packedTile65536 2956355840 2956486912 14 5989 54372 31 _ _ (2180721 / 100000) (545181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956486912 :
    ThetaLowerSegment 2956486912 2956617984 (11825704736667 / 4000) (473048956947 / 160) := by
  exact
    packedTile65536 2956486912 2956617984 14 5952 54373 31 _ _ (87229 / 4000) (272591 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956617984 :
    ThetaLowerSegment 2956617984 2956749056 (473048956947 / 160) (59133706836447 / 20000) := by
  exact
    packedTile65536 2956617984 2956749056 14 5932 54374 31 _ _ (218073 / 10000) (2180733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956749056 :
    ThetaLowerSegment 2956749056 2956880128 (59133706836447 / 20000)
      (295681592417427 / 100000) := by
  exact
    packedTile65536 2956749056 2956880128 14 5988 54375 31 _ _ (1090367 / 50000) (2180737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2956880128 :
    ThetaLowerSegment 2956880128 2957011200 (295681592417427 / 100000) (18480910624701 / 6250) := by
  exact
    packedTile65536 2956880128 2957011200 14 5951 54377 31 _ _ (2180739 / 100000) (1090371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957011200 :
    ThetaLowerSegment 2957011200 2957142272 (18480910624701 / 6250) (9240866382406 / 3125) := by
  exact
    packedTile65536 2957011200 2957142272 14 6032 54378 31 _ _ (2180743 / 100000) (1090373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957142272 :
    ThetaLowerSegment 2957142272 2957273344 (9240866382406 / 3125) (7393021526423 / 2500) := by
  exact
    packedTile65536 2957142272 2957273344 14 6024 54379 31 _ _ (2180747 / 100000) (8723 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957273344 :
    ThetaLowerSegment 2957273344 2957404416 (7393021526423 / 2500) (295734032799 / 100) := by
  exact
    packedTile65536 2957273344 2957404416 14 6040 54380 31 _ _ (136297 / 6250) (436151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957404416 :
    ThetaLowerSegment 2957404416 2957535488 (295734032799 / 100) (14787355321561 / 5000) := by
  exact
    packedTile65536 2957404416 2957535488 14 5995 54382 31 _ _ (545189 / 25000) (2180759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957535488 :
    ThetaLowerSegment 2957535488 2957666560 (14787355321561 / 5000) (295760258600811 / 100000) := by
  exact
    packedTile65536 2957535488 2957666560 14 6031 54383 31 _ _ (2180761 / 100000) (545191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957666560 :
    ThetaLowerSegment 2957666560 2957797632 (295760258600811 / 100000)
      (295773330106221 / 100000) := by
  exact
    packedTile65536 2957666560 2957797632 14 5994 54384 31 _ _ (436153 / 20000) (68149 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957797632 :
    ThetaLowerSegment 2957797632 2957928704 (295773330106221 / 100000)
      (295786331856961 / 100000) := by
  exact
    packedTile65536 2957797632 2957928704 14 5962 54385 31 _ _ (218077 / 10000) (2180773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2957928704 :
    ThetaLowerSegment 2957928704 2958059776 (295786331856961 / 100000)
      (295799409958639 / 100000) := by
  exact
    packedTile65536 2957928704 2958059776 14 5997 54386 31 _ _ (1090387 / 50000) (2180777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958059776 :
    ThetaLowerSegment 2958059776 2958190848 (295799409958639 / 100000)
      (295812664727323 / 100000) := by
  exact
    packedTile65536 2958059776 2958190848 14 6078 54388 31 _ _ (1090389 / 50000) (2180781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958190848 :
    ThetaLowerSegment 2958190848 2958321920 (295812664727323 / 100000) (18489102115239 / 6250) := by
  exact
    packedTile65536 2958190848 2958321920 14 5947 54389 31 _ _ (2180783 / 100000) (1090393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958321920 :
    ThetaLowerSegment 2958321920 2958452992 (18489102115239 / 6250) (295838842870683 / 100000) := by
  exact
    packedTile65536 2958321920 2958452992 14 6057 54390 31 _ _ (2180787 / 100000) (218079 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958452992 :
    ThetaLowerSegment 2958452992 2958584064 (295838842870683 / 100000)
      (295852003950403 / 100000) := by
  exact
    packedTile65536 2958452992 2958584064 14 6035 54391 31 _ _ (272599 / 12500) (436159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958584064 :
    ThetaLowerSegment 2958584064 2958715136 (295852003950403 / 100000)
      (59173038244763 / 20000) := by
  exact
    packedTile65536 2958584064 2958715136 14 6047 54392 31 _ _ (545199 / 25000) (2180799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958715136 :
    ThetaLowerSegment 2958715136 2958846208 (59173038244763 / 20000)
      (295878236775397 / 100000) := by
  exact
    packedTile65536 2958715136 2958846208 14 5982 54394 31 _ _ (2180801 / 100000) (545201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958846208 :
    ThetaLowerSegment 2958846208 2958977280 (295878236775397 / 100000)
      (73972880014663 / 25000) := by
  exact
    packedTile65536 2958846208 2958977280 14 6091 54395 31 _ _ (436161 / 20000) (272601 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2958977280 :
    ThetaLowerSegment 2958977280 2959108352 (73972880014663 / 25000) (36988083246913 / 12500) := by
  exact
    packedTile65536 2958977280 2959108352 14 6028 54396 31 _ _ (2180809 / 100000) (545203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959108352 :
    ThetaLowerSegment 2959108352 2959239424 (36988083246913 / 12500) (147958839446221 / 50000) := by
  exact
    packedTile65536 2959108352 2959239424 14 5967 54397 31 _ _ (1090407 / 50000) (2180817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959239424 :
    ThetaLowerSegment 2959239424 2959370496 (147958839446221 / 50000)
      (147965414612491 / 50000) := by
  exact
    packedTile65536 2959239424 2959370496 14 6030 54398 31 _ _ (1090409 / 50000) (2180821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959370496 :
    ThetaLowerSegment 2959370496 2959501568 (147965414612491 / 50000)
      (295943885812283 / 100000) := by
  exact
    packedTile65536 2959370496 2959501568 14 5987 54400 31 _ _ (2180823 / 100000) (1090413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959501568 :
    ThetaLowerSegment 2959501568 2959632640 (295943885812283 / 100000)
      (295957044922401 / 100000) := by
  exact
    packedTile65536 2959501568 2959632640 14 6034 54401 31 _ _ (2180827 / 100000) (218083 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959632640 :
    ThetaLowerSegment 2959632640 2959763712 (295957044922401 / 100000)
      (59194026855213 / 20000) := by
  exact
    packedTile65536 2959632640 2959763712 14 6002 54402 31 _ _ (68151 / 3125) (436167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959763712 :
    ThetaLowerSegment 2959763712 2959894784 (59194026855213 / 20000)
      (295983206207049 / 100000) := by
  exact
    packedTile65536 2959763712 2959894784 14 5994 54403 31 _ _ (545209 / 25000) (2180839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2959894784 :
    ThetaLowerSegment 2959894784 2960025856 (295983206207049 / 100000)
      (295996319597969 / 100000) := by
  exact
    packedTile65536 2959894784 2960025856 14 6013 54404 31 _ _ (54521 / 2500) (2180843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960025856 :
    ThetaLowerSegment 2960025856 2960156928 (295996319597969 / 100000)
      (296009326157549 / 100000) := by
  exact
    packedTile65536 2960025856 2960156928 14 5964 54406 31 _ _ (436169 / 20000) (136303 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960156928 :
    ThetaLowerSegment 2960156928 2960288000 (296009326157549 / 100000)
      (296022341464381 / 100000) := by
  exact
    packedTile65536 2960156928 2960288000 14 5968 54407 31 _ _ (2180849 / 100000) (545213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960288000 :
    ThetaLowerSegment 2960288000 2960419072 (296022341464381 / 100000)
      (296035553077913 / 100000) := by
  exact
    packedTile65536 2960288000 2960419072 14 6058 54408 31 _ _ (1090427 / 50000) (2180857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960419072 :
    ThetaLowerSegment 2960419072 2960550144 (296035553077913 / 100000)
      (296048714555943 / 100000) := by
  exact
    packedTile65536 2960419072 2960550144 14 6035 54409 31 _ _ (1090429 / 50000) (2180861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960550144 :
    ThetaLowerSegment 2960550144 2960681216 (296048714555943 / 100000)
      (74015442845681 / 25000) := by
  exact
    packedTile65536 2960550144 2960681216 14 5987 54410 31 _ _ (2180863 / 100000) (1090433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960681216 :
    ThetaLowerSegment 2960681216 2960812288 (74015442845681 / 25000) (59214981348933 / 20000) := by
  exact
    packedTile65536 2960681216 2960812288 14 6023 54412 31 _ _ (2180867 / 100000) (218087 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960812288 :
    ThetaLowerSegment 2960812288 2960943360 (59214981348933 / 20000) (148044016703607 / 50000) := by
  exact
    packedTile65536 2960812288 2960943360 14 6019 54413 31 _ _ (2180871 / 100000) (1090437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2960943360 :
    ThetaLowerSegment 2960943360 2961074432 (148044016703607 / 50000)
      (148050611672631 / 50000) := by
  exact
    packedTile65536 2960943360 2961074432 14 6048 54414 31 _ _ (545219 / 25000) (2180879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961074432 :
    ThetaLowerSegment 2961074432 2961205504 (148050611672631 / 50000)
      (148057073620071 / 50000) := by
  exact
    packedTile65536 2961074432 2961205504 14 5926 54415 31 _ _ (27261 / 1250) (2180883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961205504 :
    ThetaLowerSegment 2961205504 2961336576 (148057073620071 / 50000)
      (296127191113327 / 100000) := by
  exact
    packedTile65536 2961205504 2961336576 14 5981 54416 31 _ _ (436177 / 20000) (272611 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961336576 :
    ThetaLowerSegment 2961336576 2961467648 (296127191113327 / 100000)
      (296140350597553 / 100000) := by
  exact
    packedTile65536 2961336576 2961467648 14 6034 54418 31 _ _ (2180889 / 100000) (545223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961467648 :
    ThetaLowerSegment 2961467648 2961598720 (296140350597553 / 100000)
      (296153433780659 / 100000) := by
  exact
    packedTile65536 2961467648 2961598720 14 5999 54419 31 _ _ (1090447 / 50000) (2180897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961598720 :
    ThetaLowerSegment 2961598720 2961729792 (296153433780659 / 100000)
      (296166514806863 / 100000) := by
  exact
    packedTile65536 2961598720 2961729792 14 5998 54420 31 _ _ (1090449 / 50000) (2180901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961729792 :
    ThetaLowerSegment 2961729792 2961860864 (296166514806863 / 100000)
      (296179737615689 / 100000) := by
  exact
    packedTile65536 2961729792 2961860864 14 6063 54421 31 _ _ (1090451 / 50000) (436181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961860864 :
    ThetaLowerSegment 2961860864 2961991936 (296179737615689 / 100000)
      (296192940826667 / 100000) := by
  exact
    packedTile65536 2961860864 2961991936 14 6054 54422 31 _ _ (2180907 / 100000) (218091 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2961991936 :
    ThetaLowerSegment 2961991936 2962123008 (296192940826667 / 100000) (14810303822681 / 5000) := by
  exact
    packedTile65536 2961991936 2962123008 14 6023 54424 31 _ _ (2180911 / 100000) (1090457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962123008 :
    ThetaLowerSegment 2962123008 2962254080 (14810303822681 / 5000) (7405478230897 / 2500) := by
  exact
    packedTile65536 2962123008 2962254080 14 5985 54425 31 _ _ (545229 / 25000) (2180919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962254080 :
    ThetaLowerSegment 2962254080 2962385152 (7405478230897 / 2500) (7405807658863 / 2500) := by
  exact
    packedTile65536 2962254080 2962385152 14 6042 54426 31 _ _ (54523 / 2500) (2180923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962385152 :
    ThetaLowerSegment 2962385152 2962516224 (7405807658863 / 2500) (59249095392119 / 20000) := by
  exact
    packedTile65536 2962385152 2962516224 14 6039 54427 31 _ _ (87237 / 4000) (68154 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962516224 :
    ThetaLowerSegment 2962516224 2962647296 (59249095392119 / 20000) (74064641178881 / 25000) := by
  exact
    packedTile65536 2962516224 2962647296 14 6001 54429 31 _ _ (2180929 / 100000) (545233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962647296 :
    ThetaLowerSegment 2962647296 2962778368 (74064641178881 / 25000) (148135814252097 / 50000) := by
  exact
    packedTile65536 2962647296 2962778368 14 5990 54430 31 _ _ (2180933 / 100000) (272617 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962778368 :
    ThetaLowerSegment 2962778368 2962909440 (148135814252097 / 50000) (74071181259221 / 25000) := by
  exact
    packedTile65536 2962778368 2962909440 14 6005 54431 31 _ _ (1090469 / 50000) (2180941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2962909440 :
    ThetaLowerSegment 2962909440 2963040512 (74071181259221 / 25000) (148148841006653 / 50000) := by
  exact
    packedTile65536 2962909440 2963040512 14 5941 54432 31 _ _ (1090471 / 50000) (436189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963040512 :
    ThetaLowerSegment 2963040512 2963171584 (148148841006653 / 50000)
      (148155453637957 / 50000) := by
  exact
    packedTile65536 2963040512 2963171584 14 6064 54433 31 _ _ (2180947 / 100000) (43619 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963171584 :
    ThetaLowerSegment 2963171584 2963302656 (148155453637957 / 50000) (9260123281281 / 3125) := by
  exact
    packedTile65536 2963171584 2963302656 14 5978 54435 31 _ _ (2180951 / 100000) (1090477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963302656 :
    ThetaLowerSegment 2963302656 2963433728 (9260123281281 / 3125) (74084280039047 / 25000) := by
  exact
    packedTile65536 2963302656 2963433728 14 6041 54436 31 _ _ (545239 / 25000) (2180959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963433728 :
    ThetaLowerSegment 2963433728 2963564800 (74084280039047 / 25000) (74087578741047 / 25000) := by
  exact
    packedTile65536 2963433728 2963564800 14 6050 54437 31 _ _ (13631 / 625) (2180963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963564800 :
    ThetaLowerSegment 2963564800 2963695872 (74087578741047 / 25000) (74090858910903 / 25000) := by
  exact
    packedTile65536 2963564800 2963695872 14 6016 54438 31 _ _ (545241 / 25000) (2180967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963695872 :
    ThetaLowerSegment 2963695872 2963826944 (74090858910903 / 25000) (148188293443341 / 50000) := by
  exact
    packedTile65536 2963695872 2963826944 14 6030 54439 31 _ _ (2180969 / 100000) (545243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963826944 :
    ThetaLowerSegment 2963826944 2963958016 (148188293443341 / 50000) (74097423633603 / 25000) := by
  exact
    packedTile65536 2963826944 2963958016 14 6010 54441 31 _ _ (2180973 / 100000) (136311 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2963958016 :
    ThetaLowerSegment 2963958016 2964089088 (74097423633603 / 25000) (29640267353449 / 10000) := by
  exact
    packedTile65536 2963958016 2964089088 14 5951 54442 31 _ _ (1090489 / 50000) (2180981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964089088 :
    ThetaLowerSegment 2964089088 2964220160 (29640267353449 / 10000) (37051969110443 / 12500) := by
  exact
    packedTile65536 2964089088 2964220160 14 5997 54443 31 _ _ (1090491 / 50000) (436197 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964220160 :
    ThetaLowerSegment 2964220160 2964351232 (37051969110443 / 12500) (74107250048127 / 25000) := by
  exact
    packedTile65536 2964220160 2964351232 14 6074 54444 31 _ _ (1090493 / 50000) (2180989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964351232 :
    ThetaLowerSegment 2964351232 2964482304 (74107250048127 / 25000) (74110525896609 / 25000) := by
  exact
    packedTile65536 2964351232 2964482304 14 6008 54445 31 _ _ (2180991 / 100000) (1090497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964482304 :
    ThetaLowerSegment 2964482304 2964613376 (74110525896609 / 25000)
      (296455174289471 / 100000) := by
  exact
    packedTile65536 2964482304 2964613376 14 5993 54447 31 _ _ (436199 / 20000) (1090499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964613376 :
    ThetaLowerSegment 2964613376 2964744448 (296455174289471 / 100000)
      (296468262470471 / 100000) := by
  exact
    packedTile65536 2964613376 2964744448 14 6001 54448 31 _ _ (2181 / 100) (2181003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964744448 :
    ThetaLowerSegment 2964744448 2964875520 (296468262470471 / 100000)
      (59296267954091 / 20000) := by
  exact
    packedTile65536 2964744448 2964875520 14 5996 54449 31 _ _ (545251 / 25000) (2181007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2964875520 :
    ThetaLowerSegment 2964875520 2965006592 (59296267954091 / 20000)
      (296494438910509 / 100000) := by
  exact
    packedTile65536 2964875520 2965006592 14 6006 54450 31 _ _ (2181009 / 100000) (545253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965006592 :
    ThetaLowerSegment 2965006592 2965137664 (296494438910509 / 100000)
      (296507411575833 / 100000) := by
  exact
    packedTile65536 2965006592 2965137664 14 5948 54451 31 _ _ (2181013 / 100000) (272627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965137664 :
    ThetaLowerSegment 2965137664 2965268736 (296507411575833 / 100000)
      (37065072842187 / 12500) := by
  exact
    packedTile65536 2965137664 2965268736 14 6039 54453 31 _ _ (2181017 / 100000) (109051 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965268736 :
    ThetaLowerSegment 2965268736 2965399808 (37065072842187 / 12500) (14826690204643 / 5000) := by
  exact
    packedTile65536 2965268736 2965399808 14 6062 54454 31 _ _ (1090511 / 50000) (87241 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965399808 :
    ThetaLowerSegment 2965399808 2965530880 (14826690204643 / 5000) (148273533455983 / 50000) := by
  exact
    packedTile65536 2965399808 2965530880 14 6081 54455 31 _ _ (1090513 / 50000) (2181029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965530880 :
    ThetaLowerSegment 2965530880 2965661952 (148273533455983 / 50000) (18535002752901 / 6250) := by
  exact
    packedTile65536 2965530880 2965661952 14 5950 54456 31 _ _ (2181031 / 100000) (1090517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965661952 :
    ThetaLowerSegment 2965661952 2965793024 (18535002752901 / 6250) (148286597843733 / 50000) := by
  exact
    packedTile65536 2965661952 2965793024 14 6030 54457 31 _ _ (436207 / 20000) (1090519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965793024 :
    ThetaLowerSegment 2965793024 2965924096 (148286597843733 / 50000)
      (148293205304413 / 50000) := by
  exact
    packedTile65536 2965793024 2965924096 14 6059 54459 31 _ _ (27263 / 1250) (2181043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2965924096 :
    ThetaLowerSegment 2965924096 2966055168 (148293205304413 / 50000)
      (148299840040261 / 50000) := by
  exact
    packedTile65536 2965924096 2966055168 14 6084 54460 31 _ _ (545261 / 25000) (2181047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966055168 :
    ThetaLowerSegment 2966055168 2966186240 (148299840040261 / 50000)
      (148306374460069 / 50000) := by
  exact
    packedTile65536 2966055168 2966186240 14 5992 54461 31 _ _ (272631 / 12500) (2181051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966186240 :
    ThetaLowerSegment 2966186240 2966317312 (148306374460069 / 50000)
      (296625815608661 / 100000) := by
  exact
    packedTile65536 2966186240 2966317312 14 5991 54462 31 _ _ (2181053 / 100000) (68158 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966317312 :
    ThetaLowerSegment 2966317312 2966448384 (296625815608661 / 100000)
      (148319434617403 / 50000) := by
  exact
    packedTile65536 2966317312 2966448384 14 5985 54463 31 _ _ (2181057 / 100000) (109053 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966448384 :
    ThetaLowerSegment 2966448384 2966579456 (148319434617403 / 50000) (74163004714401 / 25000) := by
  exact
    packedTile65536 2966448384 2966579456 14 6029 54465 31 _ _ (1090531 / 50000) (436213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966579456 :
    ThetaLowerSegment 2966579456 2966710528 (74163004714401 / 25000) (74166298124061 / 25000) := by
  exact
    packedTile65536 2966579456 2966710528 14 6040 54466 31 _ _ (1090533 / 50000) (2181069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966710528 :
    ThetaLowerSegment 2966710528 2966841600 (74166298124061 / 25000) (148339223429317 / 50000) := by
  exact
    packedTile65536 2966710528 2966841600 14 6077 54467 31 _ _ (218107 / 10000) (2181073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966841600 :
    ThetaLowerSegment 2966841600 2966972672 (148339223429317 / 50000)
      (296691417711659 / 100000) := by
  exact
    packedTile65536 2966841600 2966972672 14 5947 54468 31 _ _ (87243 / 4000) (1090539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2966972672 :
    ThetaLowerSegment 2966972672 2967103744 (296691417711659 / 100000) (9272018141357 / 3125) := by
  exact
    packedTile65536 2966972672 2967103744 14 6035 54469 31 _ _ (2181079 / 100000) (1090541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967103744 :
    ThetaLowerSegment 2967103744 2967234816 (9272018141357 / 3125) (74179429298089 / 25000) := by
  exact
    packedTile65536 2967103744 2967234816 14 6023 54471 31 _ _ (545271 / 25000) (2181087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967234816 :
    ThetaLowerSegment 2967234816 2967365888 (74179429298089 / 25000) (14836539422637 / 5000) := by
  exact
    packedTile65536 2967234816 2967365888 14 5993 54472 31 _ _ (68159 / 3125) (2181091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967365888 :
    ThetaLowerSegment 2967365888 2967496960 (14836539422637 / 5000) (296743720153137 / 100000) := by
  exact
    packedTile65536 2967365888 2967496960 14 5929 54473 31 _ _ (2181093 / 100000) (272637 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967496960 :
    ThetaLowerSegment 2967496960 2967628032 (296743720153137 / 100000)
      (148378452442251 / 50000) := by
  exact
    packedTile65536 2967496960 2967628032 14 6045 54474 31 _ _ (2181097 / 100000) (21811 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967628032 :
    ThetaLowerSegment 2967628032 2967759104 (148378452442251 / 50000)
      (296769923876371 / 100000) := by
  exact
    packedTile65536 2967628032 2967759104 14 5969 54475 31 _ _ (2181101 / 100000) (136319 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967759104 :
    ThetaLowerSegment 2967759104 2967890176 (296769923876371 / 100000)
      (296783156646473 / 100000) := by
  exact
    packedTile65536 2967759104 2967890176 14 6067 54477 31 _ _ (1090553 / 50000) (2181109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2967890176 :
    ThetaLowerSegment 2967890176 2968021248 (296783156646473 / 100000)
      (296796411251943 / 100000) := by
  exact
    packedTile65536 2967890176 2968021248 14 6077 54478 31 _ _ (218111 / 10000) (2181113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968021248 :
    ThetaLowerSegment 2968021248 2968152320 (296796411251943 / 100000) (9275297560444 / 3125) := by
  exact
    packedTile65536 2968021248 2968152320 14 6011 54479 31 _ _ (436223 / 20000) (1090559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968152320 :
    ThetaLowerSegment 2968152320 2968283392 (9275297560444 / 3125) (296822623916041 / 100000) := by
  exact
    packedTile65536 2968152320 2968283392 14 6007 54480 31 _ _ (2181119 / 100000) (1090561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968283392 :
    ThetaLowerSegment 2968283392 2968414464 (296822623916041 / 100000)
      (296835492541741 / 100000) := by
  exact
    packedTile65536 2968283392 2968414464 14 5900 54481 31 _ _ (2181123 / 100000) (1090563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968414464 :
    ThetaLowerSegment 2968414464 2968545536 (296835492541741 / 100000)
      (296848707996293 / 100000) := by
  exact
    packedTile65536 2968414464 2968545536 14 6059 54483 31 _ _ (272641 / 12500) (2181131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968545536 :
    ThetaLowerSegment 2968545536 2968676608 (296848707996293 / 100000)
      (296861831867537 / 100000) := by
  exact
    packedTile65536 2968545536 2968676608 14 6017 54484 31 _ _ (545283 / 25000) (436227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968676608 :
    ThetaLowerSegment 2968676608 2968807680 (296861831867537 / 100000)
      (59374985482817 / 20000) := by
  exact
    packedTile65536 2968676608 2968807680 14 6004 54485 31 _ _ (2181137 / 100000) (109057 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968807680 :
    ThetaLowerSegment 2968807680 2968938752 (59374985482817 / 20000) (74221987751749 / 25000) := by
  exact
    packedTile65536 2968807680 2968938752 14 5971 54486 31 _ _ (2181141 / 100000) (272643 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2968938752 :
    ThetaLowerSegment 2968938752 2969069824 (74221987751749 / 25000) (37112625918369 / 12500) := by
  exact
    packedTile65536 2968938752 2969069824 14 5986 54487 31 _ _ (1090573 / 50000) (2181149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969069824 :
    ThetaLowerSegment 2969069824 2969200896 (37112625918369 / 12500) (148456976236101 / 50000) := by
  exact
    packedTile65536 2969069824 2969200896 14 5935 54489 31 _ _ (43623 / 2000) (2181153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969200896 :
    ThetaLowerSegment 2969200896 2969331968 (148456976236101 / 50000)
      (148463528422717 / 50000) := by
  exact
    packedTile65536 2969200896 2969331968 14 6008 54490 31 _ _ (1090577 / 50000) (2181157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969331968 :
    ThetaLowerSegment 2969331968 2969463040 (148463528422717 / 50000)
      (148470189682303 / 50000) := by
  exact
    packedTile65536 2969331968 2969463040 14 6108 54491 31 _ _ (2181159 / 100000) (1090581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969463040 :
    ThetaLowerSegment 2969463040 2969594112 (148470189682303 / 50000)
      (296953529596333 / 100000) := by
  exact
    packedTile65536 2969463040 2969594112 14 6029 54492 31 _ _ (2181163 / 100000) (1090583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969594112 :
    ThetaLowerSegment 2969594112 2969725184 (296953529596333 / 100000)
      (296966568618637 / 100000) := by
  exact
    packedTile65536 2969594112 2969725184 14 5978 54493 31 _ _ (136323 / 6250) (2181171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969725184 :
    ThetaLowerSegment 2969725184 2969856256 (296966568618637 / 100000)
      (296979880311353 / 100000) := by
  exact
    packedTile65536 2969725184 2969856256 14 6103 54495 31 _ _ (545293 / 25000) (87247 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969856256 :
    ThetaLowerSegment 2969856256 2969987328 (296979880311353 / 100000)
      (296992858308553 / 100000) := by
  exact
    packedTile65536 2969856256 2969987328 14 5950 54496 31 _ _ (272647 / 12500) (2181179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2969987328 :
    ThetaLowerSegment 2969987328 2970118400 (296992858308553 / 100000)
      (74251429092637 / 25000) := by
  exact
    packedTile65536 2969987328 2970118400 14 5895 54497 31 _ _ (2181181 / 100000) (68162 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970118400 :
    ThetaLowerSegment 2970118400 2970249472 (74251429092637 / 25000)
      (297018600630343 / 100000) := by
  exact
    packedTile65536 2970118400 2970249472 14 5907 54498 31 _ _ (436237 / 20000) (545297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970249472 :
    ThetaLowerSegment 2970249472 2970380544 (297018600630343 / 100000)
      (297031628878213 / 100000) := by
  exact
    packedTile65536 2970249472 2970380544 14 5973 54499 31 _ _ (218119 / 10000) (2181193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970380544 :
    ThetaLowerSegment 2970380544 2970511616 (297031628878213 / 100000)
      (297044742216541 / 100000) := by
  exact
    packedTile65536 2970380544 2970511616 14 6012 54501 31 _ _ (1090597 / 50000) (2181197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970511616 :
    ThetaLowerSegment 2970511616 2970642688 (297044742216541 / 100000)
      (297057916658501 / 100000) := by
  exact
    packedTile65536 2970511616 2970642688 14 6040 54502 31 _ _ (2181199 / 100000) (1090601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970642688 :
    ThetaLowerSegment 2970642688 2970773760 (297057916658501 / 100000)
      (37133875757213 / 12500) := by
  exact
    packedTile65536 2970642688 2970773760 14 6001 54503 31 _ _ (2181203 / 100000) (1090603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970773760 :
    ThetaLowerSegment 2970773760 2970904832 (37133875757213 / 12500)
      (297083942796421 / 100000) := by
  exact
    packedTile65536 2970773760 2970904832 14 5931 54504 31 _ _ (2181207 / 100000) (218121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2970904832 :
    ThetaLowerSegment 2970904832 2971035904 (297083942796421 / 100000)
      (297096949363577 / 100000) := by
  exact
    packedTile65536 2970904832 2971035904 14 5963 54506 31 _ _ (545303 / 25000) (436243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971035904 :
    ThetaLowerSegment 2971035904 2971166976 (297096949363577 / 100000)
      (59422015184293 / 20000) := by
  exact
    packedTile65536 2971035904 2971166976 14 6018 54507 31 _ _ (68163 / 3125) (2181219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971166976 :
    ThetaLowerSegment 2971166976 2971298048 (59422015184293 / 20000)
      (297123224321653 / 100000) := by
  exact
    packedTile65536 2971166976 2971298048 14 6028 54508 31 _ _ (2181221 / 100000) (272653 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971298048 :
    ThetaLowerSegment 2971298048 2971429120 (297123224321653 / 100000)
      (148568183101139 / 50000) := by
  exact
    packedTile65536 2971298048 2971429120 14 6025 54509 31 _ _ (87249 / 4000) (545307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971429120 :
    ThetaLowerSegment 2971429120 2971560192 (148568183101139 / 50000)
      (297149621530911 / 100000) := by
  exact
    packedTile65536 2971429120 2971560192 14 6077 54510 31 _ _ (2181229 / 100000) (136327 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971560192 :
    ThetaLowerSegment 2971560192 2971691264 (297149621530911 / 100000)
      (297162730747251 / 100000) := by
  exact
    packedTile65536 2971560192 2971691264 14 6010 54512 31 _ _ (1090617 / 50000) (2181237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971691264 :
    ThetaLowerSegment 2971691264 2971822336 (297162730747251 / 100000)
      (59435147493889 / 20000) := by
  exact
    packedTile65536 2971691264 2971822336 14 5963 54513 31 _ _ (1090619 / 50000) (2181241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971822336 :
    ThetaLowerSegment 2971822336 2971953408 (59435147493889 / 20000)
      (297188750765183 / 100000) := by
  exact
    packedTile65536 2971822336 2971953408 14 5966 54514 31 _ _ (2181243 / 100000) (1090623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2971953408 :
    ThetaLowerSegment 2971953408 2972084480 (297188750765183 / 100000)
      (148600872226781 / 50000) := by
  exact
    packedTile65536 2971953408 2972084480 14 5957 54515 31 _ _ (2181247 / 100000) (349 / 16)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972084480 :
    ThetaLowerSegment 2972084480 2972215552 (148600872226781 / 50000)
      (148607498867319 / 50000) := by
  exact
    packedTile65536 2972084480 2972215552 14 6076 54516 31 _ _ (2181251 / 100000) (1090627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972215552 :
    ThetaLowerSegment 2972215552 2972346624 (148607498867319 / 50000)
      (148614041544691 / 50000) := by
  exact
    packedTile65536 2972215552 2972346624 14 5999 54518 31 _ _ (272657 / 12500) (2181259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972346624 :
    ThetaLowerSegment 2972346624 2972477696 (148614041544691 / 50000)
      (148620562421461 / 50000) := by
  exact
    packedTile65536 2972346624 2972477696 14 5979 54519 31 _ _ (109063 / 5000) (2181263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972477696 :
    ThetaLowerSegment 2972477696 2972608768 (148620562421461 / 50000) (74313536748743 / 25000) := by
  exact
    packedTile65536 2972477696 2972608768 14 5970 54520 31 _ _ (436253 / 20000) (545317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972608768 :
    ThetaLowerSegment 2972608768 2972739840 (74313536748743 / 25000) (148633658748597 / 50000) := by
  exact
    packedTile65536 2972608768 2972739840 14 6038 54521 31 _ _ (2181269 / 100000) (272659 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972739840 :
    ThetaLowerSegment 2972739840 2972870912 (148633658748597 / 50000)
      (148640246193057 / 50000) := by
  exact
    packedTile65536 2972739840 2972870912 14 6040 54522 31 _ _ (2181273 / 100000) (545319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2972870912 :
    ThetaLowerSegment 2972870912 2973001984 (148640246193057 / 50000) (371616803292 / 125) := by
  exact
    packedTile65536 2972870912 2973001984 14 5937 54524 31 _ _ (1090639 / 50000) (2181281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973001984 :
    ThetaLowerSegment 2973001984 2973133056 (371616803292 / 125) (371633162907 / 125) := by
  exact
    packedTile65536 2973001984 2973133056 14 6000 54525 31 _ _ (1090641 / 50000) (436257 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973133056 :
    ThetaLowerSegment 2973133056 2973264128 (371633162907 / 125) (148659833017957 / 50000) := by
  exact
    packedTile65536 2973133056 2973264128 14 6022 54526 31 _ _ (2181287 / 100000) (218129 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973264128 :
    ThetaLowerSegment 2973264128 2973395200 (148659833017957 / 50000) (29733291956003 / 10000) := by
  exact
    packedTile65536 2973264128 2973395200 14 6076 54527 31 _ _ (2181291 / 100000) (1090647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973395200 :
    ThetaLowerSegment 2973395200 2973526272 (29733291956003 / 10000) (148672982945703 / 50000) := by
  exact
    packedTile65536 2973395200 2973526272 14 5981 54528 31 _ _ (136331 / 6250) (2181299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973526272 :
    ThetaLowerSegment 2973526272 2973657344 (148672982945703 / 50000)
      (148679549749353 / 50000) := by
  exact
    packedTile65536 2973526272 2973657344 14 6021 54530 31 _ _ (21813 / 1000) (2181303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973657344 :
    ThetaLowerSegment 2973657344 2973788416 (148679549749353 / 50000)
      (148686079482877 / 50000) := by
  exact
    packedTile65536 2973657344 2973788416 14 5987 54531 31 _ _ (272663 / 12500) (2181307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973788416 :
    ThetaLowerSegment 2973788416 2973919488 (148686079482877 / 50000) (59477044565071 / 20000) := by
  exact
    packedTile65536 2973788416 2973919488 14 5989 54532 31 _ _ (2181309 / 100000) (68166 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2973919488 :
    ThetaLowerSegment 2973919488 2974050560 (59477044565071 / 20000)
      (297398406681127 / 100000) := by
  exact
    packedTile65536 2973919488 2974050560 14 6044 54533 31 _ _ (2181313 / 100000) (545329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974050560 :
    ThetaLowerSegment 2974050560 2974181632 (297398406681127 / 100000)
      (59482294991453 / 20000) := by
  exact
    packedTile65536 2974050560 2974181632 14 5991 54534 31 _ _ (1090659 / 50000) (2181321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974181632 :
    ThetaLowerSegment 2974181632 2974312704 (59482294991453 / 20000) (59484897308599 / 20000) := by
  exact
    packedTile65536 2974181632 2974312704 14 5965 54536 31 _ _ (1090661 / 50000) (87253 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974312704 :
    ThetaLowerSegment 2974312704 2974443776 (59484897308599 / 20000)
      (297437515603193 / 100000) := by
  exact
    packedTile65536 2974312704 2974443776 14 5973 54537 31 _ _ (1090663 / 50000) (2181329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974443776 :
    ThetaLowerSegment 2974443776 2974574848 (297437515603193 / 100000)
      (148725291978607 / 50000) := by
  exact
    packedTile65536 2974443776 2974574848 14 5991 54538 31 _ _ (2181331 / 100000) (1090667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974574848 :
    ThetaLowerSegment 2974574848 2974705920 (148725291978607 / 50000) (37182982445253 / 12500) := by
  exact
    packedTile65536 2974574848 2974705920 14 6086 54539 31 _ _ (436267 / 20000) (1090669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974705920 :
    ThetaLowerSegment 2974705920 2974836992 (37182982445253 / 12500) (9296156384902 / 3125) := by
  exact
    packedTile65536 2974705920 2974836992 14 6026 54540 31 _ _ (109067 / 5000) (2181343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974836992 :
    ThetaLowerSegment 2974836992 2974968064 (9296156384902 / 3125) (1859312586578 / 625) := by
  exact
    packedTile65536 2974836992 2974968064 14 5964 54542 31 _ _ (68167 / 3125) (2181347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2974968064 :
    ThetaLowerSegment 2974968064 2975099136 (1859312586578 / 625) (7437578093849 / 2500) := by
  exact
    packedTile65536 2974968064 2975099136 14 6010 54543 31 _ _ (545337 / 25000) (2181351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975099136 :
    ThetaLowerSegment 2975099136 2975230208 (7437578093849 / 2500) (29751632093961 / 10000) := by
  exact
    packedTile65536 2975099136 2975230208 14 6050 54544 31 _ _ (2181353 / 100000) (545339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975230208 :
    ThetaLowerSegment 2975230208 2975361280 (29751632093961 / 10000)
      (297529411262967 / 100000) := by
  exact
    packedTile65536 2975230208 2975361280 14 6001 54545 31 _ _ (2181357 / 100000) (27267 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975361280 :
    ThetaLowerSegment 2975361280 2975492352 (297529411262967 / 100000)
      (297542571419913 / 100000) := by
  exact
    packedTile65536 2975361280 2975492352 14 6033 54546 31 _ _ (1090681 / 50000) (436273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975492352 :
    ThetaLowerSegment 2975492352 2975623424 (297542571419913 / 100000)
      (59511154609389 / 20000) := by
  exact
    packedTile65536 2975492352 2975623424 14 6052 54548 31 _ _ (1090683 / 50000) (2181369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975623424 :
    ThetaLowerSegment 2975623424 2975754496 (59511154609389 / 20000) (59513770072019 / 20000) := by
  exact
    packedTile65536 2975623424 2975754496 14 5995 54549 31 _ _ (218137 / 10000) (2181373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975754496 :
    ThetaLowerSegment 2975754496 2975885568 (59513770072019 / 20000) (59516417388719 / 20000) := by
  exact
    packedTile65536 2975754496 2975885568 14 6068 54550 31 _ _ (17451 / 800) (1090689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2975885568 :
    ThetaLowerSegment 2975885568 2976016640 (59516417388719 / 20000) (148797579973971 / 50000) := by
  exact
    packedTile65536 2975885568 2976016640 14 5993 54551 31 _ _ (2181379 / 100000) (1090691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976016640 :
    ThetaLowerSegment 2976016640 2976147712 (148797579973971 / 50000)
      (148804069591371 / 50000) := by
  exact
    packedTile65536 2976016640 2976147712 14 5950 54552 31 _ _ (272673 / 12500) (2181387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976147712 :
    ThetaLowerSegment 2976147712 2976278784 (148804069591371 / 50000)
      (148810649748273 / 50000) := by
  exact
    packedTile65536 2976147712 2976278784 14 6033 54554 31 _ _ (545347 / 25000) (2181391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976278784 :
    ThetaLowerSegment 2976278784 2976409856 (148810649748273 / 50000) (29763437039741 / 10000) := by
  exact
    packedTile65536 2976278784 2976409856 14 5992 54555 31 _ _ (136337 / 6250) (436279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976409856 :
    ThetaLowerSegment 2976409856 2976540928 (29763437039741 / 10000) (23811791467 / 8) := by
  exact
    packedTile65536 2976409856 2976540928 14 5970 54556 31 _ _ (2181397 / 100000) (10907 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976540928 :
    ThetaLowerSegment 2976540928 2976672000 (23811791467 / 8) (5953211816271 / 2000) := by
  exact
    packedTile65536 2976540928 2976672000 14 6050 54557 31 _ _ (2181401 / 100000) (545351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976672000 :
    ThetaLowerSegment 2976672000 2976803072 (5953211816271 / 2000) (7441843889969 / 2500) := by
  exact
    packedTile65536 2976672000 2976803072 14 6035 54558 31 _ _ (1090703 / 50000) (2181409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976803072 :
    ThetaLowerSegment 2976803072 2976934144 (7441843889969 / 2500) (14884341112233 / 5000) := by
  exact
    packedTile65536 2976803072 2976934144 14 5990 54560 31 _ _ (218141 / 10000) (2181413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2976934144 :
    ThetaLowerSegment 2976934144 2977065216 (14884341112233 / 5000) (14884993355019 / 5000) := by
  exact
    packedTile65536 2976934144 2977065216 14 5980 54561 31 _ _ (1090707 / 50000) (2181417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977065216 :
    ThetaLowerSegment 2977065216 2977196288 (14884993355019 / 5000) (297712853087687 / 100000) := by
  exact
    packedTile65536 2977065216 2977196288 14 5953 54562 31 _ _ (2181419 / 100000) (1090711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977196288 :
    ThetaLowerSegment 2977196288 2977327360 (297712853087687 / 100000)
      (59545221482767 / 20000) := by
  exact
    packedTile65536 2977196288 2977327360 14 6076 54563 31 _ _ (2181423 / 100000) (1090713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977327360 :
    ThetaLowerSegment 2977327360 2977458432 (59545221482767 / 20000)
      (297739298508951 / 100000) := by
  exact
    packedTile65536 2977327360 2977458432 14 6047 54564 31 _ _ (545357 / 25000) (2181431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977458432 :
    ThetaLowerSegment 2977458432 2977589504 (297739298508951 / 100000)
      (297752428548159 / 100000) := by
  exact
    packedTile65536 2977458432 2977589504 14 6019 54566 31 _ _ (272679 / 12500) (436287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977589504 :
    ThetaLowerSegment 2977589504 2977720576 (297752428548159 / 100000) (11910625572983 / 4000) := by
  exact
    packedTile65536 2977589504 2977720576 14 6056 54567 31 _ _ (545359 / 25000) (2181439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977720576 :
    ThetaLowerSegment 2977720576 2977851648 (11910625572983 / 4000) (74444702170973 / 25000) := by
  exact
    packedTile65536 2977720576 2977851648 14 6037 54568 31 _ _ (2181441 / 100000) (545361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977851648 :
    ThetaLowerSegment 2977851648 2977982720 (74444702170973 / 25000) (18611984313477 / 6250) := by
  exact
    packedTile65536 2977851648 2977982720 14 5932 54569 31 _ _ (436289 / 20000) (272681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2977982720 :
    ThetaLowerSegment 2977982720 2978113792 (18611984313477 / 6250) (74451223608333 / 25000) := by
  exact
    packedTile65536 2977982720 2978113792 14 6026 54570 31 _ _ (43629 / 2000) (2181453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978113792 :
    ThetaLowerSegment 2978113792 2978244864 (74451223608333 / 25000) (74454554688591 / 25000) := by
  exact
    packedTile65536 2978113792 2978244864 14 6108 54572 31 _ _ (1090727 / 50000) (2181457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978244864 :
    ThetaLowerSegment 2978244864 2978375936 (74454554688591 / 25000) (37228904166599 / 12500) := by
  exact
    packedTile65536 2978244864 2978375936 14 5966 54573 31 _ _ (1090729 / 50000) (2181461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978375936 :
    ThetaLowerSegment 2978375936 2978507008 (37228904166599 / 12500) (74461113249643 / 25000) := by
  exact
    packedTile65536 2978375936 2978507008 14 6060 54574 31 _ _ (2181463 / 100000) (1090733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978507008 :
    ThetaLowerSegment 2978507008 2978638080 (74461113249643 / 25000) (148928694548941 / 50000) := by
  exact
    packedTile65536 2978507008 2978638080 14 5930 54575 31 _ _ (2181467 / 100000) (218147 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978638080 :
    ThetaLowerSegment 2978638080 2978769152 (148928694548941 / 50000)
      (148935315316461 / 50000) := by
  exact
    packedTile65536 2978638080 2978769152 14 6070 54576 31 _ _ (68171 / 3125) (87259 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978769152 :
    ThetaLowerSegment 2978769152 2978900224 (148935315316461 / 50000)
      (148941882649959 / 50000) := by
  exact
    packedTile65536 2978769152 2978900224 14 6021 54578 31 _ _ (545369 / 25000) (2181479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2978900224 :
    ThetaLowerSegment 2978900224 2979031296 (148941882649959 / 50000)
      (297896747293349 / 100000) := by
  exact
    packedTile65536 2978900224 2979031296 14 5951 54579 31 _ _ (2181481 / 100000) (545371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979031296 :
    ThetaLowerSegment 2979031296 2979162368 (297896747293349 / 100000)
      (297909853655229 / 100000) := by
  exact
    packedTile65536 2979031296 2979162368 14 6008 54580 31 _ _ (436297 / 20000) (136343 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979162368 :
    ThetaLowerSegment 2979162368 2979293440 (297909853655229 / 100000)
      (297923134560261 / 100000) := by
  exact
    packedTile65536 2979162368 2979293440 14 6088 54581 31 _ _ (2181489 / 100000) (545373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979293440 :
    ThetaLowerSegment 2979293440 2979424512 (297923134560261 / 100000)
      (297936075182669 / 100000) := by
  exact
    packedTile65536 2979293440 2979424512 14 5932 54582 31 _ _ (1090747 / 50000) (2181497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979424512 :
    ThetaLowerSegment 2979424512 2979555584 (297936075182669 / 100000)
      (59589862066207 / 20000) := by
  exact
    packedTile65536 2979424512 2979555584 14 6067 54584 31 _ _ (1090749 / 50000) (2181501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979555584 :
    ThetaLowerSegment 2979555584 2979686656 (59589862066207 / 20000)
      (297962484421613 / 100000) := by
  exact
    packedTile65536 2979555584 2979686656 14 6039 54585 31 _ _ (1090751 / 50000) (436301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979686656 :
    ThetaLowerSegment 2979686656 2979817728 (297962484421613 / 100000)
      (148987694017759 / 50000) := by
  exact
    packedTile65536 2979686656 2979817728 14 5915 54586 31 _ _ (2181507 / 100000) (218151 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979817728 :
    ThetaLowerSegment 2979817728 2979948800 (148987694017759 / 50000)
      (297988322214237 / 100000) := by
  exact
    packedTile65536 2979817728 2979948800 14 5929 54587 31 _ _ (2181511 / 100000) (1090757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2979948800 :
    ThetaLowerSegment 2979948800 2980079872 (297988322214237 / 100000)
      (298001437488429 / 100000) := by
  exact
    packedTile65536 2979948800 2980079872 14 6012 54588 31 _ _ (545379 / 25000) (2181519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980079872 :
    ThetaLowerSegment 2980079872 2980210944 (298001437488429 / 100000)
      (298014712037629 / 100000) := by
  exact
    packedTile65536 2980079872 2980210944 14 6085 54590 31 _ _ (27269 / 1250) (2181523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980210944 :
    ThetaLowerSegment 2980210944 2980342016 (298014712037629 / 100000)
      (59605609975073 / 20000) := by
  exact
    packedTile65536 2980210944 2980342016 14 6114 54591 31 _ _ (545381 / 25000) (2181527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980342016 :
    ThetaLowerSegment 2980342016 2980473088 (59605609975073 / 20000)
      (298040995068451 / 100000) := by
  exact
    packedTile65536 2980342016 2980473088 14 5934 54592 31 _ _ (2181529 / 100000) (545383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980473088 :
    ThetaLowerSegment 2980473088 2980604160 (298040995068451 / 100000)
      (298054092992583 / 100000) := by
  exact
    packedTile65536 2980473088 2980604160 14 6004 54593 31 _ _ (2181533 / 100000) (68173 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980604160 :
    ThetaLowerSegment 2980604160 2980735232 (298054092992583 / 100000)
      (298067123319057 / 100000) := by
  exact
    packedTile65536 2980604160 2980735232 14 5973 54594 31 _ _ (1090769 / 50000) (2181541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980735232 :
    ThetaLowerSegment 2980735232 2980866304 (298067123319057 / 100000)
      (59616074801033 / 20000) := by
  exact
    packedTile65536 2980735232 2980866304 14 6074 54596 31 _ _ (1090771 / 50000) (436309 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980866304 :
    ThetaLowerSegment 2980866304 2980997376 (59616074801033 / 20000)
      (298093533090637 / 100000) := by
  exact
    packedTile65536 2980866304 2980997376 14 6032 54597 31 _ _ (1090773 / 50000) (2181549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2980997376 :
    ThetaLowerSegment 2980997376 2981128448 (298093533090637 / 100000)
      (298106635485943 / 100000) := by
  exact
    packedTile65536 2980997376 2981128448 14 6006 54598 31 _ _ (2181551 / 100000) (1090777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981128448 :
    ThetaLowerSegment 2981128448 2981259520 (298106635485943 / 100000)
      (74529930658597 / 25000) := by
  exact
    packedTile65536 2981128448 2981259520 14 5999 54599 31 _ _ (436311 / 20000) (1090779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981259520 :
    ThetaLowerSegment 2981259520 2981390592 (74529930658597 / 25000) (74533248811357 / 25000) := by
  exact
    packedTile65536 2981259520 2981390592 14 6084 54600 31 _ _ (54539 / 2500) (2181563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981390592 :
    ThetaLowerSegment 2981390592 2981521664 (74533248811357 / 25000) (74536491706243 / 25000) := by
  exact
    packedTile65536 2981390592 2981521664 14 5946 54602 31 _ _ (545391 / 25000) (2181567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981521664 :
    ThetaLowerSegment 2981521664 2981652736 (74536491706243 / 25000) (14907939831319 / 5000) := by
  exact
    packedTile65536 2981521664 2981652736 14 5881 54603 31 _ _ (68174 / 3125) (2181571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981652736 :
    ThetaLowerSegment 2981652736 2981783808 (14907939831319 / 5000) (298171862067077 / 100000) := by
  exact
    packedTile65536 2981652736 2981783808 14 5989 54604 31 _ _ (2181573 / 100000) (272697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981783808 :
    ThetaLowerSegment 2981783808 2981914880 (298171862067077 / 100000)
      (149092402681709 / 50000) := by
  exact
    packedTile65536 2981783808 2981914880 14 5933 54605 31 _ _ (2181577 / 100000) (109079 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2981914880 :
    ThetaLowerSegment 2981914880 2982045952 (149092402681709 / 50000)
      (149098988877767 / 50000) := by
  exact
    packedTile65536 2981914880 2982045952 14 6038 54606 31 _ _ (1090791 / 50000) (436317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982045952 :
    ThetaLowerSegment 2982045952 2982177024 (149098988877767 / 50000)
      (149105531454181 / 50000) := by
  exact
    packedTile65536 2982045952 2982177024 14 5998 54608 31 _ _ (1090793 / 50000) (2181589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982177024 :
    ThetaLowerSegment 2982177024 2982308096 (149105531454181 / 50000)
      (149112143853471 / 50000) := by
  exact
    packedTile65536 2982177024 2982308096 14 6062 54609 31 _ _ (218159 / 10000) (2181593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982308096 :
    ThetaLowerSegment 2982308096 2982439168 (149112143853471 / 50000)
      (298237471085527 / 100000) := by
  exact
    packedTile65536 2982308096 2982439168 14 6043 54610 31 _ _ (436319 / 20000) (1090799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982439168 :
    ThetaLowerSegment 2982439168 2982570240 (298237471085527 / 100000) (3728134380983 / 1250) := by
  exact
    packedTile65536 2982439168 2982570240 14 6087 54611 31 _ _ (2181599 / 100000) (1090801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982570240 :
    ThetaLowerSegment 2982570240 2982701312 (3728134380983 / 1250) (74566002021537 / 25000) := by
  exact
    packedTile65536 2982570240 2982701312 14 6077 54612 31 _ _ (545401 / 25000) (2181607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982701312 :
    ThetaLowerSegment 2982701312 2982832384 (74566002021537 / 25000) (14913856413833 / 5000) := by
  exact
    packedTile65536 2982701312 2982832384 14 6014 54614 31 _ _ (272701 / 12500) (2181611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982832384 :
    ThetaLowerSegment 2982832384 2982963456 (14913856413833 / 5000) (74572555577971 / 25000) := by
  exact
    packedTile65536 2982832384 2982963456 14 6002 54615 31 _ _ (545403 / 25000) (436323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2982963456 :
    ThetaLowerSegment 2982963456 2983094528 (74572555577971 / 25000) (149151614556219 / 50000) := by
  exact
    packedTile65536 2982963456 2983094528 14 5962 54616 31 _ _ (2181617 / 100000) (109081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983094528 :
    ThetaLowerSegment 2983094528 2983225600 (149151614556219 / 50000) (59663258095473 / 20000) := by
  exact
    packedTile65536 2983094528 2983225600 14 5987 54617 31 _ _ (2181621 / 100000) (272703 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983225600 :
    ThetaLowerSegment 2983225600 2983356672 (59663258095473 / 20000) (59665908771063 / 20000) := by
  exact
    packedTile65536 2983225600 2983356672 14 6075 54618 31 _ _ (1090813 / 50000) (2181629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983356672 :
    ThetaLowerSegment 2983356672 2983487744 (59665908771063 / 20000) (59668517564217 / 20000) := by
  exact
    packedTile65536 2983356672 2983487744 14 5979 54620 31 _ _ (218163 / 10000) (2181633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983487744 :
    ThetaLowerSegment 2983487744 2983618816 (59668517564217 / 20000)
      (298355507457633 / 100000) := by
  exact
    packedTile65536 2983487744 2983618816 14 5922 54621 31 _ _ (1090817 / 50000) (2181637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983618816 :
    ThetaLowerSegment 2983618816 2983749888 (298355507457633 / 100000)
      (298368688920471 / 100000) := by
  exact
    packedTile65536 2983618816 2983749888 14 6042 54622 31 _ _ (2181639 / 100000) (1090821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983749888 :
    ThetaLowerSegment 2983749888 2983880960 (298368688920471 / 100000)
      (149190951566061 / 50000) := by
  exact
    packedTile65536 2983749888 2983880960 14 6057 54623 31 _ _ (2181643 / 100000) (1090823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2983880960 :
    ThetaLowerSegment 2983880960 2984012032 (149190951566061 / 50000)
      (149197522689837 / 50000) := by
  exact
    packedTile65536 2983880960 2984012032 14 6024 54624 31 _ _ (136353 / 6250) (2181651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984012032 :
    ThetaLowerSegment 2984012032 2984143104 (149197522689837 / 50000)
      (149204082917401 / 50000) := by
  exact
    packedTile65536 2984012032 2984143104 14 6014 54626 31 _ _ (545413 / 25000) (436331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984143104 :
    ThetaLowerSegment 2984143104 2984274176 (149204082917401 / 50000)
      (149210656246929 / 50000) := by
  exact
    packedTile65536 2984143104 2984274176 14 6026 54627 31 _ _ (272707 / 12500) (2181659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984274176 :
    ThetaLowerSegment 2984274176 2984405248 (149210656246929 / 50000)
      (298434334828367 / 100000) := by
  exact
    packedTile65536 2984274176 2984405248 14 5969 54628 31 _ _ (2181661 / 100000) (68177 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984405248 :
    ThetaLowerSegment 2984405248 2984536320 (298434334828367 / 100000)
      (298447215378527 / 100000) := by
  exact
    packedTile65536 2984405248 2984536320 14 5904 54629 31 _ _ (436333 / 20000) (545417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984536320 :
    ThetaLowerSegment 2984536320 2984667392 (298447215378527 / 100000)
      (298460327215227 / 100000) := by
  exact
    packedTile65536 2984536320 2984667392 14 6010 54630 31 _ _ (218167 / 10000) (2181673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984667392 :
    ThetaLowerSegment 2984667392 2984798464 (298460327215227 / 100000)
      (298473321265571 / 100000) := by
  exact
    packedTile65536 2984667392 2984798464 14 5956 54632 31 _ _ (1090837 / 50000) (2181677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984798464 :
    ThetaLowerSegment 2984798464 2984929536 (298473321265571 / 100000)
      (298486546597607 / 100000) := by
  exact
    packedTile65536 2984798464 2984929536 14 6062 54633 31 _ _ (1090839 / 50000) (2181681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2984929536 :
    ThetaLowerSegment 2984929536 2985060608 (298486546597607 / 100000)
      (29849955160997 / 10000) := by
  exact
    packedTile65536 2984929536 2985060608 14 5961 54634 31 _ _ (2181683 / 100000) (1090843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985060608 :
    ThetaLowerSegment 2985060608 2985191680 (29849955160997 / 10000)
      (298512617733413 / 100000) := by
  exact
    packedTile65536 2985060608 2985191680 14 5989 54635 31 _ _ (2181687 / 100000) (218169 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985191680 :
    ThetaLowerSegment 2985191680 2985322752 (298512617733413 / 100000) (11941031107741 / 4000) := by
  exact
    packedTile65536 2985191680 2985322752 14 6032 54636 31 _ _ (2181691 / 100000) (1090847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985322752 :
    ThetaLowerSegment 2985322752 2985339136 (11941031107741 / 4000) (298527379058389 / 100000) := by
  exact
    packedTile65536 2985322752 2985339136 11 734 54638 31 _ _ (68178 / 3125) (2181699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2985339136 :
    ThetaLowerSegment 2985339136 2985341184 (298527379058389 / 100000)
      (298527603773077 / 100000) := by
  exact
    packedTile65536 2985339136 2985341184 8 103 54638 31 _ _ (68178 / 3125) (2181699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2953341184_2985341184 :
    ThetaLowerSegment 2953341184 2985341184 (295328588872647 / 100000)
      (298527603773077 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2953341184 cell2953472256)
                  (ThetaLowerSegment.join cell2953603328 cell2953734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2953865472 cell2953996544)
                  (ThetaLowerSegment.join cell2954127616 cell2954258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2954389760 cell2954520832)
                  (ThetaLowerSegment.join cell2954651904 cell2954782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2954914048 cell2955045120)
                  (ThetaLowerSegment.join cell2955176192 cell2955307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2955438336 cell2955569408)
                  (ThetaLowerSegment.join cell2955700480 cell2955831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2955962624 cell2956093696)
                  (ThetaLowerSegment.join cell2956224768 cell2956355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2956486912 cell2956617984)
                  (ThetaLowerSegment.join cell2956749056 cell2956880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2957011200 cell2957142272)
                  (ThetaLowerSegment.join cell2957273344 cell2957404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2957535488 cell2957666560)
                  (ThetaLowerSegment.join cell2957797632 cell2957928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2958059776 cell2958190848)
                  (ThetaLowerSegment.join cell2958321920 cell2958452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2958584064 cell2958715136)
                  (ThetaLowerSegment.join cell2958846208 cell2958977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2959108352 cell2959239424)
                  (ThetaLowerSegment.join cell2959370496 cell2959501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2959632640 cell2959763712)
                  (ThetaLowerSegment.join cell2959894784 cell2960025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2960156928 cell2960288000)
                  (ThetaLowerSegment.join cell2960419072 cell2960550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2960681216 cell2960812288)
                  (ThetaLowerSegment.join cell2960943360 cell2961074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2961205504 cell2961336576)
                  (ThetaLowerSegment.join cell2961467648 cell2961598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2961729792 cell2961860864)
                  (ThetaLowerSegment.join cell2961991936 cell2962123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2962254080 cell2962385152)
                  (ThetaLowerSegment.join cell2962516224 cell2962647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2962778368 cell2962909440)
                  (ThetaLowerSegment.join cell2963040512 cell2963171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2963302656 cell2963433728)
                  (ThetaLowerSegment.join cell2963564800 cell2963695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2963826944 cell2963958016)
                  (ThetaLowerSegment.join cell2964089088 cell2964220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2964351232 cell2964482304)
                  (ThetaLowerSegment.join cell2964613376 cell2964744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2964875520 cell2965006592)
                  (ThetaLowerSegment.join cell2965137664 cell2965268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2965399808 cell2965530880)
                  (ThetaLowerSegment.join cell2965661952 cell2965793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2965924096 cell2966055168)
                  (ThetaLowerSegment.join cell2966186240 cell2966317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2966448384 cell2966579456)
                  (ThetaLowerSegment.join cell2966710528 cell2966841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2966972672 cell2967103744)
                  (ThetaLowerSegment.join cell2967234816 cell2967365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2967496960 cell2967628032)
                  (ThetaLowerSegment.join cell2967759104 cell2967890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2968021248 cell2968152320)
                  (ThetaLowerSegment.join cell2968283392 cell2968414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2968545536 cell2968676608)
                  (ThetaLowerSegment.join cell2968807680 cell2968938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2969069824 cell2969200896)
                  (ThetaLowerSegment.join cell2969331968 cell2969463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2969594112 cell2969725184)
                  (ThetaLowerSegment.join cell2969856256 cell2969987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2970118400 cell2970249472)
                  (ThetaLowerSegment.join cell2970380544 cell2970511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2970642688 cell2970773760)
                  (ThetaLowerSegment.join cell2970904832 cell2971035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2971166976 cell2971298048)
                  (ThetaLowerSegment.join cell2971429120 cell2971560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2971691264 cell2971822336)
                  (ThetaLowerSegment.join cell2971953408 cell2972084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2972215552 cell2972346624)
                  (ThetaLowerSegment.join cell2972477696 cell2972608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2972739840 cell2972870912)
                  (ThetaLowerSegment.join cell2973001984 cell2973133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2973264128 cell2973395200)
                  (ThetaLowerSegment.join cell2973526272 cell2973657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2973788416 cell2973919488)
                  (ThetaLowerSegment.join cell2974050560 cell2974181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2974312704 cell2974443776)
                  (ThetaLowerSegment.join cell2974574848 cell2974705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2974836992 cell2974968064)
                  (ThetaLowerSegment.join cell2975099136 cell2975230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2975361280 cell2975492352)
                  (ThetaLowerSegment.join cell2975623424 cell2975754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2975885568 cell2976016640)
                  (ThetaLowerSegment.join cell2976147712 cell2976278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2976409856 cell2976540928)
                  (ThetaLowerSegment.join cell2976672000 cell2976803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2976934144 cell2977065216)
                  (ThetaLowerSegment.join cell2977196288 cell2977327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2977458432 cell2977589504)
                  (ThetaLowerSegment.join cell2977720576 cell2977851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2977982720 cell2978113792)
                  (ThetaLowerSegment.join cell2978244864 cell2978375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2978507008 cell2978638080)
                  (ThetaLowerSegment.join cell2978769152 cell2978900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2979031296 cell2979162368)
                  (ThetaLowerSegment.join cell2979293440 cell2979424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2979555584 cell2979686656)
                  (ThetaLowerSegment.join cell2979817728 cell2979948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2980079872 cell2980210944)
                  (ThetaLowerSegment.join cell2980342016 cell2980473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2980604160 cell2980735232)
                  (ThetaLowerSegment.join cell2980866304 cell2980997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2981128448 cell2981259520)
                  (ThetaLowerSegment.join cell2981390592 cell2981521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2981652736 cell2981783808)
                  (ThetaLowerSegment.join cell2981914880 cell2982045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2982177024 cell2982308096)
                  (ThetaLowerSegment.join cell2982439168 cell2982570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2982701312 cell2982832384)
                  (ThetaLowerSegment.join cell2982963456 cell2983094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2983225600 cell2983356672)
                  (ThetaLowerSegment.join cell2983487744 cell2983618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2983749888 cell2983880960)
                  (ThetaLowerSegment.join cell2984012032 cell2984143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2984274176 cell2984405248)
                  (ThetaLowerSegment.join cell2984536320 cell2984667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2984798464 cell2984929536)
                (ThetaLowerSegment.join cell2985060608 cell2985191680))
              (ThetaLowerSegment.join cell2985322752 cell2985339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
