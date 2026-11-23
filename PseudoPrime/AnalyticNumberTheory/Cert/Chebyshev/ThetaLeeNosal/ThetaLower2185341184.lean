/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2185341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2153341184 :
    ThetaLowerSegment 2153341184 2153472256 (215328072469243 / 100000)
      (53835303442337 / 25000) := by
  exact
    packedTile65536 2153341184 2153472256 14 6115 46404 31 _ _ (2149027 / 100000) (214903 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153472256 :
    ThetaLowerSegment 2153472256 2153603328 (53835303442337 / 25000) (107677167882423 / 50000) := by
  exact
    packedTile65536 2153472256 2153603328 14 6106 46405 31 _ _ (2149033 / 100000) (537259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153603328 :
    ThetaLowerSegment 2153603328 2153734400 (107677167882423 / 50000) (4307350445363 / 2000) := by
  exact
    packedTile65536 2153603328 2153734400 14 6136 46406 31 _ _ (2149039 / 100000) (1074521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153734400 :
    ThetaLowerSegment 2153734400 2153865472 (4307350445363 / 2000) (10769026629329 / 5000) := by
  exact
    packedTile65536 2153734400 2153865472 14 6054 46408 31 _ _ (429809 / 20000) (268631 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153865472 :
    ThetaLowerSegment 2153865472 2153996544 (10769026629329 / 5000) (53848434088981 / 25000) := by
  exact
    packedTile65536 2153865472 2153996544 14 6144 46409 31 _ _ (2149051 / 100000) (1074527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2153996544 :
    ThetaLowerSegment 2153996544 2154127616 (53848434088981 / 25000) (107703402388811 / 50000) := by
  exact
    packedTile65536 2153996544 2154127616 14 6081 46411 31 _ _ (1074529 / 50000) (2149061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154127616 :
    ThetaLowerSegment 2154127616 2154258688 (107703402388811 / 50000)
      (107709992493567 / 50000) := by
  exact
    packedTile65536 2154127616 2154258688 14 6133 46412 31 _ _ (268633 / 12500) (2149067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154258688 :
    ThetaLowerSegment 2154258688 2154389760 (107709992493567 / 50000)
      (107716532113577 / 50000) := by
  exact
    packedTile65536 2154258688 2154389760 14 6086 46413 31 _ _ (214907 / 10000) (2149073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154389760 :
    ThetaLowerSegment 2154389760 2154520832 (107716532113577 / 50000) (861785089793 / 400) := by
  exact
    packedTile65536 2154389760 2154520832 14 6146 46415 31 _ _ (537269 / 25000) (2149079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154520832 :
    ThetaLowerSegment 2154520832 2154651904 (861785089793 / 400) (107729632899011 / 50000) := by
  exact
    packedTile65536 2154520832 2154651904 14 6046 46416 31 _ _ (1074541 / 50000) (429817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154651904 :
    ThetaLowerSegment 2154651904 2154782976 (107729632899011 / 50000)
      (107736212331923 / 50000) := by
  exact
    packedTile65536 2154651904 2154782976 14 6123 46418 31 _ _ (67159 / 3125) (2149091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154782976 :
    ThetaLowerSegment 2154782976 2154914048 (107736212331923 / 50000)
      (107742797155939 / 50000) := by
  exact
    packedTile65536 2154782976 2154914048 14 6128 46419 31 _ _ (1074547 / 50000) (2149097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2154914048 :
    ThetaLowerSegment 2154914048 2155045120 (107742797155939 / 50000)
      (107749379849239 / 50000) := by
  exact
    packedTile65536 2154914048 2155045120 14 6126 46421 31 _ _ (21491 / 1000) (2149103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155045120 :
    ThetaLowerSegment 2155045120 2155176192 (107749379849239 / 50000) (21551183056117 / 10000) := by
  exact
    packedTile65536 2155045120 2155176192 14 6082 46422 31 _ _ (1074553 / 50000) (2149109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155176192 :
    ThetaLowerSegment 2155176192 2155307264 (21551183056117 / 10000) (107762537769213 / 50000) := by
  exact
    packedTile65536 2155176192 2155307264 14 6163 46423 31 _ _ (268639 / 12500) (429823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155307264 :
    ThetaLowerSegment 2155307264 2155438336 (107762537769213 / 50000)
      (107769049596753 / 50000) := by
  exact
    packedTile65536 2155307264 2155438336 14 6060 46425 31 _ _ (1074559 / 50000) (2149121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155438336 :
    ThetaLowerSegment 2155438336 2155569408 (107769049596753 / 50000) (21555120025341 / 10000) := by
  exact
    packedTile65536 2155438336 2155569408 14 6096 46426 31 _ _ (537281 / 25000) (2149127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155569408 :
    ThetaLowerSegment 2155569408 2155700480 (21555120025341 / 10000) (53891078562693 / 25000) := by
  exact
    packedTile65536 2155569408 2155700480 14 6102 46428 31 _ _ (2149131 / 100000) (1074567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155700480 :
    ThetaLowerSegment 2155700480 2155831552 (53891078562693 / 25000) (43115484367467 / 20000) := by
  exact
    packedTile65536 2155700480 2155831552 14 6099 46429 31 _ _ (2149137 / 100000) (107457 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155831552 :
    ThetaLowerSegment 2155831552 2155962624 (43115484367467 / 20000) (43118110620213 / 20000) := by
  exact
    packedTile65536 2155831552 2155962624 14 6110 46430 31 _ _ (2149143 / 100000) (1074573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2155962624 :
    ThetaLowerSegment 2155962624 2156093696 (43118110620213 / 20000) (107801789546577 / 50000) := by
  exact
    packedTile65536 2155962624 2156093696 14 6061 46432 31 _ _ (2149149 / 100000) (67161 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156093696 :
    ThetaLowerSegment 2156093696 2156224768 (107801789546577 / 50000)
      (107808301486227 / 50000) := by
  exact
    packedTile65536 2156093696 2156224768 14 6060 46433 31 _ _ (429831 / 20000) (1074579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156224768 :
    ThetaLowerSegment 2156224768 2156355840 (107808301486227 / 50000)
      (215629762285257 / 100000) := by
  exact
    packedTile65536 2156224768 2156355840 14 6123 46435 31 _ _ (2149161 / 100000) (537291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156355840 :
    ThetaLowerSegment 2156355840 2156486912 (215629762285257 / 100000) (4312856541429 / 2000) := by
  exact
    packedTile65536 2156355840 2156486912 14 6079 46436 31 _ _ (2149167 / 100000) (214917 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156486912 :
    ThetaLowerSegment 2156486912 2156617984 (4312856541429 / 2000) (6739247629116 / 3125) := by
  exact
    packedTile65536 2156486912 2156617984 14 6094 46437 31 _ _ (2149173 / 100000) (268647 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156617984 :
    ThetaLowerSegment 2156617984 2156749056 (6739247629116 / 3125) (1347931624461 / 625) := by
  exact
    packedTile65536 2156617984 2156749056 14 6112 46439 31 _ _ (2149179 / 100000) (1074591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156749056 :
    ThetaLowerSegment 2156749056 2156880128 (1347931624461 / 625) (215682178539 / 100) := by
  exact
    packedTile65536 2156749056 2156880128 14 6104 46440 31 _ _ (429837 / 20000) (537297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2156880128 :
    ThetaLowerSegment 2156880128 2157011200 (215682178539 / 100) (215695080132573 / 100000) := by
  exact
    packedTile65536 2156880128 2157011200 14 6003 46442 31 _ _ (2149191 / 100000) (1074597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157011200 :
    ThetaLowerSegment 2157011200 2157142272 (215695080132573 / 100000)
      (26963503093263 / 12500) := by
  exact
    packedTile65536 2157011200 2157142272 14 6023 46443 31 _ _ (2149197 / 100000) (5373 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157142272 :
    ThetaLowerSegment 2157142272 2157273344 (26963503093263 / 12500) (10786060935473 / 5000) := by
  exact
    packedTile65536 2157142272 2157273344 14 6139 46445 31 _ _ (537301 / 25000) (2149207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157273344 :
    ThetaLowerSegment 2157273344 2157404416 (10786060935473 / 5000) (21573453306541 / 10000) := by
  exact
    packedTile65536 2157273344 2157404416 14 6195 46446 31 _ _ (214921 / 10000) (2149213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157404416 :
    ThetaLowerSegment 2157404416 2157535488 (21573453306541 / 10000) (107873852805137 / 50000) := by
  exact
    packedTile65536 2157404416 2157535488 14 6129 46447 31 _ _ (67163 / 3125) (2149219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157535488 :
    ThetaLowerSegment 2157535488 2157666560 (107873852805137 / 50000)
      (107880377843129 / 50000) := by
  exact
    packedTile65536 2157535488 2157666560 14 6072 46449 31 _ _ (1074611 / 50000) (85969 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157666560 :
    ThetaLowerSegment 2157666560 2157797632 (107880377843129 / 50000) (21577387457397 / 10000) := by
  exact
    packedTile65536 2157666560 2157797632 14 6104 46450 31 _ _ (537307 / 25000) (2149231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157797632 :
    ThetaLowerSegment 2157797632 2157928704 (21577387457397 / 10000) (107893425824431 / 50000) := by
  exact
    packedTile65536 2157797632 2157928704 14 6038 46452 31 _ _ (1074617 / 50000) (2149237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2157928704 :
    ThetaLowerSegment 2157928704 2158059776 (107893425824431 / 50000)
      (107899976707951 / 50000) := by
  exact
    packedTile65536 2157928704 2158059776 14 6096 46453 31 _ _ (53731 / 2500) (2149243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158059776 :
    ThetaLowerSegment 2158059776 2158190848 (107899976707951 / 50000) (53953257894453 / 25000) := by
  exact
    packedTile65536 2158059776 2158190848 14 6085 46454 31 _ _ (1074623 / 50000) (2149249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158190848 :
    ThetaLowerSegment 2158190848 2158321920 (53953257894453 / 25000) (53956527981371 / 25000) := by
  exact
    packedTile65536 2158190848 2158321920 14 6086 46456 31 _ _ (537313 / 25000) (429851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158321920 :
    ThetaLowerSegment 2158321920 2158452992 (53956527981371 / 25000) (21583915147377 / 10000) := by
  exact
    packedTile65536 2158321920 2158452992 14 6067 46457 31 _ _ (1074629 / 50000) (2149261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158452992 :
    ThetaLowerSegment 2158452992 2158584064 (21583915147377 / 10000) (4317042875493 / 2000) := by
  exact
    packedTile65536 2158452992 2158584064 14 6045 46459 31 _ _ (134329 / 6250) (2149267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158584064 :
    ThetaLowerSegment 2158584064 2158715136 (4317042875493 / 2000) (4317305946141 / 2000) := by
  exact
    packedTile65536 2158584064 2158715136 14 6120 46460 31 _ _ (214927 / 10000) (2149273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158715136 :
    ThetaLowerSegment 2158715136 2158846208 (4317305946141 / 2000) (107939229736637 / 50000) := by
  exact
    packedTile65536 2158715136 2158846208 14 6124 46461 31 _ _ (537319 / 25000) (2149279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158846208 :
    ThetaLowerSegment 2158846208 2158977280 (107939229736637 / 50000) (21589152280927 / 10000) := by
  exact
    packedTile65536 2158846208 2158977280 14 6078 46463 31 _ _ (1074641 / 50000) (429857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2158977280 :
    ThetaLowerSegment 2158977280 2159108352 (21589152280927 / 10000) (107952183480167 / 50000) := by
  exact
    packedTile65536 2158977280 2159108352 14 5976 46464 31 _ _ (2149289 / 100000) (537323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159108352 :
    ThetaLowerSegment 2159108352 2159239424 (107952183480167 / 50000) (26989676647623 / 12500) := by
  exact
    packedTile65536 2159108352 2159239424 14 6070 46466 31 _ _ (429859 / 20000) (1074649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159239424 :
    ThetaLowerSegment 2159239424 2159370496 (26989676647623 / 12500) (6747834514324 / 3125) := by
  exact
    packedTile65536 2159239424 2159370496 14 6184 46467 31 _ _ (2149301 / 100000) (268663 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159370496 :
    ThetaLowerSegment 2159370496 2159501568 (6747834514324 / 3125) (215943765797007 / 100000) := by
  exact
    packedTile65536 2159370496 2159501568 14 6077 46469 31 _ _ (2149307 / 100000) (214931 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159501568 :
    ThetaLowerSegment 2159501568 2159632640 (215943765797007 / 100000)
      (53989245480661 / 25000) := by
  exact
    packedTile65536 2159501568 2159632640 14 6149 46470 31 _ _ (2149313 / 100000) (537329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159632640 :
    ThetaLowerSegment 2159632640 2159763712 (53989245480661 / 25000) (8638807923407 / 4000) := by
  exact
    packedTile65536 2159632640 2159763712 14 6149 46471 31 _ _ (2149319 / 100000) (1074661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159763712 :
    ThetaLowerSegment 2159763712 2159894784 (8638807923407 / 4000) (2159833197143 / 1000) := by
  exact
    packedTile65536 2159763712 2159894784 14 6105 46473 31 _ _ (85973 / 4000) (134333 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2159894784 :
    ThetaLowerSegment 2159894784 2160025856 (2159833197143 / 1000) (43199331262631 / 20000) := by
  exact
    packedTile65536 2159894784 2160025856 14 6205 46474 31 _ _ (2149331 / 100000) (1074667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160025856 :
    ThetaLowerSegment 2160025856 2160156928 (43199331262631 / 20000)
      (216009866138357 / 100000) := by
  exact
    packedTile65536 2160025856 2160156928 14 6146 46476 31 _ _ (2149337 / 100000) (107467 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160156928 :
    ThetaLowerSegment 2160156928 2160288000 (216009866138357 / 100000)
      (216023041610947 / 100000) := by
  exact
    packedTile65536 2160156928 2160288000 14 6130 46477 31 _ _ (2149343 / 100000) (1074673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160288000 :
    ThetaLowerSegment 2160288000 2160419072 (216023041610947 / 100000)
      (216036105354169 / 100000) := by
  exact
    packedTile65536 2160288000 2160419072 14 6078 46478 31 _ _ (2149349 / 100000) (268669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160419072 :
    ThetaLowerSegment 2160419072 2160550144 (216036105354169 / 100000)
      (216049328186129 / 100000) := by
  exact
    packedTile65536 2160419072 2160550144 14 6152 46480 31 _ _ (429871 / 20000) (1074679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160550144 :
    ThetaLowerSegment 2160550144 2160681216 (216049328186129 / 100000) (2160622479951 / 1000) := by
  exact
    packedTile65536 2160550144 2160681216 14 6011 46481 31 _ _ (2149361 / 100000) (537341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160681216 :
    ThetaLowerSegment 2160681216 2160812288 (2160622479951 / 1000) (13504713169913 / 6250) := by
  exact
    packedTile65536 2160681216 2160812288 14 6124 46483 31 _ _ (2149367 / 100000) (214937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160812288 :
    ThetaLowerSegment 2160812288 2160943360 (13504713169913 / 6250) (43217707819 / 20) := by
  exact
    packedTile65536 2160812288 2160943360 14 6108 46484 31 _ _ (1074687 / 50000) (2149377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2160943360 :
    ThetaLowerSegment 2160943360 2161074432 (43217707819 / 20) (2701271112523 / 1250) := by
  exact
    packedTile65536 2160943360 2161074432 14 6118 46485 31 _ _ (107469 / 5000) (2149383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161074432 :
    ThetaLowerSegment 2161074432 2161205504 (2701271112523 / 1250) (13507180926839 / 6250) := by
  exact
    packedTile65536 2161074432 2161205504 14 6144 46487 31 _ _ (1074693 / 50000) (2149389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161205504 :
    ThetaLowerSegment 2161205504 2161336576 (13507180926839 / 6250) (270160015711 / 125) := by
  exact
    packedTile65536 2161205504 2161336576 14 6103 46488 31 _ _ (134337 / 6250) (429879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161336576 :
    ThetaLowerSegment 2161336576 2161467648 (270160015711 / 125) (27017649084667 / 12500) := by
  exact
    packedTile65536 2161336576 2161467648 14 6132 46490 31 _ _ (1074699 / 50000) (2149401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161467648 :
    ThetaLowerSegment 2161467648 2161598720 (27017649084667 / 12500) (54038578697189 / 25000) := by
  exact
    packedTile65536 2161467648 2161598720 14 6105 46491 31 _ _ (537351 / 25000) (2149407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161598720 :
    ThetaLowerSegment 2161598720 2161729792 (54038578697189 / 25000) (108083623894363 / 50000) := by
  exact
    packedTile65536 2161598720 2161729792 14 6017 46492 31 _ _ (214941 / 10000) (2149413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161729792 :
    ThetaLowerSegment 2161729792 2161860864 (108083623894363 / 50000)
      (108090145222507 / 50000) := by
  exact
    packedTile65536 2161729792 2161860864 14 6068 46494 31 _ _ (268677 / 12500) (2149419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161860864 :
    ThetaLowerSegment 2161860864 2161991936 (108090145222507 / 50000) (27024156701137 / 12500) := by
  exact
    packedTile65536 2161860864 2161991936 14 6031 46495 31 _ _ (1074711 / 50000) (85977 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2161991936 :
    ThetaLowerSegment 2161991936 2162123008 (27024156701137 / 12500) (27025810685983 / 12500) := by
  exact
    packedTile65536 2161991936 2162123008 14 6156 46497 31 _ _ (537357 / 25000) (2149431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162123008 :
    ThetaLowerSegment 2162123008 2162254080 (27025810685983 / 12500) (108109780247443 / 50000) := by
  exact
    packedTile65536 2162123008 2162254080 14 6083 46498 31 _ _ (1074717 / 50000) (2149437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162254080 :
    ThetaLowerSegment 2162254080 2162385152 (108109780247443 / 50000)
      (108116329591123 / 50000) := by
  exact
    packedTile65536 2162254080 2162385152 14 6094 46500 31 _ _ (13434 / 625) (2149443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162385152 :
    ThetaLowerSegment 2162385152 2162516224 (108116329591123 / 50000) (10812285208501 / 5000) := by
  exact
    packedTile65536 2162385152 2162516224 14 6069 46501 31 _ _ (1074723 / 50000) (2149449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162516224 :
    ThetaLowerSegment 2162516224 2162647296 (10812285208501 / 5000) (54064738348037 / 25000) := by
  exact
    packedTile65536 2162516224 2162647296 14 6164 46502 31 _ _ (537363 / 25000) (429891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162647296 :
    ThetaLowerSegment 2162647296 2162778368 (54064738348037 / 25000) (54068011972571 / 25000) := by
  exact
    packedTile65536 2162647296 2162778368 14 6092 46504 31 _ _ (1074729 / 50000) (2149461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162778368 :
    ThetaLowerSegment 2162778368 2162909440 (54068011972571 / 25000) (10814259485659 / 5000) := by
  exact
    packedTile65536 2162778368 2162909440 14 6114 46505 31 _ _ (268683 / 12500) (2149467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2162909440 :
    ThetaLowerSegment 2162909440 2163040512 (10814259485659 / 5000) (108149221675683 / 50000) := by
  exact
    packedTile65536 2162909440 2163040512 14 6166 46507 31 _ _ (2149471 / 100000) (1074737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163040512 :
    ThetaLowerSegment 2163040512 2163171584 (108149221675683 / 50000)
      (216311381053429 / 100000) := by
  exact
    packedTile65536 2163040512 2163171584 14 6019 46508 31 _ _ (2149477 / 100000) (53737 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163171584 :
    ThetaLowerSegment 2163171584 2163302656 (216311381053429 / 100000)
      (108162215282361 / 50000) := by
  exact
    packedTile65536 2163171584 2163302656 14 6071 46509 31 _ _ (2149483 / 100000) (1074743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163302656 :
    ThetaLowerSegment 2163302656 2163433728 (108162215282361 / 50000) (27042184745369 / 12500) := by
  exact
    packedTile65536 2163302656 2163433728 14 6070 46511 31 _ _ (2149489 / 100000) (537373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163433728 :
    ThetaLowerSegment 2163433728 2163564800 (27042184745369 / 12500)
      (216350566238007 / 100000) := by
  exact
    packedTile65536 2163433728 2163564800 14 6089 46512 31 _ _ (429899 / 20000) (1074749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163564800 :
    ThetaLowerSegment 2163564800 2163695872 (216350566238007 / 100000)
      (216363884546203 / 100000) := by
  exact
    packedTile65536 2163564800 2163695872 14 6196 46514 31 _ _ (2149501 / 100000) (67172 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163695872 :
    ThetaLowerSegment 2163695872 2163826944 (216363884546203 / 100000)
      (216377013734959 / 100000) := by
  exact
    packedTile65536 2163695872 2163826944 14 6108 46515 31 _ _ (2149507 / 100000) (214951 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163826944 :
    ThetaLowerSegment 2163826944 2163958016 (216377013734959 / 100000)
      (108194993022957 / 50000) := by
  exact
    packedTile65536 2163826944 2163958016 14 6035 46516 31 _ _ (2149513 / 100000) (537379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2163958016 :
    ThetaLowerSegment 2163958016 2164089088 (108194993022957 / 50000) (54100702519067 / 25000) := by
  exact
    packedTile65536 2163958016 2164089088 14 5966 46518 31 _ _ (2149519 / 100000) (1074761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164089088 :
    ThetaLowerSegment 2164089088 2164220160 (54100702519067 / 25000) (6763002941899 / 3125) := by
  exact
    packedTile65536 2164089088 2164220160 14 6180 46519 31 _ _ (85981 / 4000) (268691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164220160 :
    ThetaLowerSegment 2164220160 2164351232 (6763002941899 / 3125) (216429131046283 / 100000) := by
  exact
    packedTile65536 2164220160 2164351232 14 6065 46521 31 _ _ (2149531 / 100000) (1074767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164351232 :
    ThetaLowerSegment 2164351232 2164482304 (216429131046283 / 100000)
      (216442316306241 / 100000) := by
  exact
    packedTile65536 2164351232 2164482304 14 6134 46522 31 _ _ (2149537 / 100000) (107477 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164482304 :
    ThetaLowerSegment 2164482304 2164613376 (216442316306241 / 100000)
      (43291089142977 / 20000) := by
  exact
    packedTile65536 2164482304 2164613376 14 6108 46523 31 _ _ (2149543 / 100000) (1074773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164613376 :
    ThetaLowerSegment 2164613376 2164744448 (43291089142977 / 20000)
      (216468489178217 / 100000) := by
  exact
    packedTile65536 2164613376 2164744448 14 6068 46525 31 _ _ (2149549 / 100000) (134347 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164744448 :
    ThetaLowerSegment 2164744448 2164875520 (216468489178217 / 100000)
      (216481610061937 / 100000) := by
  exact
    packedTile65536 2164744448 2164875520 14 6104 46526 31 _ _ (429911 / 20000) (1074779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2164875520 :
    ThetaLowerSegment 2164875520 2165006592 (216481610061937 / 100000)
      (216494606307743 / 100000) := by
  exact
    packedTile65536 2164875520 2165006592 14 6046 46528 31 _ _ (2149561 / 100000) (537391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165006592 :
    ThetaLowerSegment 2165006592 2165137664 (216494606307743 / 100000) (10825389265151 / 5000) := by
  exact
    packedTile65536 2165006592 2165137664 14 6131 46529 31 _ _ (2149567 / 100000) (214957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165137664 :
    ThetaLowerSegment 2165137664 2165268736 (10825389265151 / 5000) (216520792369243 / 100000) := by
  exact
    packedTile65536 2165137664 2165268736 14 6051 46531 31 _ _ (2149573 / 100000) (268697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165268736 :
    ThetaLowerSegment 2165268736 2165399808 (216520792369243 / 100000)
      (216533954247583 / 100000) := by
  exact
    packedTile65536 2165268736 2165399808 14 6123 46532 31 _ _ (107479 / 5000) (2149583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165399808 :
    ThetaLowerSegment 2165399808 2165530880 (216533954247583 / 100000)
      (216547131209763 / 100000) := by
  exact
    packedTile65536 2165399808 2165530880 14 6130 46533 31 _ _ (1074793 / 50000) (2149589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165530880 :
    ThetaLowerSegment 2165530880 2165661952 (216547131209763 / 100000)
      (216560207177899 / 100000) := by
  exact
    packedTile65536 2165530880 2165661952 14 6083 46535 31 _ _ (268699 / 12500) (429919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165661952 :
    ThetaLowerSegment 2165661952 2165793024 (216560207177899 / 100000)
      (216573197198613 / 100000) := by
  exact
    packedTile65536 2165661952 2165793024 14 6043 46536 31 _ _ (1074799 / 50000) (2149601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165793024 :
    ThetaLowerSegment 2165793024 2165924096 (216573197198613 / 100000)
      (216586309783013 / 100000) := by
  exact
    packedTile65536 2165793024 2165924096 14 6100 46538 31 _ _ (537401 / 25000) (2149607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2165924096 :
    ThetaLowerSegment 2165924096 2166055168 (216586309783013 / 100000)
      (216599542782173 / 100000) := by
  exact
    packedTile65536 2165924096 2166055168 14 6156 46539 31 _ _ (214961 / 10000) (2149613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166055168 :
    ThetaLowerSegment 2166055168 2166186240 (216599542782173 / 100000)
      (216612636093229 / 100000) := by
  exact
    packedTile65536 2166055168 2166186240 14 6091 46540 31 _ _ (134351 / 6250) (2149619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166186240 :
    ThetaLowerSegment 2166186240 2166317312 (216612636093229 / 100000)
      (43325155346503 / 20000) := by
  exact
    packedTile65536 2166186240 2166317312 14 6113 46542 31 _ _ (1074811 / 50000) (17197 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166317312 :
    ThetaLowerSegment 2166317312 2166448384 (43325155346503 / 20000)
      (216638799178939 / 100000) := by
  exact
    packedTile65536 2166317312 2166448384 14 6058 46543 31 _ _ (537407 / 25000) (2149631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166448384 :
    ThetaLowerSegment 2166448384 2166579456 (216638799178939 / 100000)
      (43330409904583 / 20000) := by
  exact
    packedTile65536 2166448384 2166579456 14 6164 46545 31 _ _ (1074817 / 50000) (2149637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166579456 :
    ThetaLowerSegment 2166579456 2166710528 (43330409904583 / 20000) (8666605977163 / 4000) := by
  exact
    packedTile65536 2166579456 2166710528 14 6094 46546 31 _ _ (53741 / 2500) (2149643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166710528 :
    ThetaLowerSegment 2166710528 2166841600 (8666605977163 / 4000) (216678227875339 / 100000) := by
  exact
    packedTile65536 2166710528 2166841600 14 6084 46547 31 _ _ (1074823 / 50000) (2149649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166841600 :
    ThetaLowerSegment 2166841600 2166972672 (216678227875339 / 100000)
      (216691517024003 / 100000) := by
  exact
    packedTile65536 2166841600 2166972672 14 6182 46549 31 _ _ (537413 / 25000) (429931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2166972672 :
    ThetaLowerSegment 2166972672 2167103744 (216691517024003 / 100000)
      (216704475162427 / 100000) := by
  exact
    packedTile65536 2166972672 2167103744 14 6028 46550 31 _ _ (1074829 / 50000) (2149661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167103744 :
    ThetaLowerSegment 2167103744 2167234816 (216704475162427 / 100000)
      (216717534371227 / 100000) := by
  exact
    packedTile65536 2167103744 2167234816 14 6075 46552 31 _ _ (67177 / 3125) (2149667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167234816 :
    ThetaLowerSegment 2167234816 2167365888 (216717534371227 / 100000)
      (216730666705257 / 100000) := by
  exact
    packedTile65536 2167234816 2167365888 14 6109 46553 31 _ _ (214967 / 10000) (2149673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167365888 :
    ThetaLowerSegment 2167365888 2167496960 (216730666705257 / 100000)
      (216743730286309 / 100000) := by
  exact
    packedTile65536 2167365888 2167496960 14 6077 46554 31 _ _ (537419 / 25000) (2149679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167496960 :
    ThetaLowerSegment 2167496960 2167628032 (216743730286309 / 100000)
      (43351380707521 / 20000) := by
  exact
    packedTile65536 2167496960 2167628032 14 6128 46556 31 _ _ (1074841 / 50000) (429937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167628032 :
    ThetaLowerSegment 2167628032 2167759104 (43351380707521 / 20000)
      (216769990838149 / 100000) := by
  exact
    packedTile65536 2167628032 2167759104 14 6088 46557 31 _ _ (268711 / 12500) (2149691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167759104 :
    ThetaLowerSegment 2167759104 2167890176 (216769990838149 / 100000)
      (216782998636543 / 100000) := by
  exact
    packedTile65536 2167759104 2167890176 14 6051 46559 31 _ _ (1074847 / 50000) (2149697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2167890176 :
    ThetaLowerSegment 2167890176 2168021248 (216782998636543 / 100000)
      (108398080627883 / 50000) := by
  exact
    packedTile65536 2167890176 2168021248 14 6123 46560 31 _ _ (2149701 / 100000) (268713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168021248 :
    ThetaLowerSegment 2168021248 2168152320 (108398080627883 / 50000)
      (216809190629893 / 100000) := by
  exact
    packedTile65536 2168021248 2168152320 14 6061 46562 31 _ _ (2149707 / 100000) (214971 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168152320 :
    ThetaLowerSegment 2168152320 2168283392 (216809190629893 / 100000)
      (108411165912731 / 50000) := by
  exact
    packedTile65536 2168152320 2168283392 14 6113 46563 31 _ _ (2149713 / 100000) (537429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168283392 :
    ThetaLowerSegment 2168283392 2168414464 (108411165912731 / 50000) (54208843005229 / 25000) := by
  exact
    packedTile65536 2168283392 2168414464 14 6066 46564 31 _ _ (2149719 / 100000) (1074861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168414464 :
    ThetaLowerSegment 2168414464 2168545536 (54208843005229 / 25000) (108424305013733 / 50000) := by
  exact
    packedTile65536 2168414464 2168545536 14 6158 46566 31 _ _ (85989 / 4000) (67179 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168545536 :
    ThetaLowerSegment 2168545536 2168676608 (108424305013733 / 50000) (27107717035619 / 12500) := by
  exact
    packedTile65536 2168545536 2168676608 14 6106 46567 31 _ _ (2149731 / 100000) (1074867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168676608 :
    ThetaLowerSegment 2168676608 2168807680 (27107717035619 / 12500) (108437328102161 / 50000) := by
  exact
    packedTile65536 2168676608 2168807680 14 6010 46569 31 _ _ (2149737 / 100000) (107487 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168807680 :
    ThetaLowerSegment 2168807680 2168938752 (108437328102161 / 50000) (54221969280943 / 25000) := by
  exact
    packedTile65536 2168807680 2168938752 14 6150 46570 31 _ _ (2149743 / 100000) (1074873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2168938752 :
    ThetaLowerSegment 2168938752 2169069824 (54221969280943 / 25000)
      (216900889554469 / 100000) := by
  exact
    packedTile65536 2168938752 2169069824 14 6053 46571 31 _ _ (2149749 / 100000) (268719 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169069824 :
    ThetaLowerSegment 2169069824 2169200896 (216900889554469 / 100000)
      (216914054654089 / 100000) := by
  exact
    packedTile65536 2169069824 2169200896 14 6124 46573 31 _ _ (429951 / 20000) (1074879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169200896 :
    ThetaLowerSegment 2169200896 2169331968 (216914054654089 / 100000)
      (216927150998101 / 100000) := by
  exact
    packedTile65536 2169200896 2169331968 14 6092 46574 31 _ _ (2149761 / 100000) (537441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169331968 :
    ThetaLowerSegment 2169331968 2169463040 (216927150998101 / 100000)
      (216940187185189 / 100000) := by
  exact
    packedTile65536 2169331968 2169463040 14 6064 46576 31 _ _ (2149767 / 100000) (214977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169463040 :
    ThetaLowerSegment 2169463040 2169594112 (216940187185189 / 100000)
      (216953227708207 / 100000) := by
  exact
    packedTile65536 2169463040 2169594112 14 6066 46577 31 _ _ (2149773 / 100000) (134361 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169594112 :
    ThetaLowerSegment 2169594112 2169725184 (216953227708207 / 100000) (1356040802443 / 625) := by
  exact
    packedTile65536 2169594112 2169725184 14 6187 46578 31 _ _ (2149779 / 100000) (1074891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169725184 :
    ThetaLowerSegment 2169725184 2169856256 (1356040802443 / 625) (21697954318927 / 10000) := by
  exact
    packedTile65536 2169725184 2169856256 14 6054 46580 31 _ _ (429957 / 20000) (537447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169856256 :
    ThetaLowerSegment 2169856256 2169987328 (21697954318927 / 10000) (54248154554533 / 25000) := by
  exact
    packedTile65536 2169856256 2169987328 14 6082 46581 31 _ _ (2149791 / 100000) (1074897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2169987328 :
    ThetaLowerSegment 2169987328 2170118400 (54248154554533 / 25000) (108502842342149 / 50000) := by
  exact
    packedTile65536 2169987328 2170118400 14 6078 46583 31 _ _ (2149797 / 100000) (10749 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170118400 :
    ThetaLowerSegment 2170118400 2170249472 (108502842342149 / 50000)
      (217018830729643 / 100000) := by
  exact
    packedTile65536 2170118400 2170249472 14 6115 46584 31 _ _ (2149803 / 100000) (1074903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170249472 :
    ThetaLowerSegment 2170249472 2170380544 (217018830729643 / 100000)
      (27129021286811 / 12500) := by
  exact
    packedTile65536 2170249472 2170380544 14 6205 46585 31 _ _ (2149809 / 100000) (537453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170380544 :
    ThetaLowerSegment 2170380544 2170511616 (27129021286811 / 12500)
      (217045243319503 / 100000) := by
  exact
    packedTile65536 2170380544 2170511616 14 6081 46587 31 _ _ (429963 / 20000) (1074909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170511616 :
    ThetaLowerSegment 2170511616 2170642688 (217045243319503 / 100000)
      (108529194737459 / 50000) := by
  exact
    packedTile65536 2170511616 2170642688 14 6115 46588 31 _ _ (2149821 / 100000) (67182 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170642688 :
    ThetaLowerSegment 2170642688 2170773760 (108529194737459 / 50000)
      (108535773208079 / 50000) := by
  exact
    packedTile65536 2170642688 2170773760 14 6120 46590 31 _ _ (2149827 / 100000) (214983 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170773760 :
    ThetaLowerSegment 2170773760 2170904832 (108535773208079 / 50000) (43416983245517 / 20000) := by
  exact
    packedTile65536 2170773760 2170904832 14 6219 46591 31 _ _ (2149833 / 100000) (537459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2170904832 :
    ThetaLowerSegment 2170904832 2171035904 (43416983245517 / 20000) (2170979979979 / 1000) := by
  exact
    packedTile65536 2170904832 2171035904 14 6085 46592 31 _ _ (2149839 / 100000) (1074921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171035904 :
    ThetaLowerSegment 2171035904 2171166976 (2170979979979 / 1000) (108555578602633 / 50000) := by
  exact
    packedTile65536 2171035904 2171166976 14 6121 46594 31 _ _ (1074923 / 50000) (2149849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171166976 :
    ThetaLowerSegment 2171166976 2171298048 (108555578602633 / 50000) (21712408211549 / 10000) := by
  exact
    packedTile65536 2171166976 2171298048 14 6012 46595 31 _ _ (537463 / 25000) (429971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171298048 :
    ThetaLowerSegment 2171298048 2171429120 (21712408211549 / 10000) (5428426412713 / 2500) := by
  exact
    packedTile65536 2171298048 2171429120 14 6035 46597 31 _ _ (1074929 / 50000) (2149861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171429120 :
    ThetaLowerSegment 2171429120 2171560192 (5428426412713 / 2500) (27143783159117 / 12500) := by
  exact
    packedTile65536 2171429120 2171560192 14 6144 46598 31 _ _ (268733 / 12500) (2149867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171560192 :
    ThetaLowerSegment 2171560192 2171691264 (27143783159117 / 12500) (108581727362693 / 50000) := by
  exact
    packedTile65536 2171560192 2171691264 14 6135 46600 31 _ _ (214987 / 10000) (2149873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171691264 :
    ThetaLowerSegment 2171691264 2171822336 (108581727362693 / 50000)
      (108588203864143 / 50000) := by
  exact
    packedTile65536 2171691264 2171822336 14 6025 46601 31 _ _ (537469 / 25000) (2149879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171822336 :
    ThetaLowerSegment 2171822336 2171953408 (108588203864143 / 50000)
      (108594776053417 / 50000) := by
  exact
    packedTile65536 2171822336 2171953408 14 6114 46602 31 _ _ (1074941 / 50000) (429977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2171953408 :
    ThetaLowerSegment 2171953408 2172084480 (108594776053417 / 50000)
      (108601310637993 / 50000) := by
  exact
    packedTile65536 2171953408 2172084480 14 6079 46604 31 _ _ (67184 / 3125) (2149891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172084480 :
    ThetaLowerSegment 2172084480 2172215552 (108601310637993 / 50000) (54303935519767 / 25000) := by
  exact
    packedTile65536 2172084480 2172215552 14 6103 46605 31 _ _ (1074947 / 50000) (2149897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172215552 :
    ThetaLowerSegment 2172215552 2172346624 (54303935519767 / 25000) (27153580453621 / 12500) := by
  exact
    packedTile65536 2172215552 2172346624 14 6001 46607 31 _ _ (21499 / 1000) (2149903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172346624 :
    ThetaLowerSegment 2172346624 2172477696 (27153580453621 / 12500) (1086208489291 / 500) := by
  exact
    packedTile65536 2172346624 2172477696 14 6072 46608 31 _ _ (1074953 / 50000) (2149909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172477696 :
    ThetaLowerSegment 2172477696 2172608768 (1086208489291 / 500) (13578418917243 / 6250) := by
  exact
    packedTile65536 2172477696 2172608768 14 6049 46609 31 _ _ (268739 / 12500) (429983 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172608768 :
    ThetaLowerSegment 2172608768 2172739840 (13578418917243 / 6250) (108633911812721 / 50000) := by
  exact
    packedTile65536 2172608768 2172739840 14 6103 46611 31 _ _ (1074959 / 50000) (2149921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172739840 :
    ThetaLowerSegment 2172739840 2172870912 (108633911812721 / 50000)
      (108640499179857 / 50000) := by
  exact
    packedTile65536 2172739840 2172870912 14 6128 46612 31 _ _ (537481 / 25000) (2149927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2172870912 :
    ThetaLowerSegment 2172870912 2173001984 (108640499179857 / 50000)
      (108647103764817 / 50000) := by
  exact
    packedTile65536 2172870912 2173001984 14 6144 46614 31 _ _ (214993 / 10000) (2149933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173001984 :
    ThetaLowerSegment 2173001984 2173133056 (108647103764817 / 50000) (21730745328533 / 10000) := by
  exact
    packedTile65536 2173001984 2173133056 14 6161 46615 31 _ _ (134371 / 6250) (2149939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173133056 :
    ThetaLowerSegment 2173133056 2173264128 (21730745328533 / 10000) (108660247416751 / 50000) := by
  exact
    packedTile65536 2173133056 2173264128 14 6066 46616 31 _ _ (1074971 / 50000) (429989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173264128 :
    ThetaLowerSegment 2173264128 2173395200 (108660247416751 / 50000)
      (108666720910179 / 50000) := by
  exact
    packedTile65536 2173264128 2173395200 14 6022 46618 31 _ _ (537487 / 25000) (2149951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173395200 :
    ThetaLowerSegment 2173395200 2173526272 (108666720910179 / 50000) (54336653647129 / 25000) := by
  exact
    packedTile65536 2173395200 2173526272 14 6127 46619 31 _ _ (1074977 / 50000) (2149957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173526272 :
    ThetaLowerSegment 2173526272 2173657344 (54336653647129 / 25000) (54339948998319 / 25000) := by
  exact
    packedTile65536 2173526272 2173657344 14 6131 46621 31 _ _ (53749 / 2500) (2149963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173657344 :
    ThetaLowerSegment 2173657344 2173788416 (54339948998319 / 25000) (54343191147047 / 25000) := by
  exact
    packedTile65536 2173657344 2173788416 14 6032 46622 31 _ _ (1074983 / 50000) (2149969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173788416 :
    ThetaLowerSegment 2173788416 2173919488 (54343191147047 / 25000) (13586618135453 / 6250) := by
  exact
    packedTile65536 2173788416 2173919488 14 6105 46623 31 _ _ (537493 / 25000) (85999 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2173919488 :
    ThetaLowerSegment 2173919488 2174050560 (13586618135453 / 6250) (108699525091293 / 50000) := by
  exact
    packedTile65536 2173919488 2174050560 14 6121 46625 31 _ _ (1074989 / 50000) (2149981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174050560 :
    ThetaLowerSegment 2174050560 2174181632 (108699525091293 / 50000)
      (108706087917453 / 50000) := by
  exact
    packedTile65536 2174050560 2174181632 14 6105 46626 31 _ _ (67187 / 3125) (2149987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174181632 :
    ThetaLowerSegment 2174181632 2174312704 (108706087917453 / 50000)
      (108712576587273 / 50000) := by
  exact
    packedTile65536 2174181632 2174312704 14 6036 46628 31 _ _ (214999 / 10000) (2149993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174312704 :
    ThetaLowerSegment 2174312704 2174443776 (108712576587273 / 50000)
      (108719216849919 / 50000) := by
  exact
    packedTile65536 2174312704 2174443776 14 6177 46629 31 _ _ (537499 / 25000) (2149999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174443776 :
    ThetaLowerSegment 2174443776 2174574848 (108719216849919 / 50000)
      (108725669005921 / 50000) := by
  exact
    packedTile65536 2174443776 2174574848 14 6002 46630 31 _ _ (1075001 / 50000) (430001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174574848 :
    ThetaLowerSegment 2174574848 2174705920 (108725669005921 / 50000)
      (108732183530161 / 50000) := by
  exact
    packedTile65536 2174574848 2174705920 14 6060 46632 31 _ _ (268751 / 12500) (2150011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174705920 :
    ThetaLowerSegment 2174705920 2174836992 (108732183530161 / 50000)
      (108738814173337 / 50000) := by
  exact
    packedTile65536 2174705920 2174836992 14 6168 46633 31 _ _ (1075007 / 50000) (2150017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174836992 :
    ThetaLowerSegment 2174836992 2174968064 (108738814173337 / 50000)
      (108745359909227 / 50000) := by
  exact
    packedTile65536 2174836992 2174968064 14 6089 46635 31 _ _ (107501 / 5000) (2150023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2174968064 :
    ThetaLowerSegment 2174968064 2175099136 (108745359909227 / 50000)
      (108751971239177 / 50000) := by
  exact
    packedTile65536 2174968064 2175099136 14 6150 46636 31 _ _ (1075013 / 50000) (2150029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175099136 :
    ThetaLowerSegment 2175099136 2175230208 (108751971239177 / 50000) (43503418846043 / 20000) := by
  exact
    packedTile65536 2175099136 2175230208 14 6117 46637 31 _ _ (2150033 / 100000) (537509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175230208 :
    ThetaLowerSegment 2175230208 2175361280 (43503418846043 / 20000) (27191289890013 / 12500) := by
  exact
    packedTile65536 2175230208 2175361280 14 6151 46639 31 _ _ (2150039 / 100000) (1075021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175361280 :
    ThetaLowerSegment 2175361280 2175492352 (27191289890013 / 12500) (108771706447077 / 50000) := by
  exact
    packedTile65536 2175361280 2175492352 14 6090 46640 31 _ _ (430009 / 20000) (67189 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175492352 :
    ThetaLowerSegment 2175492352 2175623424 (108771706447077 / 50000) (543891567769 / 250) := by
  exact
    packedTile65536 2175492352 2175623424 14 6146 46642 31 _ _ (2150051 / 100000) (1075027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175623424 :
    ThetaLowerSegment 2175623424 2175754496 (543891567769 / 250) (54392431313711 / 25000) := by
  exact
    packedTile65536 2175623424 2175754496 14 6092 46643 31 _ _ (2150057 / 100000) (107503 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175754496 :
    ThetaLowerSegment 2175754496 2175885568 (54392431313711 / 25000)
      (217582851389459 / 100000) := by
  exact
    packedTile65536 2175754496 2175885568 14 6105 46644 31 _ _ (2150063 / 100000) (1075033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2175885568 :
    ThetaLowerSegment 2175885568 2176016640 (217582851389459 / 100000) (13599742147337 / 6250) := by
  exact
    packedTile65536 2175885568 2176016640 14 6057 46646 31 _ _ (2150069 / 100000) (268759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176016640 :
    ThetaLowerSegment 2176016640 2176147712 (13599742147337 / 6250) (217609077967967 / 100000) := by
  exact
    packedTile65536 2176016640 2176147712 14 6141 46647 31 _ _ (86003 / 4000) (1075039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176147712 :
    ThetaLowerSegment 2176147712 2176278784 (217609077967967 / 100000)
      (217622257964497 / 100000) := by
  exact
    packedTile65536 2176147712 2176278784 14 6130 46649 31 _ _ (2150081 / 100000) (537521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176278784 :
    ThetaLowerSegment 2176278784 2176409856 (217622257964497 / 100000)
      (217635330493457 / 100000) := by
  exact
    packedTile65536 2176278784 2176409856 14 6080 46650 31 _ _ (2150087 / 100000) (215009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176409856 :
    ThetaLowerSegment 2176409856 2176540928 (217635330493457 / 100000)
      (108824163902821 / 50000) := by
  exact
    packedTile65536 2176409856 2176540928 14 6045 46652 31 _ _ (2150093 / 100000) (134381 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176540928 :
    ThetaLowerSegment 2176540928 2176672000 (108824163902821 / 50000)
      (108830764706751 / 50000) := by
  exact
    packedTile65536 2176540928 2176672000 14 6140 46653 31 _ _ (2150099 / 100000) (1075051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176672000 :
    ThetaLowerSegment 2176672000 2176803072 (108830764706751 / 50000)
      (217674793411247 / 100000) := by
  exact
    packedTile65536 2176672000 2176803072 14 6169 46654 31 _ _ (430021 / 20000) (537527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176803072 :
    ThetaLowerSegment 2176803072 2176934144 (217674793411247 / 100000)
      (108843985720783 / 50000) := by
  exact
    packedTile65536 2176803072 2176934144 14 6129 46656 31 _ _ (2150111 / 100000) (1075057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2176934144 :
    ThetaLowerSegment 2176934144 2177065216 (108843985720783 / 50000) (21770111295667 / 10000) := by
  exact
    packedTile65536 2176934144 2177065216 14 6112 46657 31 _ _ (2150117 / 100000) (53753 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177065216 :
    ThetaLowerSegment 2177065216 2177196288 (21770111295667 / 10000) (54428556101681 / 25000) := by
  exact
    packedTile65536 2177065216 2177196288 14 6098 46659 31 _ _ (2150123 / 100000) (1075063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177196288 :
    ThetaLowerSegment 2177196288 2177327360 (54428556101681 / 25000) (6803973468196 / 3125) := by
  exact
    packedTile65536 2177196288 2177327360 14 6012 46660 31 _ _ (2150129 / 100000) (537533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177327360 :
    ThetaLowerSegment 2177327360 2177458432 (6803973468196 / 3125) (217740256055097 / 100000) := by
  exact
    packedTile65536 2177327360 2177458432 14 6095 46661 31 _ _ (430027 / 20000) (1075069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177458432 :
    ThetaLowerSegment 2177458432 2177589504 (217740256055097 / 100000) (10887664617999 / 5000) := by
  exact
    packedTile65536 2177458432 2177589504 14 6063 46663 31 _ _ (2150141 / 100000) (67192 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177589504 :
    ThetaLowerSegment 2177589504 2177720576 (10887664617999 / 5000) (217766384605063 / 100000) := by
  exact
    packedTile65536 2177589504 2177720576 14 6089 46664 31 _ _ (2150147 / 100000) (43003 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177720576 :
    ThetaLowerSegment 2177720576 2177851648 (217766384605063 / 100000)
      (217779474736527 / 100000) := by
  exact
    packedTile65536 2177720576 2177851648 14 6088 46666 31 _ _ (2150153 / 100000) (537539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177851648 :
    ThetaLowerSegment 2177851648 2177982720 (217779474736527 / 100000)
      (217792625108971 / 100000) := by
  exact
    packedTile65536 2177851648 2177982720 14 6116 46667 31 _ _ (2150159 / 100000) (1075081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2177982720 :
    ThetaLowerSegment 2177982720 2178113792 (217792625108971 / 100000)
      (27225736184607 / 12500) := by
  exact
    packedTile65536 2177982720 2178113792 14 6169 46668 31 _ _ (430033 / 20000) (268771 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178113792 :
    ThetaLowerSegment 2178113792 2178244864 (27225736184607 / 12500)
      (217818999069443 / 100000) := by
  exact
    packedTile65536 2178113792 2178244864 14 6097 46670 31 _ _ (2150171 / 100000) (1075087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178244864 :
    ThetaLowerSegment 2178244864 2178375936 (217818999069443 / 100000)
      (54458057277131 / 25000) := by
  exact
    packedTile65536 2178244864 2178375936 14 6153 46671 31 _ _ (2150177 / 100000) (107509 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178375936 :
    ThetaLowerSegment 2178375936 2178507008 (54458057277131 / 25000)
      (217845429081961 / 100000) := by
  exact
    packedTile65536 2178375936 2178507008 14 6139 46673 31 _ _ (2150183 / 100000) (1075093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178507008 :
    ThetaLowerSegment 2178507008 2178638080 (217845429081961 / 100000)
      (43571715927577 / 20000) := by
  exact
    packedTile65536 2178507008 2178638080 14 6116 46674 31 _ _ (2150189 / 100000) (134387 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178638080 :
    ThetaLowerSegment 2178638080 2178769152 (43571715927577 / 20000) (43574358947271 / 20000) := by
  exact
    packedTile65536 2178638080 2178769152 14 6146 46675 31 _ _ (430039 / 20000) (1075099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178769152 :
    ThetaLowerSegment 2178769152 2178900224 (43574358947271 / 20000)
      (217884898061249 / 100000) := by
  exact
    packedTile65536 2178769152 2178900224 14 6094 46677 31 _ _ (2150201 / 100000) (537551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2178900224 :
    ThetaLowerSegment 2178900224 2179031296 (217884898061249 / 100000)
      (54474508418953 / 25000) := by
  exact
    packedTile65536 2178900224 2179031296 14 6109 46678 31 _ _ (2150207 / 100000) (215021 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179031296 :
    ThetaLowerSegment 2179031296 2179162368 (54474508418953 / 25000) (54477781043139 / 25000) := by
  exact
    packedTile65536 2179031296 2179162368 14 6088 46680 31 _ _ (2150213 / 100000) (268777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179162368 :
    ThetaLowerSegment 2179162368 2179293440 (54477781043139 / 25000) (108962032095249 / 50000) := by
  exact
    packedTile65536 2179162368 2179293440 14 6018 46681 31 _ _ (2150219 / 100000) (1075111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179293440 :
    ThetaLowerSegment 2179293440 2179424512 (108962032095249 / 50000) (54484311267437 / 25000) := by
  exact
    packedTile65536 2179293440 2179424512 14 6130 46682 31 _ _ (86009 / 4000) (537557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179424512 :
    ThetaLowerSegment 2179424512 2179555584 (54484311267437 / 25000)
      (217950256117529 / 100000) := by
  exact
    packedTile65536 2179424512 2179555584 14 6051 46684 31 _ _ (2150231 / 100000) (1075117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179555584 :
    ThetaLowerSegment 2179555584 2179686656 (217950256117529 / 100000) (6811351024932 / 3125) := by
  exact
    packedTile65536 2179555584 2179686656 14 6035 46685 31 _ _ (2150237 / 100000) (13439 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179686656 :
    ThetaLowerSegment 2179686656 2179817728 (6811351024932 / 3125) (8719050272787 / 4000) := by
  exact
    packedTile65536 2179686656 2179817728 14 6057 46687 31 _ _ (2150243 / 100000) (1075123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179817728 :
    ThetaLowerSegment 2179817728 2179948800 (8719050272787 / 4000) (217989455048037 / 100000) := by
  exact
    packedTile65536 2179817728 2179948800 14 6138 46688 31 _ _ (2150249 / 100000) (537563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2179948800 :
    ThetaLowerSegment 2179948800 2180079872 (217989455048037 / 100000)
      (109001258923581 / 50000) := by
  exact
    packedTile65536 2179948800 2180079872 14 6075 46689 31 _ _ (430051 / 20000) (1075129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180079872 :
    ThetaLowerSegment 2180079872 2180210944 (109001258923581 / 50000)
      (109007800017543 / 50000) := by
  exact
    packedTile65536 2180079872 2180210944 14 6084 46691 31 _ _ (2150261 / 100000) (268783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180210944 :
    ThetaLowerSegment 2180210944 2180342016 (109007800017543 / 50000)
      (218028843529539 / 100000) := by
  exact
    packedTile65536 2180210944 2180342016 14 6159 46692 31 _ _ (2150267 / 100000) (215027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180342016 :
    ThetaLowerSegment 2180342016 2180473088 (218028843529539 / 100000)
      (109020974721737 / 50000) := by
  exact
    packedTile65536 2180342016 2180473088 14 6095 46694 31 _ _ (2150273 / 100000) (537569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180473088 :
    ThetaLowerSegment 2180473088 2180604160 (109020974721737 / 50000) (27256863378091 / 12500) := by
  exact
    packedTile65536 2180473088 2180604160 14 6026 46695 31 _ _ (2150279 / 100000) (1075141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180604160 :
    ThetaLowerSegment 2180604160 2180735232 (27256863378091 / 12500)
      (218067901196983 / 100000) := by
  exact
    packedTile65536 2180604160 2180735232 14 6043 46696 31 _ _ (430057 / 20000) (134393 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180735232 :
    ThetaLowerSegment 2180735232 2180866304 (218067901196983 / 100000)
      (43616217356279 / 20000) := by
  exact
    packedTile65536 2180735232 2180866304 14 6132 46698 31 _ _ (2150291 / 100000) (1075147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180866304 :
    ThetaLowerSegment 2180866304 2180997376 (43616217356279 / 20000)
      (218094336911509 / 100000) := by
  exact
    packedTile65536 2180866304 2180997376 14 6162 46699 31 _ _ (2150297 / 100000) (21503 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2180997376 :
    ThetaLowerSegment 2180997376 2181128448 (218094336911509 / 100000)
      (218107389250719 / 100000) := by
  exact
    packedTile65536 2180997376 2181128448 14 6070 46701 31 _ _ (2150303 / 100000) (1075153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181128448 :
    ThetaLowerSegment 2181128448 2181259520 (218107389250719 / 100000)
      (218120273902247 / 100000) := by
  exact
    packedTile65536 2181128448 2181259520 14 5992 46702 31 _ _ (2150309 / 100000) (268789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181259520 :
    ThetaLowerSegment 2181259520 2181390592 (218120273902247 / 100000)
      (109066683585141 / 50000) := by
  exact
    packedTile65536 2181259520 2181390592 14 6089 46703 31 _ _ (430063 / 20000) (1075159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181390592 :
    ThetaLowerSegment 2181390592 2181521664 (109066683585141 / 50000) (27268296001381 / 12500) := by
  exact
    packedTile65536 2181390592 2181521664 14 6046 46705 31 _ _ (2150321 / 100000) (537581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181521664 :
    ThetaLowerSegment 2181521664 2181652736 (27268296001381 / 12500) (109079740352547 / 50000) := by
  exact
    packedTile65536 2181521664 2181652736 14 6098 46706 31 _ _ (2150327 / 100000) (215033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181652736 :
    ThetaLowerSegment 2181652736 2181783808 (109079740352547 / 50000) (54543176313261 / 25000) := by
  exact
    packedTile65536 2181652736 2181783808 14 6150 46708 31 _ _ (2150333 / 100000) (67198 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181783808 :
    ThetaLowerSegment 2181783808 2181914880 (54543176313261 / 25000)
      (218185790065859 / 100000) := by
  exact
    packedTile65536 2181783808 2181914880 14 6085 46709 31 _ _ (2150339 / 100000) (1075171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2181914880 :
    ThetaLowerSegment 2181914880 2182045952 (218185790065859 / 100000)
      (109099465412077 / 50000) := by
  exact
    packedTile65536 2181914880 2182045952 14 6111 46710 31 _ _ (430069 / 20000) (537587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182045952 :
    ThetaLowerSegment 2182045952 2182177024 (109099465412077 / 50000) (54552948555959 / 25000) := by
  exact
    packedTile65536 2182045952 2182177024 14 5982 46712 31 _ _ (2150351 / 100000) (1075177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182177024 :
    ThetaLowerSegment 2182177024 2182308096 (54552948555959 / 25000) (109112401941843 / 50000) := by
  exact
    packedTile65536 2182177024 2182308096 14 6050 46713 31 _ _ (2150357 / 100000) (53759 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182308096 :
    ThetaLowerSegment 2182308096 2182439168 (109112401941843 / 50000)
      (218237871639637 / 100000) := by
  exact
    packedTile65536 2182308096 2182439168 14 6077 46715 31 _ _ (2150363 / 100000) (1075183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182439168 :
    ThetaLowerSegment 2182439168 2182570240 (218237871639637 / 100000)
      (54562692925817 / 25000) := by
  exact
    packedTile65536 2182439168 2182570240 14 5999 46716 31 _ _ (2150369 / 100000) (537593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182570240 :
    ThetaLowerSegment 2182570240 2182701312 (54562692925817 / 25000) (109131946645759 / 50000) := by
  exact
    packedTile65536 2182570240 2182701312 14 6102 46717 31 _ _ (17203 / 800) (1075189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182701312 :
    ThetaLowerSegment 2182701312 2182832384 (109131946645759 / 50000) (43655396532133 / 20000) := by
  exact
    packedTile65536 2182701312 2182832384 14 6087 46719 31 _ _ (2150381 / 100000) (134399 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182832384 :
    ThetaLowerSegment 2182832384 2182963456 (43655396532133 / 20000) (109145031732393 / 50000) := by
  exact
    packedTile65536 2182832384 2182963456 14 6083 46720 31 _ _ (2150387 / 100000) (215039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2182963456 :
    ThetaLowerSegment 2182963456 2183094528 (109145031732393 / 50000)
      (109151616235759 / 50000) := by
  exact
    packedTile65536 2182963456 2183094528 14 6124 46722 31 _ _ (2150393 / 100000) (537599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183094528 :
    ThetaLowerSegment 2183094528 2183225600 (109151616235759 / 50000)
      (218316347755019 / 100000) := by
  exact
    packedTile65536 2183094528 2183225600 14 6099 46723 31 _ _ (2150399 / 100000) (1075201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183225600 :
    ThetaLowerSegment 2183225600 2183356672 (218316347755019 / 100000) (13645584722179 / 6250) := by
  exact
    packedTile65536 2183225600 2183356672 14 6049 46724 31 _ _ (430081 / 20000) (268801 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183356672 :
    ThetaLowerSegment 2183356672 2183487744 (13645584722179 / 6250) (218342462309909 / 100000) := by
  exact
    packedTile65536 2183356672 2183487744 14 6095 46726 31 _ _ (2150411 / 100000) (1075207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183487744 :
    ThetaLowerSegment 2183487744 2183618816 (218342462309909 / 100000) (10917779315243 / 5000) := by
  exact
    packedTile65536 2183487744 2183618816 14 6103 46727 31 _ _ (2150417 / 100000) (107521 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183618816 :
    ThetaLowerSegment 2183618816 2183749888 (10917779315243 / 5000) (109184289580313 / 50000) := by
  exact
    packedTile65536 2183618816 2183749888 14 6042 46729 31 _ _ (2150423 / 100000) (1075213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183749888 :
    ThetaLowerSegment 2183749888 2183880960 (109184289580313 / 50000)
      (109190878494769 / 50000) := by
  exact
    packedTile65536 2183749888 2183880960 14 6128 46730 31 _ _ (2150429 / 100000) (67201 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2183880960 :
    ThetaLowerSegment 2183880960 2184012032 (109190878494769 / 50000)
      (109197488931959 / 50000) := by
  exact
    packedTile65536 2183880960 2184012032 14 6148 46732 31 _ _ (430087 / 20000) (1075219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184012032 :
    ThetaLowerSegment 2184012032 2184143104 (109197488931959 / 50000)
      (218407977279763 / 100000) := by
  exact
    packedTile65536 2184012032 2184143104 14 6045 46733 31 _ _ (2150441 / 100000) (537611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184143104 :
    ThetaLowerSegment 2184143104 2184274176 (218407977279763 / 100000)
      (27302643058343 / 12500) := by
  exact
    packedTile65536 2184143104 2184274176 14 6123 46734 31 _ _ (2150447 / 100000) (43009 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184274176 :
    ThetaLowerSegment 2184274176 2184405248 (27302643058343 / 12500) (109217124663663 / 50000) := by
  exact
    packedTile65536 2184274176 2184405248 14 6094 46736 31 _ _ (2150453 / 100000) (268807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184405248 :
    ThetaLowerSegment 2184405248 2184536320 (109217124663663 / 50000) (21844731551621 / 10000) := by
  exact
    packedTile65536 2184405248 2184536320 14 6076 46737 31 _ _ (2150459 / 100000) (1075231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184536320 :
    ThetaLowerSegment 2184536320 2184667392 (21844731551621 / 10000) (5461509220969 / 2500) := by
  exact
    packedTile65536 2184536320 2184667392 14 6070 46739 31 _ _ (430093 / 20000) (537617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184667392 :
    ThetaLowerSegment 2184667392 2184798464 (5461509220969 / 2500) (218473557677403 / 100000) := by
  exact
    packedTile65536 2184667392 2184798464 14 6133 46740 31 _ _ (2150471 / 100000) (1075237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184798464 :
    ThetaLowerSegment 2184798464 2184929536 (218473557677403 / 100000)
      (218486662684241 / 100000) := by
  exact
    packedTile65536 2184798464 2184929536 14 6094 46741 31 _ _ (2150477 / 100000) (26881 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2184929536 :
    ThetaLowerSegment 2184929536 2185060608 (218486662684241 / 100000)
      (27312466396179 / 12500) := by
  exact
    packedTile65536 2184929536 2185060608 14 6077 46743 31 _ _ (2150483 / 100000) (1075243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185060608 :
    ThetaLowerSegment 2185060608 2185191680 (27312466396179 / 12500)
      (218512868506733 / 100000) := by
  exact
    packedTile65536 2185060608 2185191680 14 6109 46744 31 _ _ (2150489 / 100000) (537623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185191680 :
    ThetaLowerSegment 2185191680 2185322752 (218512868506733 / 100000)
      (218525939215343 / 100000) := by
  exact
    packedTile65536 2185191680 2185322752 14 6078 46746 31 _ _ (430099 / 20000) (1075249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185322752 :
    ThetaLowerSegment 2185322752 2185339136 (218525939215343 / 100000)
      (43705515579421 / 20000) := by
  exact
    packedTile65536 2185322752 2185339136 11 762 46747 31 _ _ (2150501 / 100000) (268813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185339136 :
    ThetaLowerSegment 2185339136 2185341184 (43705515579421 / 20000)
      (218527790796803 / 100000) := by
  exact
    packedTile65536 2185339136 2185341184 8 99 46747 31 _ _ (1075251 / 50000) (430101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2153341184_2185341184 :
    ThetaLowerSegment 2153341184 2185341184 (215328072469243 / 100000)
      (218527790796803 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2153341184 cell2153472256)
                  (ThetaLowerSegment.join cell2153603328 cell2153734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2153865472 cell2153996544)
                  (ThetaLowerSegment.join cell2154127616 cell2154258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2154389760 cell2154520832)
                  (ThetaLowerSegment.join cell2154651904 cell2154782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2154914048 cell2155045120)
                  (ThetaLowerSegment.join cell2155176192 cell2155307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2155438336 cell2155569408)
                  (ThetaLowerSegment.join cell2155700480 cell2155831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2155962624 cell2156093696)
                  (ThetaLowerSegment.join cell2156224768 cell2156355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2156486912 cell2156617984)
                  (ThetaLowerSegment.join cell2156749056 cell2156880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2157011200 cell2157142272)
                  (ThetaLowerSegment.join cell2157273344 cell2157404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2157535488 cell2157666560)
                  (ThetaLowerSegment.join cell2157797632 cell2157928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2158059776 cell2158190848)
                  (ThetaLowerSegment.join cell2158321920 cell2158452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2158584064 cell2158715136)
                  (ThetaLowerSegment.join cell2158846208 cell2158977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2159108352 cell2159239424)
                  (ThetaLowerSegment.join cell2159370496 cell2159501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2159632640 cell2159763712)
                  (ThetaLowerSegment.join cell2159894784 cell2160025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2160156928 cell2160288000)
                  (ThetaLowerSegment.join cell2160419072 cell2160550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2160681216 cell2160812288)
                  (ThetaLowerSegment.join cell2160943360 cell2161074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2161205504 cell2161336576)
                  (ThetaLowerSegment.join cell2161467648 cell2161598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2161729792 cell2161860864)
                  (ThetaLowerSegment.join cell2161991936 cell2162123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2162254080 cell2162385152)
                  (ThetaLowerSegment.join cell2162516224 cell2162647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2162778368 cell2162909440)
                  (ThetaLowerSegment.join cell2163040512 cell2163171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2163302656 cell2163433728)
                  (ThetaLowerSegment.join cell2163564800 cell2163695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2163826944 cell2163958016)
                  (ThetaLowerSegment.join cell2164089088 cell2164220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2164351232 cell2164482304)
                  (ThetaLowerSegment.join cell2164613376 cell2164744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2164875520 cell2165006592)
                  (ThetaLowerSegment.join cell2165137664 cell2165268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2165399808 cell2165530880)
                  (ThetaLowerSegment.join cell2165661952 cell2165793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2165924096 cell2166055168)
                  (ThetaLowerSegment.join cell2166186240 cell2166317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2166448384 cell2166579456)
                  (ThetaLowerSegment.join cell2166710528 cell2166841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2166972672 cell2167103744)
                  (ThetaLowerSegment.join cell2167234816 cell2167365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2167496960 cell2167628032)
                  (ThetaLowerSegment.join cell2167759104 cell2167890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2168021248 cell2168152320)
                  (ThetaLowerSegment.join cell2168283392 cell2168414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2168545536 cell2168676608)
                  (ThetaLowerSegment.join cell2168807680 cell2168938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2169069824 cell2169200896)
                  (ThetaLowerSegment.join cell2169331968 cell2169463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2169594112 cell2169725184)
                  (ThetaLowerSegment.join cell2169856256 cell2169987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2170118400 cell2170249472)
                  (ThetaLowerSegment.join cell2170380544 cell2170511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2170642688 cell2170773760)
                  (ThetaLowerSegment.join cell2170904832 cell2171035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2171166976 cell2171298048)
                  (ThetaLowerSegment.join cell2171429120 cell2171560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2171691264 cell2171822336)
                  (ThetaLowerSegment.join cell2171953408 cell2172084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2172215552 cell2172346624)
                  (ThetaLowerSegment.join cell2172477696 cell2172608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2172739840 cell2172870912)
                  (ThetaLowerSegment.join cell2173001984 cell2173133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2173264128 cell2173395200)
                  (ThetaLowerSegment.join cell2173526272 cell2173657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2173788416 cell2173919488)
                  (ThetaLowerSegment.join cell2174050560 cell2174181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2174312704 cell2174443776)
                  (ThetaLowerSegment.join cell2174574848 cell2174705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2174836992 cell2174968064)
                  (ThetaLowerSegment.join cell2175099136 cell2175230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2175361280 cell2175492352)
                  (ThetaLowerSegment.join cell2175623424 cell2175754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2175885568 cell2176016640)
                  (ThetaLowerSegment.join cell2176147712 cell2176278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2176409856 cell2176540928)
                  (ThetaLowerSegment.join cell2176672000 cell2176803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2176934144 cell2177065216)
                  (ThetaLowerSegment.join cell2177196288 cell2177327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2177458432 cell2177589504)
                  (ThetaLowerSegment.join cell2177720576 cell2177851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2177982720 cell2178113792)
                  (ThetaLowerSegment.join cell2178244864 cell2178375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2178507008 cell2178638080)
                  (ThetaLowerSegment.join cell2178769152 cell2178900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2179031296 cell2179162368)
                  (ThetaLowerSegment.join cell2179293440 cell2179424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2179555584 cell2179686656)
                  (ThetaLowerSegment.join cell2179817728 cell2179948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2180079872 cell2180210944)
                  (ThetaLowerSegment.join cell2180342016 cell2180473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2180604160 cell2180735232)
                  (ThetaLowerSegment.join cell2180866304 cell2180997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2181128448 cell2181259520)
                  (ThetaLowerSegment.join cell2181390592 cell2181521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2181652736 cell2181783808)
                  (ThetaLowerSegment.join cell2181914880 cell2182045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2182177024 cell2182308096)
                  (ThetaLowerSegment.join cell2182439168 cell2182570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2182701312 cell2182832384)
                  (ThetaLowerSegment.join cell2182963456 cell2183094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2183225600 cell2183356672)
                  (ThetaLowerSegment.join cell2183487744 cell2183618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2183749888 cell2183880960)
                  (ThetaLowerSegment.join cell2184012032 cell2184143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2184274176 cell2184405248)
                  (ThetaLowerSegment.join cell2184536320 cell2184667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2184798464 cell2184929536)
                (ThetaLowerSegment.join cell2185060608 cell2185191680))
              (ThetaLowerSegment.join cell2185322752 cell2185339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
