/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1129341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1097341184 :
    ThetaLowerSegment 1097341184 1097472256 (109731766317517 / 100000)
      (109744834690209 / 100000) := by
  exact
    packedTile65536 1097341184 1097472256 14 6278 33126 30 _ _ (1040807 / 50000) (2081617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097472256 :
    ThetaLowerSegment 1097472256 1097603328 (109744834690209 / 100000)
      (109758090484577 / 100000) := by
  exact
    packedTile65536 1097472256 1097603328 14 6368 33128 30 _ _ (1040813 / 50000) (2081629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097603328 :
    ThetaLowerSegment 1097603328 1097734400 (109758090484577 / 100000)
      (109771079905697 / 100000) := by
  exact
    packedTile65536 1097603328 1097734400 14 6240 33130 30 _ _ (1040819 / 50000) (2081641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097734400 :
    ThetaLowerSegment 1097734400 1097865472 (109771079905697 / 100000)
      (109784185974097 / 100000) := by
  exact
    packedTile65536 1097734400 1097865472 14 6296 33132 30 _ _ (41633 / 2000) (2081653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097865472 :
    ThetaLowerSegment 1097865472 1097996544 (109784185974097 / 100000)
      (109797179708301 / 100000) := by
  exact
    packedTile65536 1097865472 1097996544 14 6242 33134 30 _ _ (1040831 / 50000) (416333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097996544 :
    ThetaLowerSegment 1097996544 1098127616 (109797179708301 / 100000)
      (109810435808333 / 100000) := by
  exact
    packedTile65536 1097996544 1098127616 14 6368 33136 30 _ _ (1040837 / 50000) (2081677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098127616 :
    ThetaLowerSegment 1098127616 1098258688 (109810435808333 / 100000)
      (109823577492051 / 100000) := by
  exact
    packedTile65536 1098127616 1098258688 14 6313 33138 30 _ _ (1040843 / 50000) (2081689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098258688 :
    ThetaLowerSegment 1098258688 1098389760 (109823577492051 / 100000)
      (109836767130579 / 100000) := by
  exact
    packedTile65536 1098258688 1098389760 14 6336 33139 30 _ _ (1040849 / 50000) (2081701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098389760 :
    ThetaLowerSegment 1098389760 1098520832 (109836767130579 / 100000)
      (109849721611909 / 100000) := by
  exact
    packedTile65536 1098389760 1098520832 14 6223 33141 30 _ _ (208171 / 10000) (2081713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098520832 :
    ThetaLowerSegment 1098520832 1098651904 (109849721611909 / 100000)
      (109862819806733 / 100000) := by
  exact
    packedTile65536 1098520832 1098651904 14 6292 33143 30 _ _ (1040861 / 50000) (83269 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098651904 :
    ThetaLowerSegment 1098651904 1098782976 (109862819806733 / 100000)
      (10987587019091 / 10000) := by
  exact
    packedTile65536 1098651904 1098782976 14 6269 33145 30 _ _ (2081733 / 100000) (260217 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098782976 :
    ThetaLowerSegment 1098782976 1098914048 (10987587019091 / 10000) (4395559157567 / 4000) := by
  exact
    packedTile65536 1098782976 1098914048 14 6297 33147 30 _ _ (416349 / 20000) (520437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1098914048 :
    ThetaLowerSegment 1098914048 1099045120 (4395559157567 / 4000) (54950971020007 / 50000) := by
  exact
    packedTile65536 1098914048 1099045120 14 6227 33149 30 _ _ (2081757 / 100000) (13011 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099045120 :
    ThetaLowerSegment 1099045120 1099176192 (54950971020007 / 50000) (27478815299519 / 25000) := by
  exact
    packedTile65536 1099045120 1099176192 14 6398 33151 30 _ _ (2081769 / 100000) (520443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099176192 :
    ThetaLowerSegment 1099176192 1099307264 (27478815299519 / 25000) (21985649885947 / 20000) := by
  exact
    packedTile65536 1099176192 1099307264 14 6239 33153 30 _ _ (2081781 / 100000) (260223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099307264 :
    ThetaLowerSegment 1099307264 1099438336 (21985649885947 / 20000) (5497075002109 / 5000) := by
  exact
    packedTile65536 1099307264 1099438336 14 6365 33155 30 _ _ (2081793 / 100000) (520449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099438336 :
    ThetaLowerSegment 1099438336 1099569408 (5497075002109 / 5000) (10995450299621 / 10000) := by
  exact
    packedTile65536 1099438336 1099569408 14 6246 33157 30 _ _ (416361 / 20000) (130113 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099569408 :
    ThetaLowerSegment 1099569408 1099700480 (10995450299621 / 10000)
      (109967641343297 / 100000) := by
  exact
    packedTile65536 1099569408 1099700480 14 6311 33159 30 _ _ (2081817 / 100000) (104091 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099700480 :
    ThetaLowerSegment 1099700480 1099831552 (109967641343297 / 100000)
      (54990379473913 / 50000) := by
  exact
    packedTile65536 1099700480 1099831552 14 6301 33161 30 _ _ (2081829 / 100000) (260229 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099831552 :
    ThetaLowerSegment 1099831552 1099962624 (54990379473913 / 50000)
      (109993926592151 / 100000) := by
  exact
    packedTile65536 1099831552 1099962624 14 6325 33163 30 _ _ (2081841 / 100000) (520461 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099962624 :
    ThetaLowerSegment 1099962624 1100093696 (109993926592151 / 100000)
      (55003457636509 / 50000) := by
  exact
    packedTile65536 1099962624 1100093696 14 6239 33165 30 _ _ (2081853 / 100000) (65058 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100093696 :
    ThetaLowerSegment 1100093696 1100224768 (55003457636509 / 50000)
      (110020070577953 / 100000) := by
  exact
    packedTile65536 1100093696 1100224768 14 6319 33167 30 _ _ (416373 / 20000) (520467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100224768 :
    ThetaLowerSegment 1100224768 1100355840 (110020070577953 / 100000)
      (11003306357231 / 10000) := by
  exact
    packedTile65536 1100224768 1100355840 14 6241 33169 30 _ _ (2081877 / 100000) (52047 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100355840 :
    ThetaLowerSegment 1100355840 1100486912 (11003306357231 / 10000) (55023050177483 / 50000) := by
  exact
    packedTile65536 1100355840 1100486912 14 6262 33171 30 _ _ (65059 / 3125) (2081891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100486912 :
    ThetaLowerSegment 1100486912 1100617984 (55023050177483 / 50000) (55029568606383 / 50000) := by
  exact
    packedTile65536 1100486912 1100617984 14 6262 33173 30 _ _ (20819 / 1000) (2081903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100617984 :
    ThetaLowerSegment 1100617984 1100749056 (55029568606383 / 50000) (55036132874919 / 50000) := by
  exact
    packedTile65536 1100617984 1100749056 14 6306 33175 30 _ _ (260239 / 12500) (416383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100749056 :
    ThetaLowerSegment 1100749056 1100880128 (55036132874919 / 50000) (55042769007669 / 50000) := by
  exact
    packedTile65536 1100749056 1100880128 14 6375 33177 30 _ _ (520481 / 25000) (2081927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1100880128 :
    ThetaLowerSegment 1100880128 1101011200 (55042769007669 / 50000) (55049333351877 / 50000) := by
  exact
    packedTile65536 1100880128 1101011200 14 6306 33179 30 _ _ (130121 / 6250) (2081939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101011200 :
    ThetaLowerSegment 1101011200 1101142272 (55049333351877 / 50000) (55055887324181 / 50000) := by
  exact
    packedTile65536 1101011200 1101142272 14 6296 33181 30 _ _ (520487 / 25000) (2081951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101142272 :
    ThetaLowerSegment 1101142272 1101273344 (55055887324181 / 50000) (55062441334261 / 50000) := by
  exact
    packedTile65536 1101142272 1101273344 14 6296 33183 30 _ _ (52049 / 2500) (2081963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101273344 :
    ThetaLowerSegment 1101273344 1101404416 (55062441334261 / 50000) (55068908980279 / 50000) := by
  exact
    packedTile65536 1101273344 1101404416 14 6213 33185 30 _ _ (520493 / 25000) (83279 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101404416 :
    ThetaLowerSegment 1101404416 1101535488 (55068908980279 / 50000) (55075424549207 / 50000) := by
  exact
    packedTile65536 1101404416 1101535488 14 6259 33187 30 _ _ (65062 / 3125) (2081987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101535488 :
    ThetaLowerSegment 1101535488 1101666560 (55075424549207 / 50000) (55082024476527 / 50000) := by
  exact
    packedTile65536 1101535488 1101666560 14 6340 33189 30 _ _ (520499 / 25000) (2081999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101666560 :
    ThetaLowerSegment 1101666560 1101797632 (55082024476527 / 50000)
      (110177105218951 / 100000) := by
  exact
    packedTile65536 1101666560 1101797632 14 6271 33191 30 _ _ (2082007 / 100000) (208201 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101797632 :
    ThetaLowerSegment 1101797632 1101928704 (110177105218951 / 100000)
      (11019014073991 / 10000) := by
  exact
    packedTile65536 1101797632 1101928704 14 6261 33193 30 _ _ (2082019 / 100000) (1041011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1101928704 :
    ThetaLowerSegment 1101928704 1102059776 (11019014073991 / 10000)
      (110203147187567 / 100000) := by
  exact
    packedTile65536 1101928704 1102059776 14 6247 33195 30 _ _ (2082031 / 100000) (1041017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102059776 :
    ThetaLowerSegment 1102059776 1102190848 (110203147187567 / 100000)
      (55108178875201 / 50000) := by
  exact
    packedTile65536 1102059776 1102190848 14 6345 33197 30 _ _ (2082043 / 100000) (1041023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102190848 :
    ThetaLowerSegment 1102190848 1102321920 (55108178875201 / 50000) (55114670722691 / 50000) := by
  exact
    packedTile65536 1102190848 1102321920 14 6236 33199 30 _ _ (416411 / 20000) (1041029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102321920 :
    ThetaLowerSegment 1102321920 1102452992 (55114670722691 / 50000)
      (110242552160497 / 100000) := by
  exact
    packedTile65536 1102321920 1102452992 14 6345 33201 30 _ _ (2082067 / 100000) (208207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102452992 :
    ThetaLowerSegment 1102452992 1102584064 (110242552160497 / 100000)
      (55127937692009 / 50000) := by
  exact
    packedTile65536 1102452992 1102584064 14 6399 33203 30 _ _ (2082079 / 100000) (1041041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102584064 :
    ThetaLowerSegment 1102584064 1102715136 (55127937692009 / 50000)
      (110269019624501 / 100000) := by
  exact
    packedTile65536 1102584064 1102715136 14 6313 33205 30 _ _ (2082091 / 100000) (1041047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102715136 :
    ThetaLowerSegment 1102715136 1102846208 (110269019624501 / 100000)
      (11028222640383 / 10000) := by
  exact
    packedTile65536 1102715136 1102846208 14 6343 33207 30 _ _ (2082103 / 100000) (1041053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102846208 :
    ThetaLowerSegment 1102846208 1102977280 (11028222640383 / 10000) (5514766145359 / 5000) := by
  exact
    packedTile65536 1102846208 1102977280 14 6290 33209 30 _ _ (416423 / 20000) (1041059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102977280 :
    ThetaLowerSegment 1102977280 1103108352 (5514766145359 / 5000) (55154202452419 / 50000) := by
  exact
    packedTile65536 1102977280 1103108352 14 6283 33211 30 _ _ (1041063 / 50000) (2082129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103108352 :
    ThetaLowerSegment 1103108352 1103239424 (55154202452419 / 50000) (13790207214151 / 12500) := by
  exact
    packedTile65536 1103108352 1103239424 14 6365 33213 30 _ _ (1041069 / 50000) (2082141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103239424 :
    ThetaLowerSegment 1103239424 1103370496 (13790207214151 / 12500) (55167388670179 / 50000) := by
  exact
    packedTile65536 1103239424 1103370496 14 6301 33215 30 _ _ (41643 / 2000) (2082153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103370496 :
    ThetaLowerSegment 1103370496 1103501568 (55167388670179 / 50000) (13793488171471 / 12500) := by
  exact
    packedTile65536 1103370496 1103501568 14 6305 33217 30 _ _ (1041081 / 50000) (416433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103501568 :
    ThetaLowerSegment 1103501568 1103632640 (13793488171471 / 12500) (55180616683771 / 50000) := by
  exact
    packedTile65536 1103501568 1103632640 14 6401 33218 30 _ _ (1041087 / 50000) (2082177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103632640 :
    ThetaLowerSegment 1103632640 1103763712 (55180616683771 / 50000) (689838302159 / 625) := by
  exact
    packedTile65536 1103632640 1103763712 14 6193 33220 30 _ _ (1041093 / 50000) (2082189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103763712 :
    ThetaLowerSegment 1103763712 1103894784 (689838302159 / 625) (27596800096121 / 25000) := by
  exact
    packedTile65536 1103763712 1103894784 14 6278 33222 30 _ _ (1041099 / 50000) (2082201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1103894784 :
    ThetaLowerSegment 1103894784 1104025856 (27596800096121 / 25000) (55200189345787 / 50000) := by
  exact
    packedTile65536 1103894784 1104025856 14 6329 33224 30 _ _ (208221 / 10000) (2082213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104025856 :
    ThetaLowerSegment 1104025856 1104156928 (55200189345787 / 50000) (13801703222697 / 12500) := by
  exact
    packedTile65536 1104025856 1104156928 14 6362 33226 30 _ _ (2082221 / 100000) (130139 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104156928 :
    ThetaLowerSegment 1104156928 1104288000 (13801703222697 / 12500)
      (110426737602777 / 100000) := by
  exact
    packedTile65536 1104156928 1104288000 14 6297 33228 30 _ _ (2082233 / 100000) (520559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104288000 :
    ThetaLowerSegment 1104288000 1104419072 (110426737602777 / 100000)
      (110440009832407 / 100000) := by
  exact
    packedTile65536 1104288000 1104419072 14 6374 33230 30 _ _ (416449 / 20000) (260281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104419072 :
    ThetaLowerSegment 1104419072 1104550144 (110440009832407 / 100000)
      (55226496352401 / 50000) := by
  exact
    packedTile65536 1104419072 1104550144 14 6235 33232 30 _ _ (2082257 / 100000) (104113 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104550144 :
    ThetaLowerSegment 1104550144 1104681216 (55226496352401 / 50000) (27616526708741 / 25000) := by
  exact
    packedTile65536 1104550144 1104681216 14 6298 33234 30 _ _ (2082269 / 100000) (65071 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104681216 :
    ThetaLowerSegment 1104681216 1104812288 (27616526708741 / 25000)
      (110479089856999 / 100000) := by
  exact
    packedTile65536 1104681216 1104812288 14 6235 33236 30 _ _ (2082281 / 100000) (520571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104812288 :
    ThetaLowerSegment 1104812288 1104943360 (110479089856999 / 100000)
      (13811522133563 / 12500) := by
  exact
    packedTile65536 1104812288 1104943360 14 6285 33238 30 _ _ (2082293 / 100000) (260287 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104943360 :
    ThetaLowerSegment 1104943360 1105074432 (13811522133563 / 12500) (2762631556671 / 2500) := by
  exact
    packedTile65536 1104943360 1105074432 14 6284 33240 30 _ _ (65072 / 3125) (2082307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105074432 :
    ThetaLowerSegment 1105074432 1105205504 (2762631556671 / 2500) (13814795524889 / 12500) := by
  exact
    packedTile65536 1105074432 1105205504 14 6292 33242 30 _ _ (520579 / 25000) (2082319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105205504 :
    ThetaLowerSegment 1105205504 1105336576 (13814795524889 / 12500) (13816435878771 / 12500) := by
  exact
    packedTile65536 1105205504 1105336576 14 6302 33244 30 _ _ (260291 / 12500) (2082331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105336576 :
    ThetaLowerSegment 1105336576 1105467648 (13816435878771 / 12500) (27636140510757 / 25000) := by
  exact
    packedTile65536 1105336576 1105467648 14 6279 33246 30 _ _ (104117 / 5000) (2082343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105467648 :
    ThetaLowerSegment 1105467648 1105598720 (27636140510757 / 25000) (27639385335761 / 25000) := by
  exact
    packedTile65536 1105467648 1105598720 14 6233 33248 30 _ _ (130147 / 6250) (416471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105598720 :
    ThetaLowerSegment 1105598720 1105729792 (27639385335761 / 25000) (2764267495029 / 2500) := by
  exact
    packedTile65536 1105598720 1105729792 14 6319 33250 30 _ _ (520591 / 25000) (2082367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105729792 :
    ThetaLowerSegment 1105729792 1105860864 (2764267495029 / 2500) (13822969016741 / 12500) := by
  exact
    packedTile65536 1105729792 1105860864 14 6268 33252 30 _ _ (260297 / 12500) (2082379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105860864 :
    ThetaLowerSegment 1105860864 1105991936 (13822969016741 / 12500) (27649217793007 / 25000) := by
  exact
    packedTile65536 1105860864 1105991936 14 6300 33254 30 _ _ (2082387 / 100000) (208239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1105991936 :
    ThetaLowerSegment 1105991936 1106123008 (27649217793007 / 25000) (3456562196429 / 3125) := by
  exact
    packedTile65536 1105991936 1106123008 14 6300 33256 30 _ _ (2082399 / 100000) (1041201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106123008 :
    ThetaLowerSegment 1106123008 1106254080 (3456562196429 / 3125) (11062307199163 / 10000) := by
  exact
    packedTile65536 1106123008 1106254080 14 6282 33258 30 _ _ (2082411 / 100000) (1041207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106254080 :
    ThetaLowerSegment 1106254080 1106385152 (11062307199163 / 10000) (27659013454153 / 25000) := by
  exact
    packedTile65536 1106254080 1106385152 14 6234 33260 30 _ _ (2082423 / 100000) (1041213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106385152 :
    ThetaLowerSegment 1106385152 1106516224 (27659013454153 / 25000)
      (110649146085457 / 100000) := by
  exact
    packedTile65536 1106385152 1106516224 14 6287 33262 30 _ _ (416487 / 20000) (1041219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106516224 :
    ThetaLowerSegment 1106516224 1106647296 (110649146085457 / 100000)
      (110662165544101 / 100000) := by
  exact
    packedTile65536 1106516224 1106647296 14 6252 33264 30 _ _ (2082447 / 100000) (41649 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106647296 :
    ThetaLowerSegment 1106647296 1106778368 (110662165544101 / 100000)
      (110675247551539 / 100000) := by
  exact
    packedTile65536 1106647296 1106778368 14 6282 33266 30 _ _ (2082459 / 100000) (1041231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106778368 :
    ThetaLowerSegment 1106778368 1106909440 (110675247551539 / 100000)
      (110688362947599 / 100000) := by
  exact
    packedTile65536 1106778368 1106909440 14 6298 33268 30 _ _ (208247 / 10000) (2082473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106909440 :
    ThetaLowerSegment 1106909440 1107040512 (110688362947599 / 100000)
      (110701565883479 / 100000) := by
  exact
    packedTile65536 1106909440 1107040512 14 6340 33270 30 _ _ (1041241 / 50000) (416497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107040512 :
    ThetaLowerSegment 1107040512 1107171584 (110701565883479 / 100000) (4428592338513 / 4000) := by
  exact
    packedTile65536 1107040512 1107171584 14 6359 33272 30 _ _ (1041247 / 50000) (2082497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107171584 :
    ThetaLowerSegment 1107171584 1107302656 (4428592338513 / 4000) (110727909508071 / 100000) := by
  exact
    packedTile65536 1107171584 1107302656 14 6291 33274 30 _ _ (1041253 / 50000) (2082509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107302656 :
    ThetaLowerSegment 1107302656 1107433728 (110727909508071 / 100000)
      (22148211288841 / 20000) := by
  exact
    packedTile65536 1107302656 1107433728 14 6313 33276 30 _ _ (1041259 / 50000) (2082521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107433728 :
    ThetaLowerSegment 1107433728 1107564800 (22148211288841 / 20000) (22150826113509 / 20000) := by
  exact
    packedTile65536 1107433728 1107564800 14 6278 33278 30 _ _ (208253 / 10000) (2082533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107564800 :
    ThetaLowerSegment 1107564800 1107695872 (22150826113509 / 20000) (27691847526523 / 25000) := by
  exact
    packedTile65536 1107564800 1107695872 14 6367 33280 30 _ _ (2082541 / 100000) (130159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107695872 :
    ThetaLowerSegment 1107695872 1107826944 (27691847526523 / 25000)
      (110780608069983 / 100000) := by
  exact
    packedTile65536 1107695872 1107826944 14 6347 33282 30 _ _ (2082553 / 100000) (520639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107826944 :
    ThetaLowerSegment 1107826944 1107958016 (110780608069983 / 100000)
      (55396829752419 / 50000) := by
  exact
    packedTile65536 1107826944 1107958016 14 6267 33284 30 _ _ (416513 / 20000) (260321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1107958016 :
    ThetaLowerSegment 1107958016 1108089088 (55396829752419 / 50000) (22161356364503 / 20000) := by
  exact
    packedTile65536 1107958016 1108089088 14 6301 33286 30 _ _ (2082577 / 100000) (104129 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108089088 :
    ThetaLowerSegment 1108089088 1108220160 (22161356364503 / 20000) (27704984384307 / 25000) := by
  exact
    packedTile65536 1108089088 1108220160 14 6317 33287 30 _ _ (2082589 / 100000) (65081 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108220160 :
    ThetaLowerSegment 1108220160 1108351232 (27704984384307 / 25000)
      (110833097492947 / 100000) := by
  exact
    packedTile65536 1108220160 1108351232 14 6319 33289 30 _ _ (2082601 / 100000) (520651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108351232 :
    ThetaLowerSegment 1108351232 1108482304 (110833097492947 / 100000)
      (110846384557507 / 100000) := by
  exact
    packedTile65536 1108351232 1108482304 14 6380 33291 30 _ _ (520653 / 25000) (416523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108482304 :
    ThetaLowerSegment 1108482304 1108613376 (110846384557507 / 100000)
      (110859390544387 / 100000) := by
  exact
    packedTile65536 1108482304 1108613376 14 6245 33293 30 _ _ (65082 / 3125) (2082627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108613376 :
    ThetaLowerSegment 1108613376 1108744448 (110859390544387 / 100000)
      (110872488242191 / 100000) := by
  exact
    packedTile65536 1108613376 1108744448 14 6289 33295 30 _ _ (520659 / 25000) (2082639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108744448 :
    ThetaLowerSegment 1108744448 1108875520 (110872488242191 / 100000)
      (110885608924591 / 100000) := by
  exact
    packedTile65536 1108744448 1108875520 14 6300 33297 30 _ _ (260331 / 12500) (2082651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108875520 :
    ThetaLowerSegment 1108875520 1109006592 (110885608924591 / 100000)
      (110898608888311 / 100000) := by
  exact
    packedTile65536 1108875520 1109006592 14 6242 33299 30 _ _ (104133 / 5000) (2082663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109006592 :
    ThetaLowerSegment 1109006592 1109137664 (110898608888311 / 100000)
      (110911735969927 / 100000) := by
  exact
    packedTile65536 1109006592 1109137664 14 6303 33301 30 _ _ (130167 / 6250) (83307 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109137664 :
    ThetaLowerSegment 1109137664 1109268736 (110911735969927 / 100000)
      (110925027652833 / 100000) := by
  exact
    packedTile65536 1109137664 1109268736 14 6382 33303 30 _ _ (2082683 / 100000) (1041343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109268736 :
    ThetaLowerSegment 1109268736 1109399808 (110925027652833 / 100000)
      (55469069108929 / 50000) := by
  exact
    packedTile65536 1109268736 1109399808 14 6295 33305 30 _ _ (416539 / 20000) (1041349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109399808 :
    ThetaLowerSegment 1109399808 1109530880 (55469069108929 / 50000) (27737795032273 / 25000) := by
  exact
    packedTile65536 1109399808 1109530880 14 6262 33307 30 _ _ (2082707 / 100000) (208271 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109530880 :
    ThetaLowerSegment 1109530880 1109661952 (27737795032273 / 25000) (55482115223173 / 50000) := by
  exact
    packedTile65536 1109530880 1109661952 14 6266 33309 30 _ _ (2082719 / 100000) (1041361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109661952 :
    ThetaLowerSegment 1109661952 1109793024 (55482115223173 / 50000)
      (110977366230763 / 100000) := by
  exact
    packedTile65536 1109661952 1109793024 14 6307 33311 30 _ _ (2082731 / 100000) (1041367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109793024 :
    ThetaLowerSegment 1109793024 1109924096 (110977366230763 / 100000)
      (22198100000363 / 20000) := by
  exact
    packedTile65536 1109793024 1109924096 14 6306 33313 30 _ _ (1041371 / 50000) (416549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1109924096 :
    ThetaLowerSegment 1109924096 1110055168 (22198100000363 / 20000)
      (111003702579421 / 100000) := by
  exact
    packedTile65536 1109924096 1110055168 14 6339 33315 30 _ _ (1041377 / 50000) (2082757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110055168 :
    ThetaLowerSegment 1110055168 1110186240 (111003702579421 / 100000)
      (22203345639597 / 20000) := by
  exact
    packedTile65536 1110055168 1110186240 14 6254 33317 30 _ _ (1041383 / 50000) (2082769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110186240 :
    ThetaLowerSegment 1110186240 1110317312 (22203345639597 / 20000)
      (111029680994367 / 100000) := by
  exact
    packedTile65536 1110186240 1110317312 14 6219 33319 30 _ _ (1041389 / 50000) (2082781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110317312 :
    ThetaLowerSegment 1110317312 1110448384 (111029680994367 / 100000)
      (111042848392747 / 100000) := by
  exact
    packedTile65536 1110317312 1110448384 14 6322 33321 30 _ _ (208279 / 10000) (2082793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110448384 :
    ThetaLowerSegment 1110448384 1110579456 (111042848392747 / 100000)
      (22211180677883 / 20000) := by
  exact
    packedTile65536 1110448384 1110579456 14 6268 33323 30 _ _ (2082801 / 100000) (520701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110579456 :
    ThetaLowerSegment 1110579456 1110710528 (22211180677883 / 20000)
      (111068904308161 / 100000) := by
  exact
    packedTile65536 1110579456 1110710528 14 6242 33325 30 _ _ (2082813 / 100000) (65088 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110710528 :
    ThetaLowerSegment 1110710528 1110841600 (111068904308161 / 100000)
      (55541022425543 / 50000) := by
  exact
    packedTile65536 1110710528 1110841600 14 6309 33327 30 _ _ (83313 / 4000) (520707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110841600 :
    ThetaLowerSegment 1110841600 1110972672 (55541022425543 / 50000) (27773801053813 / 25000) := by
  exact
    packedTile65536 1110841600 1110972672 14 6318 33329 30 _ _ (2082837 / 100000) (52071 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110972672 :
    ThetaLowerSegment 1110972672 1111103744 (27773801053813 / 25000) (55554115176449 / 50000) := by
  exact
    packedTile65536 1110972672 1111103744 14 6254 33331 30 _ _ (2082849 / 100000) (520713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111103744 :
    ThetaLowerSegment 1111103744 1111234816 (55554115176449 / 50000) (55560675144019 / 50000) := by
  exact
    packedTile65536 1111103744 1111234816 14 6299 33333 30 _ _ (104143 / 5000) (2082863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111234816 :
    ThetaLowerSegment 1111234816 1111365888 (55560675144019 / 50000) (55567277848259 / 50000) := by
  exact
    packedTile65536 1111234816 1111365888 14 6340 33335 30 _ _ (260359 / 12500) (16663 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111365888 :
    ThetaLowerSegment 1111365888 1111496960 (55567277848259 / 50000) (55573828518439 / 50000) := by
  exact
    packedTile65536 1111365888 1111496960 14 6290 33337 30 _ _ (520721 / 25000) (2082887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111496960 :
    ThetaLowerSegment 1111496960 1111628032 (55573828518439 / 50000) (55580356314503 / 50000) := by
  exact
    packedTile65536 1111496960 1111628032 14 6268 33339 30 _ _ (130181 / 6250) (2082899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111628032 :
    ThetaLowerSegment 1111628032 1111759104 (55580356314503 / 50000) (55586898728531 / 50000) := by
  exact
    packedTile65536 1111628032 1111759104 14 6282 33341 30 _ _ (520727 / 25000) (2082911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111759104 :
    ThetaLowerSegment 1111759104 1111890176 (55586898728531 / 50000) (55593439094191 / 50000) := by
  exact
    packedTile65536 1111759104 1111890176 14 6280 33343 30 _ _ (2082919 / 100000) (1041461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1111890176 :
    ThetaLowerSegment 1111890176 1112021248 (55593439094191 / 50000) (13900013100029 / 12500) := by
  exact
    packedTile65536 1111890176 1112021248 14 6350 33345 30 _ _ (2082931 / 100000) (1041467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112021248 :
    ThetaLowerSegment 1112021248 1112152320 (13900013100029 / 12500) (222426354701 / 200) := by
  exact
    packedTile65536 1112021248 1112152320 14 6276 33346 30 _ _ (2082943 / 100000) (1041473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112152320 :
    ThetaLowerSegment 1112152320 1112283392 (222426354701 / 200) (22245251244989 / 20000) := by
  exact
    packedTile65536 1112152320 1112283392 14 6279 33348 30 _ _ (416591 / 20000) (1041479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112283392 :
    ThetaLowerSegment 1112283392 1112414464 (22245251244989 / 20000) (6952469123627 / 6250) := by
  exact
    packedTile65536 1112283392 1112414464 14 6361 33350 30 _ _ (2082967 / 100000) (208297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112414464 :
    ThetaLowerSegment 1112414464 1112545536 (6952469123627 / 6250) (11125250584373 / 10000) := by
  exact
    packedTile65536 1112414464 1112545536 14 6241 33352 30 _ _ (1041489 / 50000) (2082981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112545536 :
    ThetaLowerSegment 1112545536 1112676608 (11125250584373 / 10000) (2781641185691 / 2500) := by
  exact
    packedTile65536 1112545536 1112676608 14 6309 33354 30 _ _ (208299 / 10000) (2082993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112676608 :
    ThetaLowerSegment 1112676608 1112807680 (2781641185691 / 2500) (11127855162503 / 10000) := by
  exact
    packedTile65536 1112676608 1112807680 14 6195 33356 30 _ _ (1041501 / 50000) (416601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112807680 :
    ThetaLowerSegment 1112807680 1112938752 (11127855162503 / 10000) (11129165378309 / 10000) := by
  exact
    packedTile65536 1112807680 1112938752 14 6290 33358 30 _ _ (1041507 / 50000) (2083017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112938752 :
    ThetaLowerSegment 1112938752 1113069824 (11129165378309 / 10000) (11130461019859 / 10000) := by
  exact
    packedTile65536 1112938752 1113069824 14 6220 33360 30 _ _ (83321 / 4000) (520757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113069824 :
    ThetaLowerSegment 1113069824 1113200896 (11130461019859 / 10000) (11131760834947 / 10000) := by
  exact
    packedTile65536 1113069824 1113200896 14 6240 33362 30 _ _ (2083037 / 100000) (13019 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113200896 :
    ThetaLowerSegment 1113200896 1113331968 (11131760834947 / 10000) (55665382443477 / 50000) := by
  exact
    packedTile65536 1113200896 1113331968 14 6316 33364 30 _ _ (2083049 / 100000) (520763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113331968 :
    ThetaLowerSegment 1113331968 1113463040 (55665382443477 / 50000) (55671973248481 / 50000) := by
  exact
    packedTile65536 1113331968 1113463040 14 6328 33366 30 _ _ (2083061 / 100000) (260383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113463040 :
    ThetaLowerSegment 1113463040 1113594112 (55671973248481 / 50000) (27839278921117 / 25000) := by
  exact
    packedTile65536 1113463040 1113594112 14 6322 33368 30 _ _ (2083073 / 100000) (520769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113594112 :
    ThetaLowerSegment 1113594112 1113725184 (27839278921117 / 25000) (13921279628823 / 12500) := by
  exact
    packedTile65536 1113594112 1113725184 14 6299 33370 30 _ _ (520771 / 25000) (2083087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113725184 :
    ThetaLowerSegment 1113725184 1113856256 (13921279628823 / 12500) (3480729170473 / 3125) := by
  exact
    packedTile65536 1113725184 1113856256 14 6287 33372 30 _ _ (260387 / 12500) (2083099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113856256 :
    ThetaLowerSegment 1113856256 1113987328 (3480729170473 / 3125) (27849161649591 / 25000) := by
  exact
    packedTile65536 1113856256 1113987328 14 6391 33374 30 _ _ (520777 / 25000) (2083111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1113987328 :
    ThetaLowerSegment 1113987328 1114118400 (27849161649591 / 25000) (27852408712891 / 25000) := by
  exact
    packedTile65536 1113987328 1114118400 14 6235 33376 30 _ _ (26039 / 1250) (2083123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114118400 :
    ThetaLowerSegment 1114118400 1114249472 (27852408712891 / 25000) (27855679228561 / 25000) := by
  exact
    packedTile65536 1114118400 1114249472 14 6280 33378 30 _ _ (2083131 / 100000) (1041567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114249472 :
    ThetaLowerSegment 1114249472 1114380544 (27855679228561 / 25000) (6964743169411 / 6250) := by
  exact
    packedTile65536 1114249472 1114380544 14 6324 33380 30 _ _ (2083143 / 100000) (1041573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114380544 :
    ThetaLowerSegment 1114380544 1114511616 (6964743169411 / 6250) (111449079164881 / 100000) := by
  exact
    packedTile65536 1114380544 1114511616 14 6331 33382 30 _ _ (416631 / 20000) (1041579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114511616 :
    ThetaLowerSegment 1114511616 1114642688 (111449079164881 / 100000) (5573107760207 / 5000) := by
  exact
    packedTile65536 1114511616 1114642688 14 6277 33384 30 _ _ (2083167 / 100000) (208317 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114642688 :
    ThetaLowerSegment 1114642688 1114773760 (5573107760207 / 5000) (55737553160883 / 50000) := by
  exact
    packedTile65536 1114642688 1114773760 14 6217 33386 30 _ _ (1041589 / 50000) (2083181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114773760 :
    ThetaLowerSegment 1114773760 1114904832 (55737553160883 / 50000) (55744052713683 / 50000) := by
  exact
    packedTile65536 1114773760 1114904832 14 6240 33388 30 _ _ (208319 / 10000) (2083193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114904832 :
    ThetaLowerSegment 1114904832 1115035904 (55744052713683 / 50000) (55750666880033 / 50000) := by
  exact
    packedTile65536 1114904832 1115035904 14 6350 33390 30 _ _ (1041601 / 50000) (416641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115035904 :
    ThetaLowerSegment 1115035904 1115166976 (55750666880033 / 50000) (55757314415907 / 50000) := by
  exact
    packedTile65536 1115035904 1115166976 14 6382 33392 30 _ _ (1041607 / 50000) (2083217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115166976 :
    ThetaLowerSegment 1115166976 1115298048 (55757314415907 / 50000) (27881897664441 / 25000) := by
  exact
    packedTile65536 1115166976 1115298048 14 6222 33394 30 _ _ (83329 / 4000) (520807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115298048 :
    ThetaLowerSegment 1115298048 1115429120 (27881897664441 / 25000) (5577034502601 / 5000) := by
  exact
    packedTile65536 1115298048 1115429120 14 6288 33396 30 _ _ (2083237 / 100000) (52081 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115429120 :
    ThetaLowerSegment 1115429120 1115560192 (5577034502601 / 5000) (111553829103463 / 100000) := by
  exact
    packedTile65536 1115429120 1115560192 14 6307 33398 30 _ _ (2083249 / 100000) (520813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115560192 :
    ThetaLowerSegment 1115560192 1115691264 (111553829103463 / 100000) (5578347369899 / 5000) := by
  exact
    packedTile65536 1115560192 1115691264 14 6297 33400 30 _ _ (2083261 / 100000) (65102 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115691264 :
    ThetaLowerSegment 1115691264 1115822336 (5578347369899 / 5000) (111579911605859 / 100000) := by
  exact
    packedTile65536 1115691264 1115822336 14 6223 33401 30 _ _ (2083273 / 100000) (520819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115822336 :
    ThetaLowerSegment 1115822336 1115953408 (111579911605859 / 100000)
      (111592905048167 / 100000) := by
  exact
    packedTile65536 1115822336 1115953408 14 6237 33403 30 _ _ (520821 / 25000) (2083287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1115953408 :
    ThetaLowerSegment 1115953408 1116084480 (111592905048167 / 100000)
      (111605969397383 / 100000) := by
  exact
    packedTile65536 1115953408 1116084480 14 6271 33405 30 _ _ (65103 / 3125) (2083299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116084480 :
    ThetaLowerSegment 1116084480 1116215552 (111605969397383 / 100000)
      (111619131737327 / 100000) := by
  exact
    packedTile65536 1116084480 1116215552 14 6318 33407 30 _ _ (520827 / 25000) (2083311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116215552 :
    ThetaLowerSegment 1116215552 1116346624 (111619131737327 / 100000)
      (111632256647027 / 100000) := by
  exact
    packedTile65536 1116215552 1116346624 14 6300 33409 30 _ _ (2083319 / 100000) (1041661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116346624 :
    ThetaLowerSegment 1116346624 1116477696 (111632256647027 / 100000)
      (27911332387263 / 25000) := by
  exact
    packedTile65536 1116346624 1116477696 14 6275 33411 30 _ _ (2083331 / 100000) (1041667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116477696 :
    ThetaLowerSegment 1116477696 1116608768 (27911332387263 / 25000) (55829271055179 / 50000) := by
  exact
    packedTile65536 1116477696 1116608768 14 6342 33413 30 _ _ (2083343 / 100000) (1041673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116608768 :
    ThetaLowerSegment 1116608768 1116739840 (55829271055179 / 50000) (27917932436877 / 25000) := by
  exact
    packedTile65536 1116608768 1116739840 14 6330 33415 30 _ _ (416671 / 20000) (1041679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116739840 :
    ThetaLowerSegment 1116739840 1116870912 (27917932436877 / 25000) (55842395184481 / 50000) := by
  exact
    packedTile65536 1116739840 1116870912 14 6269 33417 30 _ _ (1041683 / 50000) (2083369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1116870912 :
    ThetaLowerSegment 1116870912 1117001984 (55842395184481 / 50000) (13962201695069 / 12500) := by
  exact
    packedTile65536 1116870912 1117001984 14 6155 33419 30 _ _ (1041689 / 50000) (2083381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117001984 :
    ThetaLowerSegment 1117001984 1117133056 (13962201695069 / 12500) (27927723272103 / 25000) := by
  exact
    packedTile65536 1117001984 1117133056 14 6374 33421 30 _ _ (208339 / 10000) (2083393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117133056 :
    ThetaLowerSegment 1117133056 1117264128 (27927723272103 / 25000) (11172399560359 / 10000) := by
  exact
    packedTile65536 1117133056 1117264128 14 6289 33423 30 _ _ (1041701 / 50000) (416681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117264128 :
    ThetaLowerSegment 1117264128 1117395200 (11172399560359 / 10000) (22347417970859 / 20000) := by
  exact
    packedTile65536 1117264128 1117395200 14 6285 33425 30 _ _ (2083413 / 100000) (260427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117395200 :
    ThetaLowerSegment 1117395200 1117526272 (22347417970859 / 20000) (5587508375651 / 5000) := by
  exact
    packedTile65536 1117395200 1117526272 14 6277 33427 30 _ _ (83337 / 4000) (520857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117526272 :
    ThetaLowerSegment 1117526272 1117657344 (5587508375651 / 5000) (22352614881047 / 20000) := by
  exact
    packedTile65536 1117526272 1117657344 14 6195 33429 30 _ _ (2083437 / 100000) (26043 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117657344 :
    ThetaLowerSegment 1117657344 1117788416 (22352614881047 / 20000)
      (111776154298057 / 100000) := by
  exact
    packedTile65536 1117657344 1117788416 14 6278 33431 30 _ _ (2083449 / 100000) (520863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117788416 :
    ThetaLowerSegment 1117788416 1117919488 (111776154298057 / 100000)
      (111789255094537 / 100000) := by
  exact
    packedTile65536 1117788416 1117919488 14 6288 33433 30 _ _ (104173 / 5000) (2083463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1117919488 :
    ThetaLowerSegment 1117919488 1118050560 (111789255094537 / 100000)
      (111802393468969 / 100000) := by
  exact
    packedTile65536 1117919488 1118050560 14 6306 33435 30 _ _ (130217 / 6250) (83339 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118050560 :
    ThetaLowerSegment 1118050560 1118181632 (111802393468969 / 100000)
      (111815375657773 / 100000) := by
  exact
    packedTile65536 1118050560 1118181632 14 6231 33437 30 _ _ (520871 / 25000) (2083487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118181632 :
    ThetaLowerSegment 1118181632 1118312704 (111815375657773 / 100000)
      (111828526678213 / 100000) := by
  exact
    packedTile65536 1118181632 1118312704 14 6312 33439 30 _ _ (416699 / 20000) (1041749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118312704 :
    ThetaLowerSegment 1118312704 1118443776 (111828526678213 / 100000)
      (111841806951831 / 100000) := by
  exact
    packedTile65536 1118312704 1118443776 14 6374 33441 30 _ _ (2083507 / 100000) (208351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118443776 :
    ThetaLowerSegment 1118443776 1118574848 (111841806951831 / 100000)
      (111854783108163 / 100000) := by
  exact
    packedTile65536 1118443776 1118574848 14 6228 33443 30 _ _ (2083519 / 100000) (1041761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118574848 :
    ThetaLowerSegment 1118574848 1118705920 (111854783108163 / 100000)
      (111867980193517 / 100000) := by
  exact
    packedTile65536 1118574848 1118705920 14 6334 33445 30 _ _ (2083531 / 100000) (1041767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118705920 :
    ThetaLowerSegment 1118705920 1118836992 (111867980193517 / 100000)
      (111881194016881 / 100000) := by
  exact
    packedTile65536 1118705920 1118836992 14 6342 33447 30 _ _ (1041771 / 50000) (416709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118836992 :
    ThetaLowerSegment 1118836992 1118968064 (111881194016881 / 100000)
      (111894226647151 / 100000) := by
  exact
    packedTile65536 1118836992 1118968064 14 6255 33449 30 _ _ (1041777 / 50000) (2083557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118968064 :
    ThetaLowerSegment 1118968064 1119099136 (111894226647151 / 100000)
      (111907384366441 / 100000) := by
  exact
    packedTile65536 1118968064 1119099136 14 6315 33450 30 _ _ (1041783 / 50000) (2083569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119099136 :
    ThetaLowerSegment 1119099136 1119230208 (111907384366441 / 100000)
      (27980181377493 / 25000) := by
  exact
    packedTile65536 1119099136 1119230208 14 6403 33452 30 _ _ (2083577 / 100000) (104179 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119230208 :
    ThetaLowerSegment 1119230208 1119361280 (27980181377493 / 25000) (22386752505269 / 20000) := by
  exact
    packedTile65536 1119230208 1119361280 14 6257 33454 30 _ _ (2083589 / 100000) (260449 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119361280 :
    ThetaLowerSegment 1119361280 1119492352 (22386752505269 / 20000)
      (111946797534201 / 100000) := by
  exact
    packedTile65536 1119361280 1119492352 14 6256 33456 30 _ _ (2083601 / 100000) (520901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119492352 :
    ThetaLowerSegment 1119492352 1119623424 (111946797534201 / 100000)
      (111959828449903 / 100000) := by
  exact
    packedTile65536 1119492352 1119623424 14 6254 33458 30 _ _ (2083613 / 100000) (65113 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119623424 :
    ThetaLowerSegment 1119623424 1119754496 (111959828449903 / 100000)
      (111973011538951 / 100000) := by
  exact
    packedTile65536 1119623424 1119754496 14 6327 33460 30 _ _ (260453 / 12500) (2083627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119754496 :
    ThetaLowerSegment 1119754496 1119885568 (111973011538951 / 100000)
      (111986130111207 / 100000) := by
  exact
    packedTile65536 1119754496 1119885568 14 6296 33462 30 _ _ (520909 / 25000) (2083639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1119885568 :
    ThetaLowerSegment 1119885568 1120016640 (111986130111207 / 100000)
      (111999382112487 / 100000) := by
  exact
    packedTile65536 1119885568 1120016640 14 6360 33464 30 _ _ (65114 / 3125) (2083651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120016640 :
    ThetaLowerSegment 1120016640 1120147712 (111999382112487 / 100000) (2240248391337 / 2000) := by
  exact
    packedTile65536 1120016640 1120147712 14 6257 33466 30 _ _ (2083659 / 100000) (1041831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120147712 :
    ThetaLowerSegment 1120147712 1120278784 (2240248391337 / 2000) (28006379380689 / 25000) := by
  exact
    packedTile65536 1120147712 1120278784 14 6286 33468 30 _ _ (2083671 / 100000) (1041837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120278784 :
    ThetaLowerSegment 1120278784 1120409856 (28006379380689 / 25000) (11203859888463 / 10000) := by
  exact
    packedTile65536 1120278784 1120409856 14 6278 33470 30 _ _ (2083683 / 100000) (1041843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120409856 :
    ThetaLowerSegment 1120409856 1120540928 (11203859888463 / 10000) (22410336481107 / 20000) := by
  exact
    packedTile65536 1120409856 1120540928 14 6279 33472 30 _ _ (416739 / 20000) (1041849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120540928 :
    ThetaLowerSegment 1120540928 1120672000 (22410336481107 / 20000) (22412959866961 / 20000) := by
  exact
    packedTile65536 1120540928 1120672000 14 6295 33474 30 _ _ (1041853 / 50000) (2083709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120672000 :
    ThetaLowerSegment 1120672000 1120803072 (22412959866961 / 20000)
      (112077776730509 / 100000) := by
  exact
    packedTile65536 1120672000 1120803072 14 6228 33476 30 _ _ (1041859 / 50000) (2083721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120803072 :
    ThetaLowerSegment 1120803072 1120934144 (112077776730509 / 100000)
      (112091023002119 / 100000) := by
  exact
    packedTile65536 1120803072 1120934144 14 6357 33478 30 _ _ (208373 / 10000) (2083733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120934144 :
    ThetaLowerSegment 1120934144 1121065216 (112091023002119 / 100000)
      (112104096393153 / 100000) := by
  exact
    packedTile65536 1120934144 1121065216 14 6274 33480 30 _ _ (2083741 / 100000) (65117 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121065216 :
    ThetaLowerSegment 1121065216 1121196288 (112104096393153 / 100000)
      (22423446474413 / 20000) := by
  exact
    packedTile65536 1121065216 1121196288 14 6304 33482 30 _ _ (2083753 / 100000) (520939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121196288 :
    ThetaLowerSegment 1121196288 1121327360 (22423446474413 / 20000) (22426054514687 / 20000) := by
  exact
    packedTile65536 1121196288 1121327360 14 6258 33484 30 _ _ (416753 / 20000) (260471 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121327360 :
    ThetaLowerSegment 1121327360 1121458432 (22426054514687 / 20000) (22428742585727 / 20000) := by
  exact
    packedTile65536 1121327360 1121458432 14 6450 33486 30 _ _ (65118 / 3125) (2083779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121458432 :
    ThetaLowerSegment 1121458432 1121589504 (22428742585727 / 20000)
      (112156728268483 / 100000) := by
  exact
    packedTile65536 1121458432 1121589504 14 6246 33488 30 _ _ (520947 / 25000) (2083791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121589504 :
    ThetaLowerSegment 1121589504 1121720576 (112156728268483 / 100000)
      (112169693672083 / 100000) := by
  exact
    packedTile65536 1121589504 1121720576 14 6222 33490 30 _ _ (10419 / 500) (2083803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121720576 :
    ThetaLowerSegment 1121720576 1121851648 (112169693672083 / 100000) (5609137645781 / 5000) := by
  exact
    packedTile65536 1121720576 1121851648 14 6267 33492 30 _ _ (2083811 / 100000) (1041907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121851648 :
    ThetaLowerSegment 1121851648 1121982720 (5609137645781 / 5000) (11219602686813 / 10000) := by
  exact
    packedTile65536 1121851648 1121982720 14 6370 33494 30 _ _ (2083823 / 100000) (1041913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1121982720 :
    ThetaLowerSegment 1121982720 1122113792 (11219602686813 / 10000) (22441852260843 / 20000) := by
  exact
    packedTile65536 1121982720 1122113792 14 6351 33496 30 _ _ (416767 / 20000) (1041919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122113792 :
    ThetaLowerSegment 1122113792 1122244864 (22441852260843 / 20000)
      (112222439552643 / 100000) := by
  exact
    packedTile65536 1122113792 1122244864 14 6324 33497 30 _ _ (2083847 / 100000) (41677 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122244864 :
    ThetaLowerSegment 1122244864 1122375936 (112222439552643 / 100000)
      (112235553271037 / 100000) := by
  exact
    packedTile65536 1122244864 1122375936 14 6293 33499 30 _ _ (1041929 / 50000) (2083861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122375936 :
    ThetaLowerSegment 1122375936 1122507008 (112235553271037 / 100000)
      (112248560787577 / 100000) := by
  exact
    packedTile65536 1122375936 1122507008 14 6242 33501 30 _ _ (208387 / 10000) (2083873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122507008 :
    ThetaLowerSegment 1122507008 1122638080 (112248560787577 / 100000)
      (112261639231009 / 100000) := by
  exact
    packedTile65536 1122507008 1122638080 14 6276 33503 30 _ _ (1041941 / 50000) (416777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122638080 :
    ThetaLowerSegment 1122638080 1122769152 (112261639231009 / 100000)
      (28068676831003 / 25000) := by
  exact
    packedTile65536 1122638080 1122769152 14 6271 33505 30 _ _ (2083893 / 100000) (260487 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122769152 :
    ThetaLowerSegment 1122769152 1122900224 (28068676831003 / 25000)
      (112287725478547 / 100000) := by
  exact
    packedTile65536 1122769152 1122900224 14 6247 33507 30 _ _ (416781 / 20000) (520977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1122900224 :
    ThetaLowerSegment 1122900224 1123031296 (112287725478547 / 100000)
      (28075222395559 / 25000) := by
  exact
    packedTile65536 1122900224 1123031296 14 6317 33509 30 _ _ (2083917 / 100000) (26049 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123031296 :
    ThetaLowerSegment 1123031296 1123162368 (28075222395559 / 25000) (28078509270997 / 25000) := by
  exact
    packedTile65536 1123031296 1123162368 14 6309 33511 30 _ _ (260491 / 12500) (2083931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123162368 :
    ThetaLowerSegment 1123162368 1123293440 (28078509270997 / 25000) (14040881411161 / 12500) := by
  exact
    packedTile65536 1123162368 1123293440 14 6245 33513 30 _ _ (104197 / 5000) (2083943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123293440 :
    ThetaLowerSegment 1123293440 1123424512 (14040881411161 / 12500) (14042537371519 / 12500) := by
  exact
    packedTile65536 1123293440 1123424512 14 6357 33515 30 _ _ (130247 / 6250) (416791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123424512 :
    ThetaLowerSegment 1123424512 1123555584 (14042537371519 / 12500) (56176695213859 / 50000) := by
  exact
    packedTile65536 1123424512 1123555584 14 6282 33517 30 _ _ (2083963 / 100000) (1041983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123555584 :
    ThetaLowerSegment 1123555584 1123686656 (56176695213859 / 50000)
      (112366538225993 / 100000) := by
  exact
    packedTile65536 1123555584 1123686656 14 6309 33519 30 _ _ (83359 / 4000) (1041989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123686656 :
    ThetaLowerSegment 1123686656 1123817728 (112366538225993 / 100000)
      (22475902625811 / 20000) := by
  exact
    packedTile65536 1123686656 1123817728 14 6226 33521 30 _ _ (2083987 / 100000) (208399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123817728 :
    ThetaLowerSegment 1123817728 1123948800 (22475902625811 / 20000)
      (112392525612567 / 100000) := by
  exact
    packedTile65536 1123817728 1123948800 14 6244 33523 30 _ _ (1041999 / 50000) (2084001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1123948800 :
    ThetaLowerSegment 1123948800 1124079872 (112392525612567 / 100000)
      (112405656959577 / 100000) := by
  exact
    packedTile65536 1123948800 1124079872 14 6301 33525 30 _ _ (208401 / 10000) (2084013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124079872 :
    ThetaLowerSegment 1124079872 1124210944 (112405656959577 / 100000)
      (112418673760989 / 100000) := by
  exact
    packedTile65536 1124079872 1124210944 14 6246 33527 30 _ _ (1042011 / 50000) (83361 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124210944 :
    ThetaLowerSegment 1124210944 1124342016 (112418673760989 / 100000)
      (56215827601273 / 50000) := by
  exact
    packedTile65536 1124210944 1124342016 14 6229 33529 30 _ _ (2084033 / 100000) (521009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124342016 :
    ThetaLowerSegment 1124342016 1124473088 (56215827601273 / 50000) (28111161784769 / 25000) := by
  exact
    packedTile65536 1124342016 1124473088 14 6234 33531 30 _ _ (416809 / 20000) (130253 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124473088 :
    ThetaLowerSegment 1124473088 1124604160 (28111161784769 / 25000)
      (112457703756181 / 100000) := by
  exact
    packedTile65536 1124473088 1124604160 14 6265 33533 30 _ _ (2084057 / 100000) (104203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124604160 :
    ThetaLowerSegment 1124604160 1124735232 (112457703756181 / 100000)
      (112470743769657 / 100000) := by
  exact
    packedTile65536 1124604160 1124735232 14 6257 33535 30 _ _ (521017 / 25000) (2084071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124735232 :
    ThetaLowerSegment 1124735232 1124866304 (112470743769657 / 100000)
      (112483729672137 / 100000) := by
  exact
    packedTile65536 1124735232 1124866304 14 6231 33537 30 _ _ (26051 / 1250) (2084083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124866304 :
    ThetaLowerSegment 1124866304 1124997376 (112483729672137 / 100000)
      (112496811517621 / 100000) := by
  exact
    packedTile65536 1124866304 1124997376 14 6277 33539 30 _ _ (521023 / 25000) (416819 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124997376 :
    ThetaLowerSegment 1124997376 1125128448 (112496811517621 / 100000)
      (56254927959149 / 50000) := by
  exact
    packedTile65536 1124997376 1125128448 14 6259 33540 30 _ _ (2084103 / 100000) (1042053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125128448 :
    ThetaLowerSegment 1125128448 1125259520 (56254927959149 / 50000)
      (112522979590453 / 100000) := by
  exact
    packedTile65536 1125128448 1125259520 14 6297 33542 30 _ _ (416823 / 20000) (1042059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125259520 :
    ThetaLowerSegment 1125259520 1125390592 (112522979590453 / 100000)
      (112536167939781 / 100000) := by
  exact
    packedTile65536 1125259520 1125390592 14 6328 33544 30 _ _ (1042063 / 50000) (2084129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125390592 :
    ThetaLowerSegment 1125390592 1125521664 (112536167939781 / 100000)
      (112549229232627 / 100000) := by
  exact
    packedTile65536 1125390592 1125521664 14 6267 33546 30 _ _ (1042069 / 50000) (2084141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125521664 :
    ThetaLowerSegment 1125521664 1125652736 (112549229232627 / 100000)
      (112562303105577 / 100000) := by
  exact
    packedTile65536 1125521664 1125652736 14 6273 33548 30 _ _ (41683 / 2000) (2084153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125652736 :
    ThetaLowerSegment 1125652736 1125783808 (112562303105577 / 100000)
      (28143907828793 / 25000) := by
  exact
    packedTile65536 1125652736 1125783808 14 6395 33550 30 _ _ (2084161 / 100000) (521041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125783808 :
    ThetaLowerSegment 1125783808 1125914880 (28143907828793 / 25000) (28147192485441 / 25000) := by
  exact
    packedTile65536 1125783808 1125914880 14 6304 33552 30 _ _ (2084173 / 100000) (130261 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1125914880 :
    ThetaLowerSegment 1125914880 1126045952 (28147192485441 / 25000) (3518807300417 / 3125) := by
  exact
    packedTile65536 1125914880 1126045952 14 6268 33554 30 _ _ (416837 / 20000) (521047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126045952 :
    ThetaLowerSegment 1126045952 1126177024 (3518807300417 / 3125) (28153744659379 / 25000) := by
  exact
    packedTile65536 1126045952 1126177024 14 6307 33556 30 _ _ (521049 / 25000) (2084199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126177024 :
    ThetaLowerSegment 1126177024 1126308096 (28153744659379 / 25000) (28157027808031 / 25000) := by
  exact
    packedTile65536 1126177024 1126308096 14 6301 33558 30 _ _ (130263 / 6250) (2084211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126308096 :
    ThetaLowerSegment 1126308096 1126439168 (28157027808031 / 25000) (7040084778139 / 6250) := by
  exact
    packedTile65536 1126308096 1126439168 14 6355 33560 30 _ _ (104211 / 5000) (2084223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126439168 :
    ThetaLowerSegment 1126439168 1126570240 (7040084778139 / 6250) (11265449961091 / 10000) := by
  exact
    packedTile65536 1126439168 1126570240 14 6306 33562 30 _ _ (2084231 / 100000) (1042117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126570240 :
    ThetaLowerSegment 1126570240 1126701312 (11265449961091 / 10000) (56333819339391 / 50000) := by
  exact
    packedTile65536 1126570240 1126701312 14 6304 33564 30 _ _ (2084243 / 100000) (1042123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126701312 :
    ThetaLowerSegment 1126701312 1126832384 (56333819339391 / 50000)
      (112680700704867 / 100000) := by
  exact
    packedTile65536 1126701312 1126832384 14 6267 33566 30 _ _ (416851 / 20000) (1042129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126832384 :
    ThetaLowerSegment 1126832384 1126963456 (112680700704867 / 100000)
      (22538765482427 / 20000) := by
  exact
    packedTile65536 1126832384 1126963456 14 6298 33568 30 _ _ (1042133 / 50000) (2084269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126963456 :
    ThetaLowerSegment 1126963456 1127094528 (22538765482427 / 20000)
      (112706752020013 / 100000) := by
  exact
    packedTile65536 1126963456 1127094528 14 6201 33570 30 _ _ (1042139 / 50000) (2084281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127094528 :
    ThetaLowerSegment 1127094528 1127225600 (112706752020013 / 100000)
      (112719849692089 / 100000) := by
  exact
    packedTile65536 1127094528 1127225600 14 6284 33572 30 _ _ (2084289 / 100000) (521073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127225600 :
    ThetaLowerSegment 1127225600 1127356672 (112719849692089 / 100000)
      (28183234254517 / 25000) := by
  exact
    packedTile65536 1127225600 1127356672 14 6279 33574 30 _ _ (2084301 / 100000) (130269 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127356672 :
    ThetaLowerSegment 1127356672 1127487744 (28183234254517 / 25000) (56372952806777 / 50000) := by
  exact
    packedTile65536 1127356672 1127487744 14 6222 33576 30 _ _ (2084313 / 100000) (521079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127487744 :
    ThetaLowerSegment 1127487744 1127618816 (56372952806777 / 50000) (56379497584137 / 50000) := by
  exact
    packedTile65536 1127487744 1127618816 14 6280 33578 30 _ _ (521081 / 25000) (2084327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127618816 :
    ThetaLowerSegment 1127618816 1127749888 (56379497584137 / 50000) (56386016344977 / 50000) := by
  exact
    packedTile65536 1127618816 1127749888 14 6255 33580 30 _ _ (130271 / 6250) (2084339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127749888 :
    ThetaLowerSegment 1127749888 1127880960 (56386016344977 / 50000) (56392489287691 / 50000) := by
  exact
    packedTile65536 1127749888 1127880960 14 6211 33581 30 _ _ (521087 / 25000) (2084351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1127880960 :
    ThetaLowerSegment 1127880960 1128012032 (56392489287691 / 50000) (5639920300803 / 5000) := by
  exact
    packedTile65536 1127880960 1128012032 14 6442 33583 30 _ _ (2084359 / 100000) (1042181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128012032 :
    ThetaLowerSegment 1128012032 1128143104 (5639920300803 / 5000) (112811489612827 / 100000) := by
  exact
    packedTile65536 1128012032 1128143104 14 6277 33585 30 _ _ (2084371 / 100000) (1042187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128143104 :
    ThetaLowerSegment 1128143104 1128274176 (112811489612827 / 100000)
      (112824614966281 / 100000) := by
  exact
    packedTile65536 1128143104 1128274176 14 6297 33587 30 _ _ (1042191 / 50000) (416877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128274176 :
    ThetaLowerSegment 1128274176 1128405248 (112824614966281 / 100000)
      (22567533071423 / 20000) := by
  exact
    packedTile65536 1128274176 1128405248 14 6261 33589 30 _ _ (1042197 / 50000) (2084397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128405248 :
    ThetaLowerSegment 1128405248 1128536320 (22567533071423 / 20000)
      (112850884659967 / 100000) := by
  exact
    packedTile65536 1128405248 1128536320 14 6342 33591 30 _ _ (1042203 / 50000) (2084409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128536320 :
    ThetaLowerSegment 1128536320 1128667392 (112850884659967 / 100000)
      (112864037331237 / 100000) := by
  exact
    packedTile65536 1128536320 1128667392 14 6310 33593 30 _ _ (2084417 / 100000) (104221 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128667392 :
    ThetaLowerSegment 1128667392 1128798464 (112864037331237 / 100000)
      (112877169233937 / 100000) := by
  exact
    packedTile65536 1128667392 1128798464 14 6300 33595 30 _ _ (2084429 / 100000) (130277 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128798464 :
    ThetaLowerSegment 1128798464 1128929536 (112877169233937 / 100000)
      (112890344979177 / 100000) := by
  exact
    packedTile65536 1128798464 1128929536 14 6321 33597 30 _ _ (52111 / 2500) (2084443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1128929536 :
    ThetaLowerSegment 1128929536 1129060608 (112890344979177 / 100000)
      (112903468688969 / 100000) := by
  exact
    packedTile65536 1128929536 1129060608 14 6296 33599 30 _ _ (521113 / 25000) (416891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129060608 :
    ThetaLowerSegment 1129060608 1129191680 (112903468688969 / 100000)
      (112916436139513 / 100000) := by
  exact
    packedTile65536 1129060608 1129191680 14 6221 33601 30 _ _ (130279 / 6250) (2084467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129191680 :
    ThetaLowerSegment 1129191680 1129322752 (112916436139513 / 100000)
      (28232407195447 / 25000) := by
  exact
    packedTile65536 1129191680 1129322752 14 6329 33603 30 _ _ (83379 / 4000) (1042239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129322752 :
    ThetaLowerSegment 1129322752 1129339136 (28232407195447 / 25000) (56465625256337 / 50000) := by
  exact
    packedTile65536 1129322752 1129339136 11 778 33605 30 _ _ (2084487 / 100000) (208449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129339136 :
    ThetaLowerSegment 1129339136 1129341184 (56465625256337 / 50000) (56465729480737 / 50000) := by
  exact
    packedTile65536 1129339136 1129341184 8 100 33605 30 _ _ (260561 / 12500) (2084491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1097341184_1129341184 :
    ThetaLowerSegment 1097341184 1129341184 (109731766317517 / 100000)
      (56465729480737 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1097341184 cell1097472256)
                  (ThetaLowerSegment.join cell1097603328 cell1097734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1097865472 cell1097996544)
                  (ThetaLowerSegment.join cell1098127616 cell1098258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1098389760 cell1098520832)
                  (ThetaLowerSegment.join cell1098651904 cell1098782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1098914048 cell1099045120)
                  (ThetaLowerSegment.join cell1099176192 cell1099307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1099438336 cell1099569408)
                  (ThetaLowerSegment.join cell1099700480 cell1099831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1099962624 cell1100093696)
                  (ThetaLowerSegment.join cell1100224768 cell1100355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1100486912 cell1100617984)
                  (ThetaLowerSegment.join cell1100749056 cell1100880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1101011200 cell1101142272)
                  (ThetaLowerSegment.join cell1101273344 cell1101404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1101535488 cell1101666560)
                  (ThetaLowerSegment.join cell1101797632 cell1101928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1102059776 cell1102190848)
                  (ThetaLowerSegment.join cell1102321920 cell1102452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1102584064 cell1102715136)
                  (ThetaLowerSegment.join cell1102846208 cell1102977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1103108352 cell1103239424)
                  (ThetaLowerSegment.join cell1103370496 cell1103501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1103632640 cell1103763712)
                  (ThetaLowerSegment.join cell1103894784 cell1104025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1104156928 cell1104288000)
                  (ThetaLowerSegment.join cell1104419072 cell1104550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1104681216 cell1104812288)
                  (ThetaLowerSegment.join cell1104943360 cell1105074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1105205504 cell1105336576)
                  (ThetaLowerSegment.join cell1105467648 cell1105598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1105729792 cell1105860864)
                  (ThetaLowerSegment.join cell1105991936 cell1106123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1106254080 cell1106385152)
                  (ThetaLowerSegment.join cell1106516224 cell1106647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1106778368 cell1106909440)
                  (ThetaLowerSegment.join cell1107040512 cell1107171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1107302656 cell1107433728)
                  (ThetaLowerSegment.join cell1107564800 cell1107695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1107826944 cell1107958016)
                  (ThetaLowerSegment.join cell1108089088 cell1108220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1108351232 cell1108482304)
                  (ThetaLowerSegment.join cell1108613376 cell1108744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1108875520 cell1109006592)
                  (ThetaLowerSegment.join cell1109137664 cell1109268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1109399808 cell1109530880)
                  (ThetaLowerSegment.join cell1109661952 cell1109793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1109924096 cell1110055168)
                  (ThetaLowerSegment.join cell1110186240 cell1110317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1110448384 cell1110579456)
                  (ThetaLowerSegment.join cell1110710528 cell1110841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1110972672 cell1111103744)
                  (ThetaLowerSegment.join cell1111234816 cell1111365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1111496960 cell1111628032)
                  (ThetaLowerSegment.join cell1111759104 cell1111890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1112021248 cell1112152320)
                  (ThetaLowerSegment.join cell1112283392 cell1112414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1112545536 cell1112676608)
                  (ThetaLowerSegment.join cell1112807680 cell1112938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1113069824 cell1113200896)
                  (ThetaLowerSegment.join cell1113331968 cell1113463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1113594112 cell1113725184)
                  (ThetaLowerSegment.join cell1113856256 cell1113987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1114118400 cell1114249472)
                  (ThetaLowerSegment.join cell1114380544 cell1114511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1114642688 cell1114773760)
                  (ThetaLowerSegment.join cell1114904832 cell1115035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1115166976 cell1115298048)
                  (ThetaLowerSegment.join cell1115429120 cell1115560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1115691264 cell1115822336)
                  (ThetaLowerSegment.join cell1115953408 cell1116084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1116215552 cell1116346624)
                  (ThetaLowerSegment.join cell1116477696 cell1116608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1116739840 cell1116870912)
                  (ThetaLowerSegment.join cell1117001984 cell1117133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1117264128 cell1117395200)
                  (ThetaLowerSegment.join cell1117526272 cell1117657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1117788416 cell1117919488)
                  (ThetaLowerSegment.join cell1118050560 cell1118181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1118312704 cell1118443776)
                  (ThetaLowerSegment.join cell1118574848 cell1118705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1118836992 cell1118968064)
                  (ThetaLowerSegment.join cell1119099136 cell1119230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1119361280 cell1119492352)
                  (ThetaLowerSegment.join cell1119623424 cell1119754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1119885568 cell1120016640)
                  (ThetaLowerSegment.join cell1120147712 cell1120278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1120409856 cell1120540928)
                  (ThetaLowerSegment.join cell1120672000 cell1120803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1120934144 cell1121065216)
                  (ThetaLowerSegment.join cell1121196288 cell1121327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1121458432 cell1121589504)
                  (ThetaLowerSegment.join cell1121720576 cell1121851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1121982720 cell1122113792)
                  (ThetaLowerSegment.join cell1122244864 cell1122375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1122507008 cell1122638080)
                  (ThetaLowerSegment.join cell1122769152 cell1122900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1123031296 cell1123162368)
                  (ThetaLowerSegment.join cell1123293440 cell1123424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1123555584 cell1123686656)
                  (ThetaLowerSegment.join cell1123817728 cell1123948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1124079872 cell1124210944)
                  (ThetaLowerSegment.join cell1124342016 cell1124473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1124604160 cell1124735232)
                  (ThetaLowerSegment.join cell1124866304 cell1124997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1125128448 cell1125259520)
                  (ThetaLowerSegment.join cell1125390592 cell1125521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1125652736 cell1125783808)
                  (ThetaLowerSegment.join cell1125914880 cell1126045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1126177024 cell1126308096)
                  (ThetaLowerSegment.join cell1126439168 cell1126570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1126701312 cell1126832384)
                  (ThetaLowerSegment.join cell1126963456 cell1127094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1127225600 cell1127356672)
                  (ThetaLowerSegment.join cell1127487744 cell1127618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1127749888 cell1127880960)
                  (ThetaLowerSegment.join cell1128012032 cell1128143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1128274176 cell1128405248)
                  (ThetaLowerSegment.join cell1128536320 cell1128667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1128798464 cell1128929536)
                (ThetaLowerSegment.join cell1129060608 cell1129191680))
              (ThetaLowerSegment.join cell1129322752 cell1129339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
