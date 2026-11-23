/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1929341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1897341184 :
    ThetaLowerSegment 1897341184 1897472256 (37945564359169 / 20000) (37948212603421 / 20000) := by
  exact
    packedTile65536 1897341184 1897472256 14 6198 43558 31 _ _ (213637 / 10000) (2136373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897472256 :
    ThetaLowerSegment 1897472256 1897603328 (37948212603421 / 20000) (5929818871001 / 3125) := by
  exact
    packedTile65536 1897472256 1897603328 14 6151 43559 31 _ _ (2136377 / 100000) (106819 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897603328 :
    ThetaLowerSegment 1897603328 1897734400 (5929818871001 / 3125) (5930224850723 / 3125) := by
  exact
    packedTile65536 1897603328 1897734400 14 6081 43561 31 _ _ (66762 / 3125) (2136387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897734400 :
    ThetaLowerSegment 1897734400 1897865472 (5930224850723 / 3125) (189780263526883 / 100000) := by
  exact
    packedTile65536 1897734400 1897865472 14 6117 43562 31 _ _ (2136391 / 100000) (1068197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897865472 :
    ThetaLowerSegment 1897865472 1897996544 (189780263526883 / 100000)
      (189793630969169 / 100000) := by
  exact
    packedTile65536 1897865472 1897996544 14 6257 43564 31 _ _ (1068199 / 50000) (2136401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1897996544 :
    ThetaLowerSegment 1897996544 1898127616 (189793630969169 / 100000)
      (47451697271891 / 25000) := by
  exact
    packedTile65536 1897996544 1898127616 14 6159 43566 31 _ _ (427281 / 20000) (267051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898127616 :
    ThetaLowerSegment 1898127616 1898258688 (47451697271891 / 25000) (5931874152688 / 3125) := by
  exact
    packedTile65536 1898127616 1898258688 14 6171 43567 31 _ _ (534103 / 25000) (427283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898258688 :
    ThetaLowerSegment 1898258688 1898389760 (5931874152688 / 3125) (47458285443183 / 25000) := by
  exact
    packedTile65536 1898258688 1898389760 14 6164 43569 31 _ _ (2136419 / 100000) (1068211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898389760 :
    ThetaLowerSegment 1898389760 1898520832 (47458285443183 / 25000) (9492313825989 / 5000) := by
  exact
    packedTile65536 1898389760 1898520832 14 6148 43570 31 _ _ (1068213 / 50000) (2136429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898520832 :
    ThetaLowerSegment 1898520832 1898651904 (9492313825989 / 5000) (237324242773 / 125) := by
  exact
    packedTile65536 1898520832 1898651904 14 6140 43572 31 _ _ (2136433 / 100000) (534109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898651904 :
    ThetaLowerSegment 1898651904 1898782976 (237324242773 / 125) (47468123715587 / 25000) := by
  exact
    packedTile65536 1898651904 1898782976 14 6132 43573 31 _ _ (2136439 / 100000) (1068221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898782976 :
    ThetaLowerSegment 1898782976 1898914048 (47468123715587 / 25000) (94942730476561 / 50000) := by
  exact
    packedTile65536 1898782976 1898914048 14 6069 43575 31 _ _ (1068223 / 50000) (2136449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898914048 :
    ThetaLowerSegment 1898914048 1899045120 (94942730476561 / 50000)
      (189898512544499 / 100000) := by
  exact
    packedTile65536 1898914048 1899045120 14 6109 43576 31 _ _ (2136453 / 100000) (267057 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899045120 :
    ThetaLowerSegment 1899045120 1899176192 (189898512544499 / 100000)
      (189911604771379 / 100000) := by
  exact
    packedTile65536 1899045120 1899176192 14 6128 43578 31 _ _ (106823 / 5000) (2136463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899176192 :
    ThetaLowerSegment 1899176192 1899307264 (189911604771379 / 100000)
      (18992470772349 / 10000) := by
  exact
    packedTile65536 1899176192 1899307264 14 6133 43579 31 _ _ (2136467 / 100000) (213647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899307264 :
    ThetaLowerSegment 1899307264 1899438336 (18992470772349 / 10000) (18993791113281 / 10000) := by
  exact
    packedTile65536 1899307264 1899438336 14 6180 43581 31 _ _ (1068237 / 50000) (2136477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899438336 :
    ThetaLowerSegment 1899438336 1899569408 (18993791113281 / 10000)
      (189950988533011 / 100000) := by
  exact
    packedTile65536 1899438336 1899569408 14 6121 43582 31 _ _ (2136481 / 100000) (534121 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899569408 :
    ThetaLowerSegment 1899569408 1899700480 (189950988533011 / 100000)
      (37992846097127 / 20000) := by
  exact
    packedTile65536 1899569408 1899700480 14 6198 43584 31 _ _ (267061 / 12500) (2136491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899700480 :
    ThetaLowerSegment 1899700480 1899831552 (37992846097127 / 20000) (37995484241153 / 20000) := by
  exact
    packedTile65536 1899700480 1899831552 14 6174 43585 31 _ _ (427299 / 20000) (1068249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899831552 :
    ThetaLowerSegment 1899831552 1899962624 (37995484241153 / 20000)
      (189990620515121 / 100000) := by
  exact
    packedTile65536 1899831552 1899962624 14 6178 43587 31 _ _ (1068251 / 50000) (427301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1899962624 :
    ThetaLowerSegment 1899962624 1900093696 (189990620515121 / 100000)
      (47500927726441 / 25000) := by
  exact
    packedTile65536 1899962624 1900093696 14 6127 43588 31 _ _ (2136509 / 100000) (66766 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900093696 :
    ThetaLowerSegment 1900093696 1900224768 (47500927726441 / 25000)
      (190017002165579 / 100000) := by
  exact
    packedTile65536 1900093696 1900224768 14 6221 43590 31 _ _ (427303 / 20000) (1068259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900224768 :
    ThetaLowerSegment 1900224768 1900355840 (190017002165579 / 100000)
      (190030250738501 / 100000) := by
  exact
    packedTile65536 1900224768 1900355840 14 6201 43591 31 _ _ (1068261 / 50000) (85461 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900355840 :
    ThetaLowerSegment 1900355840 1900486912 (190030250738501 / 100000)
      (95021719766009 / 50000) := by
  exact
    packedTile65536 1900355840 1900486912 14 6173 43593 31 _ _ (2136529 / 100000) (534133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900486912 :
    ThetaLowerSegment 1900486912 1900617984 (95021719766009 / 50000) (95028267180581 / 50000) := by
  exact
    packedTile65536 1900486912 1900617984 14 6129 43594 31 _ _ (267067 / 12500) (2136539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900617984 :
    ThetaLowerSegment 1900617984 1900749056 (95028267180581 / 50000)
      (190069560863833 / 100000) := by
  exact
    packedTile65536 1900617984 1900749056 14 6097 43596 31 _ _ (2136543 / 100000) (1068273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900749056 :
    ThetaLowerSegment 1900749056 1900880128 (190069560863833 / 100000)
      (190082837385533 / 100000) := by
  exact
    packedTile65536 1900749056 1900880128 14 6214 43597 31 _ _ (42731 / 2000) (2136553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1900880128 :
    ThetaLowerSegment 1900880128 1901011200 (190082837385533 / 100000)
      (95047859343843 / 50000) := by
  exact
    packedTile65536 1900880128 1901011200 14 6029 43599 31 _ _ (2136557 / 100000) (26707 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901011200 :
    ThetaLowerSegment 1901011200 1901142272 (95047859343843 / 50000) (95054438892681 / 50000) := by
  exact
    packedTile65536 1901011200 1901142272 14 6159 43600 31 _ _ (534141 / 25000) (2136567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901142272 :
    ThetaLowerSegment 1901142272 1901273344 (95054438892681 / 50000)
      (190122075384429 / 100000) := by
  exact
    packedTile65536 1901142272 1901273344 14 6177 43602 31 _ _ (2136571 / 100000) (1068287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901273344 :
    ThetaLowerSegment 1901273344 1901404416 (190122075384429 / 100000)
      (190135052953127 / 100000) := by
  exact
    packedTile65536 1901273344 1901404416 14 6074 43603 31 _ _ (2136577 / 100000) (106829 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901404416 :
    ThetaLowerSegment 1901404416 1901535488 (190135052953127 / 100000)
      (190148130983791 / 100000) := by
  exact
    packedTile65536 1901404416 1901535488 14 6121 43605 31 _ _ (267073 / 12500) (2136587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901535488 :
    ThetaLowerSegment 1901535488 1901666560 (190148130983791 / 100000)
      (38032208907959 / 20000) := by
  exact
    packedTile65536 1901535488 1901666560 14 6044 43606 31 _ _ (2136591 / 100000) (1068297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901666560 :
    ThetaLowerSegment 1901666560 1901797632 (38032208907959 / 20000)
      (190174041465429 / 100000) := by
  exact
    packedTile65536 1901666560 1901797632 14 6083 43608 31 _ _ (1068299 / 50000) (2136601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901797632 :
    ThetaLowerSegment 1901797632 1901928704 (190174041465429 / 100000)
      (190187040570249 / 100000) := by
  exact
    packedTile65536 1901797632 1901928704 14 6084 43609 31 _ _ (427321 / 20000) (66769 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1901928704 :
    ThetaLowerSegment 1901928704 1902059776 (190187040570249 / 100000)
      (190199960663013 / 100000) := by
  exact
    packedTile65536 1901928704 1902059776 14 6047 43611 31 _ _ (534153 / 25000) (427323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902059776 :
    ThetaLowerSegment 1902059776 1902190848 (190199960663013 / 100000)
      (23776625590251 / 12500) := by
  exact
    packedTile65536 1902059776 1902190848 14 6105 43612 31 _ _ (2136619 / 100000) (1068311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902190848 :
    ThetaLowerSegment 1902190848 1902321920 (23776625590251 / 12500) (95113097057153 / 50000) := by
  exact
    packedTile65536 1902190848 1902321920 14 6173 43614 31 _ _ (1068313 / 50000) (2136629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902321920 :
    ThetaLowerSegment 1902321920 1902452992 (95113097057153 / 50000) (95119673613527 / 50000) := by
  exact
    packedTile65536 1902321920 1902452992 14 6156 43615 31 _ _ (2136633 / 100000) (534159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902452992 :
    ThetaLowerSegment 1902452992 1902584064 (95119673613527 / 50000) (95126271554759 / 50000) := by
  exact
    packedTile65536 1902452992 1902584064 14 6176 43617 31 _ _ (2136639 / 100000) (1068321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902584064 :
    ThetaLowerSegment 1902584064 1902715136 (95126271554759 / 50000) (2378319895083 / 1250) := by
  exact
    packedTile65536 1902584064 1902715136 14 6107 43618 31 _ _ (1068323 / 50000) (2136649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902715136 :
    ThetaLowerSegment 1902715136 1902846208 (2378319895083 / 1250) (38055757087783 / 20000) := by
  exact
    packedTile65536 1902715136 1902846208 14 6175 43620 31 _ _ (2136653 / 100000) (133541 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902846208 :
    ThetaLowerSegment 1902846208 1902977280 (38055757087783 / 20000) (38058390734899 / 20000) := by
  exact
    packedTile65536 1902846208 1902977280 14 6163 43621 31 _ _ (106833 / 5000) (2136663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902977280 :
    ThetaLowerSegment 1902977280 1903108352 (38058390734899 / 20000) (23788129560817 / 12500) := by
  exact
    packedTile65536 1902977280 1903108352 14 6123 43623 31 _ _ (2136667 / 100000) (213667 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903108352 :
    ThetaLowerSegment 1903108352 1903239424 (23788129560817 / 12500) (95159123770939 / 50000) := by
  exact
    packedTile65536 1903108352 1903239424 14 6183 43624 31 _ _ (1068337 / 50000) (2136677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903239424 :
    ThetaLowerSegment 1903239424 1903370496 (95159123770939 / 50000) (95165619281179 / 50000) := by
  exact
    packedTile65536 1903239424 1903370496 14 6080 43626 31 _ _ (2136681 / 100000) (534171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903370496 :
    ThetaLowerSegment 1903370496 1903501568 (95165619281179 / 50000) (95172048575371 / 50000) := by
  exact
    packedTile65536 1903370496 1903501568 14 6018 43627 31 _ _ (133543 / 6250) (2136691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903501568 :
    ThetaLowerSegment 1903501568 1903632640 (95172048575371 / 50000) (5948665818726 / 3125) := by
  exact
    packedTile65536 1903501568 1903632640 14 6182 43629 31 _ _ (427339 / 20000) (1068349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903632640 :
    ThetaLowerSegment 1903632640 1903763712 (5948665818726 / 3125) (95185287556221 / 50000) := by
  exact
    packedTile65536 1903632640 1903763712 14 6210 43630 31 _ _ (2136701 / 100000) (66772 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903763712 :
    ThetaLowerSegment 1903763712 1903894784 (95185287556221 / 50000) (95191851523197 / 50000) := by
  exact
    packedTile65536 1903763712 1903894784 14 6144 43632 31 _ _ (534177 / 25000) (2136711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1903894784 :
    ThetaLowerSegment 1903894784 1904025856 (95191851523197 / 50000) (47599176773471 / 25000) := by
  exact
    packedTile65536 1903894784 1904025856 14 6086 43633 31 _ _ (427343 / 20000) (1068359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904025856 :
    ThetaLowerSegment 1904025856 1904156928 (47599176773471 / 25000) (95204918625287 / 50000) := by
  exact
    packedTile65536 1904025856 1904156928 14 6145 43635 31 _ _ (1068361 / 50000) (85469 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904156928 :
    ThetaLowerSegment 1904156928 1904288000 (95204918625287 / 50000) (47605740260023 / 25000) := by
  exact
    packedTile65536 1904156928 1904288000 14 6142 43636 31 _ _ (2136729 / 100000) (534183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904288000 :
    ThetaLowerSegment 1904288000 1904419072 (47605740260023 / 25000) (47609054871743 / 25000) := by
  exact
    packedTile65536 1904288000 1904419072 14 6205 43638 31 _ _ (66773 / 3125) (2136739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904419072 :
    ThetaLowerSegment 1904419072 1904550144 (47609054871743 / 25000) (4761232195179 / 2500) := by
  exact
    packedTile65536 1904419072 1904550144 14 6116 43639 31 _ _ (2136743 / 100000) (1068373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904550144 :
    ThetaLowerSegment 1904550144 1904681216 (4761232195179 / 2500) (19046242668291 / 10000) := by
  exact
    packedTile65536 1904550144 1904681216 14 6149 43641 31 _ _ (8547 / 400) (2136753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904681216 :
    ThetaLowerSegment 1904681216 1904812288 (19046242668291 / 10000) (38095102863907 / 20000) := by
  exact
    packedTile65536 1904681216 1904812288 14 6125 43642 31 _ _ (2136757 / 100000) (53419 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904812288 :
    ThetaLowerSegment 1904812288 1904943360 (38095102863907 / 20000) (23811087535501 / 12500) := by
  exact
    packedTile65536 1904812288 1904943360 14 6171 43644 31 _ _ (2136763 / 100000) (1068383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1904943360 :
    ThetaLowerSegment 1904943360 1905074432 (23811087535501 / 12500) (5953185081774 / 3125) := by
  exact
    packedTile65536 1904943360 1905074432 14 6188 43645 31 _ _ (213677 / 10000) (2136773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905074432 :
    ThetaLowerSegment 1905074432 1905205504 (5953185081774 / 3125) (190514997555231 / 100000) := by
  exact
    packedTile65536 1905074432 1905205504 14 6119 43647 31 _ _ (2136777 / 100000) (106839 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905205504 :
    ThetaLowerSegment 1905205504 1905336576 (190514997555231 / 100000)
      (190528036211199 / 100000) := by
  exact
    packedTile65536 1905205504 1905336576 14 6102 43648 31 _ _ (133549 / 6250) (2136787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905336576 :
    ThetaLowerSegment 1905336576 1905467648 (190528036211199 / 100000)
      (190541087730627 / 100000) := by
  exact
    packedTile65536 1905336576 1905467648 14 6108 43650 31 _ _ (2136791 / 100000) (1068397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905467648 :
    ThetaLowerSegment 1905467648 1905598720 (190541087730627 / 100000)
      (190554096556851 / 100000) := by
  exact
    packedTile65536 1905467648 1905598720 14 6088 43651 31 _ _ (1068399 / 50000) (2136801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905598720 :
    ThetaLowerSegment 1905598720 1905729792 (190554096556851 / 100000)
      (95283568738883 / 50000) := by
  exact
    packedTile65536 1905598720 1905729792 14 6103 43653 31 _ _ (427361 / 20000) (267101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905729792 :
    ThetaLowerSegment 1905729792 1905860864 (95283568738883 / 50000) (95290197129707 / 50000) := by
  exact
    packedTile65536 1905729792 1905860864 14 6204 43654 31 _ _ (534203 / 25000) (427363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905860864 :
    ThetaLowerSegment 1905860864 1905991936 (95290197129707 / 50000) (47648416509003 / 25000) := by
  exact
    packedTile65536 1905860864 1905991936 14 6211 43656 31 _ _ (1068409 / 50000) (2136821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1905991936 :
    ThetaLowerSegment 1905991936 1906123008 (47648416509003 / 25000)
      (190606805372937 / 100000) := by
  exact
    packedTile65536 1905991936 1906123008 14 6149 43657 31 _ _ (85473 / 4000) (534207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906123008 :
    ThetaLowerSegment 1906123008 1906254080 (190606805372937 / 100000)
      (190619716111881 / 100000) := by
  exact
    packedTile65536 1906123008 1906254080 14 6042 43659 31 _ _ (66776 / 3125) (427367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906254080 :
    ThetaLowerSegment 1906254080 1906385152 (190619716111881 / 100000)
      (47658226704757 / 25000) := by
  exact
    packedTile65536 1906254080 1906385152 14 6173 43660 31 _ _ (2136839 / 100000) (1068421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906385152 :
    ThetaLowerSegment 1906385152 1906516224 (47658226704757 / 25000) (47661515310751 / 25000) := by
  exact
    packedTile65536 1906385152 1906516224 14 6156 43662 31 _ _ (1068423 / 50000) (2136849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906516224 :
    ThetaLowerSegment 1906516224 1906647296 (47661515310751 / 25000)
      (190658978519389 / 100000) := by
  exact
    packedTile65536 1906516224 1906647296 14 6045 43663 31 _ _ (2136853 / 100000) (267107 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906647296 :
    ThetaLowerSegment 1906647296 1906778368 (190658978519389 / 100000)
      (190672239872549 / 100000) := by
  exact
    packedTile65536 1906647296 1906778368 14 6206 43665 31 _ _ (106843 / 5000) (2136863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906778368 :
    ThetaLowerSegment 1906778368 1906909440 (190672239872549 / 100000)
      (47671349140667 / 25000) := by
  exact
    packedTile65536 1906778368 1906909440 14 6157 43666 31 _ _ (2136867 / 100000) (213687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906909440 :
    ThetaLowerSegment 1906909440 1907040512 (47671349140667 / 25000)
      (190698292591223 / 100000) := by
  exact
    packedTile65536 1906909440 1907040512 14 6035 43668 31 _ _ (2136873 / 100000) (534219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907040512 :
    ThetaLowerSegment 1907040512 1907171584 (190698292591223 / 100000)
      (190711267726583 / 100000) := by
  exact
    packedTile65536 1907040512 1907171584 14 6072 43669 31 _ _ (26711 / 1250) (2136883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907171584 :
    ThetaLowerSegment 1907171584 1907302656 (190711267726583 / 100000)
      (47681062328777 / 25000) := by
  exact
    packedTile65536 1907171584 1907302656 14 6075 43671 31 _ _ (2136887 / 100000) (213689 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907302656 :
    ThetaLowerSegment 1907302656 1907433728 (47681062328777 / 25000) (47684316818339 / 25000) := by
  exact
    packedTile65536 1907302656 1907433728 14 6092 43672 31 _ _ (1068447 / 50000) (2136897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907433728 :
    ThetaLowerSegment 1907433728 1907564800 (47684316818339 / 25000)
      (190750415625209 / 100000) := by
  exact
    packedTile65536 1907433728 1907564800 14 6153 43674 31 _ _ (2136901 / 100000) (267113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907564800 :
    ThetaLowerSegment 1907564800 1907695872 (190750415625209 / 100000) (7630540338421 / 4000) := by
  exact
    packedTile65536 1907564800 1907695872 14 6127 43675 31 _ _ (534227 / 25000) (2136911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907695872 :
    ThetaLowerSegment 1907695872 1907826944 (7630540338421 / 4000) (953883626399 / 500) := by
  exact
    packedTile65536 1907695872 1907826944 14 6185 43677 31 _ _ (427383 / 20000) (1068459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907826944 :
    ThetaLowerSegment 1907826944 1907958016 (953883626399 / 500) (47697471111369 / 25000) := by
  exact
    packedTile65536 1907826944 1907958016 14 6158 43678 31 _ _ (1068461 / 50000) (85477 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1907958016 :
    ThetaLowerSegment 1907958016 1908089088 (47697471111369 / 25000) (47700809527137 / 25000) := by
  exact
    packedTile65536 1907958016 1908089088 14 6249 43680 31 _ _ (66779 / 3125) (2136931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908089088 :
    ThetaLowerSegment 1908089088 1908220160 (47700809527137 / 25000)
      (190816228536413 / 100000) := by
  exact
    packedTile65536 1908089088 1908220160 14 6079 43681 31 _ _ (427387 / 20000) (1068469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908220160 :
    ThetaLowerSegment 1908220160 1908351232 (190816228536413 / 100000)
      (190829289525917 / 100000) := by
  exact
    packedTile65536 1908220160 1908351232 14 6112 43683 31 _ _ (1068471 / 50000) (427389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908351232 :
    ThetaLowerSegment 1908351232 1908482304 (190829289525917 / 100000)
      (95421236182149 / 50000) := by
  exact
    packedTile65536 1908351232 1908482304 14 6169 43684 31 _ _ (2136949 / 100000) (267119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908482304 :
    ThetaLowerSegment 1908482304 1908613376 (95421236182149 / 50000) (95427790226201 / 50000) := by
  exact
    packedTile65536 1908482304 1908613376 14 6134 43686 31 _ _ (534239 / 25000) (2136959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908613376 :
    ThetaLowerSegment 1908613376 1908744448 (95427790226201 / 50000) (19086847916107 / 10000) := by
  exact
    packedTile65536 1908613376 1908744448 14 6036 43687 31 _ _ (2136963 / 100000) (1068483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908744448 :
    ThetaLowerSegment 1908744448 1908875520 (19086847916107 / 10000) (477203834777 / 250) := by
  exact
    packedTile65536 1908744448 1908875520 14 6109 43689 31 _ _ (213697 / 10000) (2136973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1908875520 :
    ThetaLowerSegment 1908875520 1909006592 (477203834777 / 250) (95447325337813 / 50000) := by
  exact
    packedTile65536 1908875520 1909006592 14 6138 43690 31 _ _ (2136977 / 100000) (106849 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909006592 :
    ThetaLowerSegment 1909006592 1909137664 (95447325337813 / 50000) (47726935458371 / 25000) := by
  exact
    packedTile65536 1909006592 1909137664 14 6126 43692 31 _ _ (2136983 / 100000) (1068493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909137664 :
    ThetaLowerSegment 1909137664 1909268736 (47726935458371 / 25000) (95460434681527 / 50000) := by
  exact
    packedTile65536 1909137664 1909268736 14 6143 43693 31 _ _ (213699 / 10000) (2136993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909268736 :
    ThetaLowerSegment 1909268736 1909399808 (95460434681527 / 50000) (38186782291149 / 20000) := by
  exact
    packedTile65536 1909268736 1909399808 14 6103 43695 31 _ _ (2136997 / 100000) (2137 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909399808 :
    ThetaLowerSegment 1909399808 1909530880 (38186782291149 / 20000)
      (190947156606537 / 100000) := by
  exact
    packedTile65536 1909399808 1909530880 14 6198 43696 31 _ _ (534251 / 25000) (2137007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909530880 :
    ThetaLowerSegment 1909530880 1909661952 (190947156606537 / 100000)
      (38192058990033 / 20000) := by
  exact
    packedTile65536 1909530880 1909661952 14 6148 43698 31 _ _ (2137011 / 100000) (1068507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909661952 :
    ThetaLowerSegment 1909661952 1909793024 (38192058990033 / 20000)
      (190973358541199 / 100000) := by
  exact
    packedTile65536 1909661952 1909793024 14 6113 43699 31 _ _ (1068509 / 50000) (2137021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909793024 :
    ThetaLowerSegment 1909793024 1909924096 (190973358541199 / 100000)
      (190986343105099 / 100000) := by
  exact
    packedTile65536 1909793024 1909924096 14 6076 43701 31 _ _ (85481 / 4000) (534257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1909924096 :
    ThetaLowerSegment 1909924096 1910055168 (190986343105099 / 100000)
      (95499763224669 / 50000) := by
  exact
    packedTile65536 1909924096 1910055168 14 6169 43702 31 _ _ (2137031 / 100000) (1068517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910055168 :
    ThetaLowerSegment 1910055168 1910186240 (95499763224669 / 50000) (47753165705481 / 25000) := by
  exact
    packedTile65536 1910055168 1910186240 14 6147 43704 31 _ _ (1068519 / 50000) (2137041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910186240 :
    ThetaLowerSegment 1910186240 1910317312 (47753165705481 / 25000) (5969556827217 / 3125) := by
  exact
    packedTile65536 1910186240 1910317312 14 6156 43705 31 _ _ (427409 / 20000) (267131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910317312 :
    ThetaLowerSegment 1910317312 1910448384 (5969556827217 / 3125) (47759746212079 / 25000) := by
  exact
    packedTile65536 1910317312 1910448384 14 6161 43707 31 _ _ (534263 / 25000) (427411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910448384 :
    ThetaLowerSegment 1910448384 1910579456 (47759746212079 / 25000) (23881502613527 / 12500) := by
  exact
    packedTile65536 1910448384 1910579456 14 6100 43708 31 _ _ (2137059 / 100000) (1068531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910579456 :
    ThetaLowerSegment 1910579456 1910710528 (23881502613527 / 12500) (95532589411789 / 50000) := by
  exact
    packedTile65536 1910579456 1910710528 14 6157 43710 31 _ _ (1068533 / 50000) (2137069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910710528 :
    ThetaLowerSegment 1910710528 1910841600 (95532589411789 / 50000) (11942388702689 / 6250) := by
  exact
    packedTile65536 1910710528 1910841600 14 6102 43711 31 _ _ (2137073 / 100000) (534269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910841600 :
    ThetaLowerSegment 1910841600 1910972672 (11942388702689 / 6250) (19109128534403 / 10000) := by
  exact
    packedTile65536 1910841600 1910972672 14 6114 43713 31 _ _ (2137079 / 100000) (1068541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1910972672 :
    ThetaLowerSegment 1910972672 1911103744 (19109128534403 / 10000) (23888050614373 / 12500) := by
  exact
    packedTile65536 1910972672 1911103744 14 6139 43714 31 _ _ (1068543 / 50000) (2137089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911103744 :
    ThetaLowerSegment 1911103744 1911234816 (23888050614373 / 12500) (7644696536003 / 4000) := by
  exact
    packedTile65536 1911103744 1911234816 14 6087 43716 31 _ _ (2137093 / 100000) (267137 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911234816 :
    ThetaLowerSegment 1911234816 1911365888 (7644696536003 / 4000) (7645224998091 / 4000) := by
  exact
    packedTile65536 1911234816 1911365888 14 6182 43717 31 _ _ (21371 / 1000) (2137103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911365888 :
    ThetaLowerSegment 1911365888 1911496960 (7645224998091 / 4000) (47785948985679 / 25000) := by
  exact
    packedTile65536 1911365888 1911496960 14 6163 43719 31 _ _ (2137107 / 100000) (213711 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911496960 :
    ThetaLowerSegment 1911496960 1911628032 (47785948985679 / 25000) (9557841189483 / 5000) := by
  exact
    packedTile65536 1911496960 1911628032 14 6096 43720 31 _ _ (1068557 / 50000) (2137117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911628032 :
    ThetaLowerSegment 1911628032 1911759104 (9557841189483 / 5000) (191169772605799 / 100000) := by
  exact
    packedTile65536 1911628032 1911759104 14 6059 43722 31 _ _ (2137121 / 100000) (534281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911759104 :
    ThetaLowerSegment 1911759104 1911890176 (191169772605799 / 100000)
      (191182864645801 / 100000) := by
  exact
    packedTile65536 1911759104 1911890176 14 6126 43723 31 _ _ (2137127 / 100000) (213713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911890176 :
    ThetaLowerSegment 1911890176 1912021248 (191182864645801 / 100000)
      (38239161425861 / 20000) := by
  exact
    packedTile65536 1911890176 1912021248 14 6056 43725 31 _ _ (1068567 / 50000) (2137137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912021248 :
    ThetaLowerSegment 1912021248 1912152320 (38239161425861 / 20000) (38241811480701 / 20000) := by
  exact
    packedTile65536 1912021248 1912152320 14 6200 43726 31 _ _ (2137141 / 100000) (267143 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912152320 :
    ThetaLowerSegment 1912152320 1912283392 (38241811480701 / 20000)
      (191222245743813 / 100000) := by
  exact
    packedTile65536 1912152320 1912283392 14 6171 43728 31 _ _ (534287 / 25000) (2137151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912283392 :
    ThetaLowerSegment 1912283392 1912414464 (191222245743813 / 100000)
      (191235372149823 / 100000) := by
  exact
    packedTile65536 1912283392 1912414464 14 6142 43729 31 _ _ (427431 / 20000) (1068579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912414464 :
    ThetaLowerSegment 1912414464 1912545536 (191235372149823 / 100000)
      (191248462267073 / 100000) := by
  exact
    packedTile65536 1912414464 1912545536 14 6125 43731 31 _ _ (1068581 / 50000) (427433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912545536 :
    ThetaLowerSegment 1912545536 1912676608 (191248462267073 / 100000)
      (95630754841909 / 50000) := by
  exact
    packedTile65536 1912545536 1912676608 14 6105 43732 31 _ _ (2137169 / 100000) (534293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912676608 :
    ThetaLowerSegment 1912676608 1912807680 (95630754841909 / 50000)
      (191274510119343 / 100000) := by
  exact
    packedTile65536 1912676608 1912807680 14 6083 43734 31 _ _ (85487 / 4000) (1068589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912807680 :
    ThetaLowerSegment 1912807680 1912938752 (191274510119343 / 100000)
      (191287685846373 / 100000) := by
  exact
    packedTile65536 1912807680 1912938752 14 6165 43735 31 _ _ (1068591 / 50000) (427437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1912938752 :
    ThetaLowerSegment 1912938752 1913069824 (191287685846373 / 100000)
      (23912599687611 / 12500) := by
  exact
    packedTile65536 1912938752 1913069824 14 6135 43737 31 _ _ (2137189 / 100000) (267149 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913069824 :
    ThetaLowerSegment 1913069824 1913200896 (23912599687611 / 12500) (47828502945939 / 25000) := by
  exact
    packedTile65536 1913069824 1913200896 14 6183 43738 31 _ _ (534299 / 25000) (2137199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913200896 :
    ThetaLowerSegment 1913200896 1913331968 (47828502945939 / 25000)
      (191327016664011 / 100000) := by
  exact
    packedTile65536 1913200896 1913331968 14 6085 43740 31 _ _ (2137203 / 100000) (1068603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913331968 :
    ThetaLowerSegment 1913331968 1913463040 (191327016664011 / 100000)
      (191340117761311 / 100000) := by
  exact
    packedTile65536 1913331968 1913463040 14 6130 43741 31 _ _ (213721 / 10000) (2137213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913463040 :
    ThetaLowerSegment 1913463040 1913594112 (191340117761311 / 100000)
      (191353227450389 / 100000) := by
  exact
    packedTile65536 1913463040 1913594112 14 6134 43743 31 _ _ (2137217 / 100000) (106861 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913594112 :
    ThetaLowerSegment 1913594112 1913725184 (191353227450389 / 100000) (7654657590519 / 4000) := by
  exact
    packedTile65536 1913594112 1913725184 14 6182 43744 31 _ _ (2137223 / 100000) (1068613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913725184 :
    ThetaLowerSegment 1913725184 1913856256 (7654657590519 / 4000) (38275879130247 / 20000) := by
  exact
    packedTile65536 1913725184 1913856256 14 6062 43746 31 _ _ (213723 / 10000) (2137233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913856256 :
    ThetaLowerSegment 1913856256 1913987328 (38275879130247 / 20000) (95696258074589 / 50000) := by
  exact
    packedTile65536 1913856256 1913987328 14 6139 43747 31 _ _ (2137237 / 100000) (53431 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1913987328 :
    ThetaLowerSegment 1913987328 1914118400 (95696258074589 / 50000) (19140555974931 / 10000) := by
  exact
    packedTile65536 1913987328 1914118400 14 6103 43749 31 _ _ (534311 / 25000) (2137247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914118400 :
    ThetaLowerSegment 1914118400 1914249472 (19140555974931 / 10000) (38283734356839 / 20000) := by
  exact
    packedTile65536 1914118400 1914249472 14 6135 43750 31 _ _ (2137251 / 100000) (1068627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914249472 :
    ThetaLowerSegment 1914249472 1914380544 (38283734356839 / 20000)
      (191431771038477 / 100000) := by
  exact
    packedTile65536 1914249472 1914380544 14 6129 43752 31 _ _ (1068629 / 50000) (2137261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914380544 :
    ThetaLowerSegment 1914380544 1914511616 (191431771038477 / 100000)
      (191444942996509 / 100000) := by
  exact
    packedTile65536 1914380544 1914511616 14 6163 43753 31 _ _ (133579 / 6250) (2137267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914511616 :
    ThetaLowerSegment 1914511616 1914642688 (191444942996509 / 100000)
      (191458070114991 / 100000) := by
  exact
    packedTile65536 1914511616 1914642688 14 6142 43755 31 _ _ (2137271 / 100000) (1068637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914642688 :
    ThetaLowerSegment 1914642688 1914773760 (191458070114991 / 100000)
      (191471207962857 / 100000) := by
  exact
    packedTile65536 1914642688 1914773760 14 6147 43756 31 _ _ (1068639 / 50000) (2137281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914773760 :
    ThetaLowerSegment 1914773760 1914904832 (191471207962857 / 100000)
      (95742149416741 / 50000) := by
  exact
    packedTile65536 1914773760 1914904832 14 6125 43758 31 _ _ (427457 / 20000) (267161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1914904832 :
    ThetaLowerSegment 1914904832 1915035904 (95742149416741 / 50000) (19149747310137 / 10000) := by
  exact
    packedTile65536 1914904832 1915035904 14 6164 43759 31 _ _ (534323 / 25000) (427459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915035904 :
    ThetaLowerSegment 1915035904 1915166976 (19149747310137 / 10000)
      (191510666648097 / 100000) := by
  exact
    packedTile65536 1915035904 1915166976 14 6173 43761 31 _ _ (2137299 / 100000) (1068651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915166976 :
    ThetaLowerSegment 1915166976 1915298048 (191510666648097 / 100000)
      (191523798256161 / 100000) := by
  exact
    packedTile65536 1915166976 1915298048 14 6144 43762 31 _ _ (1068653 / 50000) (2137309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915298048 :
    ThetaLowerSegment 1915298048 1915429120 (191523798256161 / 100000)
      (191537034629377 / 100000) := by
  exact
    packedTile65536 1915298048 1915429120 14 6193 43764 31 _ _ (66791 / 3125) (427463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915429120 :
    ThetaLowerSegment 1915429120 1915560192 (191537034629377 / 100000) (30648000279 / 16) := by
  exact
    packedTile65536 1915429120 1915560192 14 6067 43765 31 _ _ (2137319 / 100000) (1068661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915560192 :
    ThetaLowerSegment 1915560192 1915691264 (30648000279 / 16) (23945395691823 / 12500) := by
  exact
    packedTile65536 1915560192 1915691264 14 6159 43767 31 _ _ (1068663 / 50000) (2137329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915691264 :
    ThetaLowerSegment 1915691264 1915822336 (23945395691823 / 12500)
      (191576231051213 / 100000) := by
  exact
    packedTile65536 1915691264 1915822336 14 6113 43768 31 _ _ (2137333 / 100000) (267167 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915822336 :
    ThetaLowerSegment 1915822336 1915953408 (191576231051213 / 100000)
      (191589354318813 / 100000) := by
  exact
    packedTile65536 1915822336 1915953408 14 6140 43770 31 _ _ (106867 / 5000) (2137343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915953408 :
    ThetaLowerSegment 1915953408 1916084480 (191589354318813 / 100000) (11975161931799 / 6250) := by
  exact
    packedTile65536 1915953408 1916084480 14 6193 43771 31 _ _ (2137347 / 100000) (42747 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916084480 :
    ThetaLowerSegment 1916084480 1916215552 (11975161931799 / 6250) (38323111645887 / 20000) := by
  exact
    packedTile65536 1916084480 1916215552 14 6067 43773 31 _ _ (2137353 / 100000) (534339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916215552 :
    ThetaLowerSegment 1916215552 1916346624 (38323111645887 / 20000) (38325743590991 / 20000) := by
  exact
    packedTile65536 1916215552 1916346624 14 6157 43774 31 _ _ (26717 / 1250) (2137363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916346624 :
    ThetaLowerSegment 1916346624 1916477696 (38325743590991 / 20000) (7665666815959 / 4000) := by
  exact
    packedTile65536 1916346624 1916477696 14 6060 43776 31 _ _ (2137367 / 100000) (213737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916477696 :
    ThetaLowerSegment 1916477696 1916608768 (7665666815959 / 4000) (191654810974327 / 100000) := by
  exact
    packedTile65536 1916477696 1916608768 14 6148 43777 31 _ _ (1068687 / 50000) (2137377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916608768 :
    ThetaLowerSegment 1916608768 1916739840 (191654810974327 / 100000)
      (191667921669381 / 100000) := by
  exact
    packedTile65536 1916608768 1916739840 14 6134 43779 31 _ _ (2137381 / 100000) (267173 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916739840 :
    ThetaLowerSegment 1916739840 1916870912 (191667921669381 / 100000)
      (191680874240661 / 100000) := by
  exact
    packedTile65536 1916739840 1916870912 14 6060 43780 31 _ _ (534347 / 25000) (2137391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1916870912 :
    ThetaLowerSegment 1916870912 1917001984 (191680874240661 / 100000)
      (191694119671279 / 100000) := by
  exact
    packedTile65536 1916870912 1917001984 14 6197 43782 31 _ _ (1068697 / 50000) (2137397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917001984 :
    ThetaLowerSegment 1917001984 1917133056 (191694119671279 / 100000)
      (95853582114791 / 50000) := by
  exact
    packedTile65536 1917001984 1917133056 14 6103 43783 31 _ _ (2137401 / 100000) (534351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917133056 :
    ThetaLowerSegment 1917133056 1917264128 (95853582114791 / 50000) (95860065941959 / 50000) := by
  exact
    packedTile65536 1917133056 1917264128 14 6067 43785 31 _ _ (66794 / 3125) (2137411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917264128 :
    ThetaLowerSegment 1917264128 1917395200 (95860065941959 / 50000) (23966655348441 / 12500) := by
  exact
    packedTile65536 1917264128 1917395200 14 6134 43786 31 _ _ (427483 / 20000) (1068709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917395200 :
    ThetaLowerSegment 1917395200 1917526272 (23966655348441 / 12500) (47936611945161 / 25000) := by
  exact
    packedTile65536 1917395200 1917526272 14 6178 43788 31 _ _ (1068711 / 50000) (85497 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917526272 :
    ThetaLowerSegment 1917526272 1917657344 (47936611945161 / 25000) (19175947327297 / 10000) := by
  exact
    packedTile65536 1917526272 1917657344 14 6094 43789 31 _ _ (2137429 / 100000) (267179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917657344 :
    ThetaLowerSegment 1917657344 1917788416 (19175947327297 / 10000) (95886299633723 / 50000) := by
  exact
    packedTile65536 1917657344 1917788416 14 6141 43791 31 _ _ (534359 / 25000) (2137439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917788416 :
    ThetaLowerSegment 1917788416 1917919488 (95886299633723 / 50000) (9589278356403 / 5000) := by
  exact
    packedTile65536 1917788416 1917919488 14 6067 43792 31 _ _ (1068721 / 50000) (427489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1917919488 :
    ThetaLowerSegment 1917919488 1918050560 (9589278356403 / 5000) (191798590604817 / 100000) := by
  exact
    packedTile65536 1917919488 1918050560 14 6093 43794 31 _ _ (2137449 / 100000) (534363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918050560 :
    ThetaLowerSegment 1918050560 1918181632 (191798590604817 / 100000)
      (191811605574401 / 100000) := by
  exact
    packedTile65536 1918050560 1918181632 14 6089 43795 31 _ _ (133591 / 6250) (2137459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918181632 :
    ThetaLowerSegment 1918181632 1918312704 (191811605574401 / 100000)
      (191824712497517 / 100000) := by
  exact
    packedTile65536 1918181632 1918312704 14 6132 43797 31 _ _ (2137463 / 100000) (1068733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918312704 :
    ThetaLowerSegment 1918312704 1918443776 (191824712497517 / 100000)
      (191837545867397 / 100000) := by
  exact
    packedTile65536 1918312704 1918443776 14 6004 43798 31 _ _ (213747 / 10000) (2137473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918443776 :
    ThetaLowerSegment 1918443776 1918574848 (191837545867397 / 100000)
      (95925374531413 / 50000) := by
  exact
    packedTile65536 1918443776 1918574848 14 6177 43800 31 _ _ (2137477 / 100000) (53437 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918574848 :
    ThetaLowerSegment 1918574848 1918705920 (95925374531413 / 50000)
      (191863909545657 / 100000) := by
  exact
    packedTile65536 1918574848 1918705920 14 6157 43801 31 _ _ (2137483 / 100000) (1068743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918705920 :
    ThetaLowerSegment 1918705920 1918836992 (191863909545657 / 100000)
      (191877232520827 / 100000) := by
  exact
    packedTile65536 1918705920 1918836992 14 6233 43803 31 _ _ (213749 / 10000) (2137493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918836992 :
    ThetaLowerSegment 1918836992 1918968064 (191877232520827 / 100000)
      (95945228607383 / 50000) := by
  exact
    packedTile65536 1918836992 1918968064 14 6187 43804 31 _ _ (2137497 / 100000) (171 / 8)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1918968064 :
    ThetaLowerSegment 1918968064 1919099136 (95945228607383 / 50000) (95951689213223 / 50000) := by
  exact
    packedTile65536 1918968064 1919099136 14 6045 43806 31 _ _ (66797 / 3125) (2137507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919099136 :
    ThetaLowerSegment 1919099136 1919230208 (95951689213223 / 50000)
      (191916611757047 / 100000) := by
  exact
    packedTile65536 1919099136 1919230208 14 6191 43807 31 _ _ (2137511 / 100000) (1068757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919230208 :
    ThetaLowerSegment 1919230208 1919361280 (191916611757047 / 100000)
      (191929565116127 / 100000) := by
  exact
    packedTile65536 1919230208 1919361280 14 6060 43809 31 _ _ (1068759 / 50000) (2137521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919361280 :
    ThetaLowerSegment 1919361280 1919492352 (191929565116127 / 100000) (7677702193979 / 4000) := by
  exact
    packedTile65536 1919361280 1919492352 14 6077 43810 31 _ _ (534381 / 25000) (2137527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919492352 :
    ThetaLowerSegment 1919492352 1919623424 (7677702193979 / 4000) (23994473537987 / 12500) := by
  exact
    packedTile65536 1919492352 1919623424 14 6191 43812 31 _ _ (2137531 / 100000) (1068767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919623424 :
    ThetaLowerSegment 1919623424 1919754496 (23994473537987 / 12500) (47992257053567 / 25000) := by
  exact
    packedTile65536 1919623424 1919754496 14 6194 43813 31 _ _ (1068769 / 50000) (2137541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919754496 :
    ThetaLowerSegment 1919754496 1919885568 (47992257053567 / 25000)
      (191982219004463 / 100000) := by
  exact
    packedTile65536 1919754496 1919885568 14 6171 43815 31 _ _ (427509 / 20000) (534387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919885568 :
    ThetaLowerSegment 1919885568 1920016640 (191982219004463 / 100000)
      (191995215320623 / 100000) := by
  exact
    packedTile65536 1919885568 1920016640 14 6080 43816 31 _ _ (133597 / 6250) (427511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920016640 :
    ThetaLowerSegment 1920016640 1920147712 (191995215320623 / 100000)
      (192008468180223 / 100000) := by
  exact
    packedTile65536 1920016640 1920147712 14 6200 43817 31 _ _ (1068779 / 50000) (2137561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920147712 :
    ThetaLowerSegment 1920147712 1920278784 (192008468180223 / 100000)
      (192021597104453 / 100000) := by
  exact
    packedTile65536 1920147712 1920278784 14 6142 43819 31 _ _ (427513 / 20000) (66799 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920278784 :
    ThetaLowerSegment 1920278784 1920409856 (192021597104453 / 100000)
      (38406887072377 / 20000) := by
  exact
    packedTile65536 1920278784 1920409856 14 6006 43820 31 _ _ (534393 / 25000) (85503 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920409856 :
    ThetaLowerSegment 1920409856 1920540928 (38406887072377 / 20000) (6001482846263 / 3125) := by
  exact
    packedTile65536 1920409856 1920540928 14 6089 43822 31 _ _ (2137579 / 100000) (1068791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920540928 :
    ThetaLowerSegment 1920540928 1920672000 (6001482846263 / 3125) (48015106556859 / 25000) := by
  exact
    packedTile65536 1920540928 1920672000 14 6070 43823 31 _ _ (1068793 / 50000) (2137589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920672000 :
    ThetaLowerSegment 1920672000 1920803072 (48015106556859 / 25000) (19207354677327 / 10000) := by
  exact
    packedTile65536 1920672000 1920803072 14 6138 43825 31 _ _ (2137593 / 100000) (534399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920803072 :
    ThetaLowerSegment 1920803072 1920934144 (19207354677327 / 10000) (38417319363033 / 20000) := by
  exact
    packedTile65536 1920803072 1920934144 14 6105 43826 31 _ _ (2137599 / 100000) (1068801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1920934144 :
    ThetaLowerSegment 1920934144 1921065216 (38417319363033 / 20000)
      (192099619110917 / 100000) := by
  exact
    packedTile65536 1920934144 1921065216 14 6092 43828 31 _ _ (1068803 / 50000) (2137609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921065216 :
    ThetaLowerSegment 1921065216 1921196288 (192099619110917 / 100000)
      (96056355995271 / 50000) := by
  exact
    packedTile65536 1921065216 1921196288 14 6125 43829 31 _ _ (2137613 / 100000) (133601 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921196288 :
    ThetaLowerSegment 1921196288 1921327360 (96056355995271 / 50000) (96062964447501 / 50000) := by
  exact
    packedTile65536 1921196288 1921327360 14 6183 43831 31 _ _ (106881 / 5000) (2137623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921327360 :
    ThetaLowerSegment 1921327360 1921458432 (96062964447501 / 50000) (48034773100517 / 25000) := by
  exact
    packedTile65536 1921327360 1921458432 14 6158 43832 31 _ _ (2137627 / 100000) (213763 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921458432 :
    ThetaLowerSegment 1921458432 1921589504 (48034773100517 / 25000) (24019035200481 / 12500) := by
  exact
    packedTile65536 1921458432 1921589504 14 6170 43834 31 _ _ (1068817 / 50000) (2137637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921589504 :
    ThetaLowerSegment 1921589504 1921720576 (24019035200481 / 12500) (24020680114461 / 12500) := by
  exact
    packedTile65536 1921589504 1921720576 14 6156 43835 31 _ _ (53441 / 2500) (2137643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921720576 :
    ThetaLowerSegment 1921720576 1921851648 (24020680114461 / 12500)
      (192178474149447 / 100000) := by
  exact
    packedTile65536 1921720576 1921851648 14 6097 43837 31 _ _ (2137647 / 100000) (42753 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921851648 :
    ThetaLowerSegment 1921851648 1921982720 (192178474149447 / 100000)
      (192191554454273 / 100000) := by
  exact
    packedTile65536 1921851648 1921982720 14 6119 43838 31 _ _ (1068827 / 50000) (2137657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1921982720 :
    ThetaLowerSegment 1921982720 1922113792 (192191554454273 / 100000)
      (192204337667053 / 100000) := by
  exact
    packedTile65536 1921982720 1922113792 14 5980 43840 31 _ _ (2137661 / 100000) (66802 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922113792 :
    ThetaLowerSegment 1922113792 1922244864 (192204337667053 / 100000)
      (192217638237349 / 100000) := by
  exact
    packedTile65536 1922113792 1922244864 14 6222 43841 31 _ _ (534417 / 25000) (2137671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922244864 :
    ThetaLowerSegment 1922244864 1922375936 (192217638237349 / 100000)
      (192230660947357 / 100000) := by
  exact
    packedTile65536 1922244864 1922375936 14 6092 43843 31 _ _ (1068837 / 50000) (2137677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922375936 :
    ThetaLowerSegment 1922375936 1922507008 (192230660947357 / 100000)
      (192243786308697 / 100000) := by
  exact
    packedTile65536 1922375936 1922507008 14 6140 43844 31 _ _ (2137681 / 100000) (534421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922507008 :
    ThetaLowerSegment 1922507008 1922638080 (192243786308697 / 100000)
      (192256995082849 / 100000) := by
  exact
    packedTile65536 1922507008 1922638080 14 6179 43846 31 _ _ (267211 / 12500) (2137691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922638080 :
    ThetaLowerSegment 1922638080 1922769152 (192256995082849 / 100000)
      (96135050645447 / 50000) := by
  exact
    packedTile65536 1922638080 1922769152 14 6131 43847 31 _ _ (427539 / 20000) (1068849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922769152 :
    ThetaLowerSegment 1922769152 1922900224 (96135050645447 / 50000) (96141583462759 / 50000) := by
  exact
    packedTile65536 1922769152 1922900224 14 6112 43849 31 _ _ (1068851 / 50000) (427541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1922900224 :
    ThetaLowerSegment 1922900224 1923031296 (96141583462759 / 50000) (2403701464583 / 1250) := by
  exact
    packedTile65536 1922900224 1923031296 14 6058 43850 31 _ _ (2137709 / 100000) (133607 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923031296 :
    ThetaLowerSegment 1923031296 1923162368 (2403701464583 / 1250) (9615462136837 / 5000) := by
  exact
    packedTile65536 1923031296 1923162368 14 6140 43852 31 _ _ (427543 / 20000) (1068859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923162368 :
    ThetaLowerSegment 1923162368 1923293440 (9615462136837 / 5000) (96161217309601 / 50000) := by
  exact
    packedTile65536 1923162368 1923293440 14 6171 43853 31 _ _ (1068861 / 50000) (85509 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923293440 :
    ThetaLowerSegment 1923293440 1923424512 (96161217309601 / 50000) (38467102221499 / 20000) := by
  exact
    packedTile65536 1923293440 1923424512 14 6117 43855 31 _ _ (2137729 / 100000) (534433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923424512 :
    ThetaLowerSegment 1923424512 1923555584 (38467102221499 / 20000)
      (192348769346167 / 100000) := by
  exact
    packedTile65536 1923424512 1923555584 14 6202 43856 31 _ _ (267217 / 12500) (2137739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923555584 :
    ThetaLowerSegment 1923555584 1923686656 (192348769346167 / 100000)
      (96180944337479 / 50000) := by
  exact
    packedTile65536 1923555584 1923686656 14 6137 43858 31 _ _ (2137743 / 100000) (1068873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923686656 :
    ThetaLowerSegment 1923686656 1923817728 (96180944337479 / 50000) (48093776059819 / 25000) := by
  exact
    packedTile65536 1923686656 1923817728 14 6182 43859 31 _ _ (2137749 / 100000) (267219 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923817728 :
    ThetaLowerSegment 1923817728 1923948800 (48093776059819 / 25000) (24048524749347 / 12500) := by
  exact
    packedTile65536 1923817728 1923948800 14 6125 43861 31 _ _ (534439 / 25000) (2137759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923948800 :
    ThetaLowerSegment 1923948800 1924079872 (24048524749347 / 12500) (96200646965457 / 50000) := by
  exact
    packedTile65536 1923948800 1924079872 14 6126 43862 31 _ _ (2137763 / 100000) (1068883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924079872 :
    ThetaLowerSegment 1924079872 1924210944 (96200646965457 / 50000) (96207222745977 / 50000) := by
  exact
    packedTile65536 1924079872 1924210944 14 6152 43864 31 _ _ (213777 / 10000) (2137773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924210944 :
    ThetaLowerSegment 1924210944 1924342016 (96207222745977 / 50000) (38485489917889 / 20000) := by
  exact
    packedTile65536 1924210944 1924342016 14 6083 43865 31 _ _ (2137777 / 100000) (106889 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924342016 :
    ThetaLowerSegment 1924342016 1924473088 (38485489917889 / 20000) (12027542520527 / 6250) := by
  exact
    packedTile65536 1924342016 1924473088 14 6189 43867 31 _ _ (2137783 / 100000) (1068893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924473088 :
    ThetaLowerSegment 1924473088 1924604160 (12027542520527 / 6250) (12028354880727 / 6250) := by
  exact
    packedTile65536 1924473088 1924604160 14 6080 43868 31 _ _ (213779 / 10000) (2137793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924604160 :
    ThetaLowerSegment 1924604160 1924735232 (12028354880727 / 6250) (96233421322779 / 50000) := by
  exact
    packedTile65536 1924604160 1924735232 14 6158 43870 31 _ _ (2137797 / 100000) (10689 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924735232 :
    ThetaLowerSegment 1924735232 1924866304 (96233421322779 / 50000) (96240000414589 / 50000) := by
  exact
    packedTile65536 1924735232 1924866304 14 6155 43871 31 _ _ (534451 / 25000) (2137807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924866304 :
    ThetaLowerSegment 1924866304 1924997376 (96240000414589 / 50000) (96246430950077 / 50000) := by
  exact
    packedTile65536 1924866304 1924997376 14 6016 43873 31 _ _ (2137811 / 100000) (1068907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1924997376 :
    ThetaLowerSegment 1924997376 1925128448 (96246430950077 / 50000) (24063243969971 / 12500) := by
  exact
    packedTile65536 1924997376 1925128448 14 6123 43874 31 _ _ (1068909 / 50000) (2137821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925128448 :
    ThetaLowerSegment 1925128448 1925259520 (24063243969971 / 12500) (24064883680979 / 12500) := by
  exact
    packedTile65536 1925128448 1925259520 14 6136 43876 31 _ _ (66807 / 3125) (2137827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925259520 :
    ThetaLowerSegment 1925259520 1925390592 (24064883680979 / 12500) (19253223421113 / 10000) := by
  exact
    packedTile65536 1925259520 1925390592 14 6158 43877 31 _ _ (2137831 / 100000) (1068917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925390592 :
    ThetaLowerSegment 1925390592 1925521664 (19253223421113 / 10000) (2406816605861 / 1250) := by
  exact
    packedTile65536 1925390592 1925521664 14 6125 43879 31 _ _ (1068919 / 50000) (2137841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925521664 :
    ThetaLowerSegment 1925521664 1925652736 (2406816605861 / 1250) (19255835649631 / 10000) := by
  exact
    packedTile65536 1925521664 1925652736 14 6094 43880 31 _ _ (427569 / 20000) (267231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925652736 :
    ThetaLowerSegment 1925652736 1925783808 (19255835649631 / 10000) (96285750005203 / 50000) := by
  exact
    packedTile65536 1925652736 1925783808 14 6148 43882 31 _ _ (534463 / 25000) (427571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925783808 :
    ThetaLowerSegment 1925783808 1925914880 (96285750005203 / 50000) (24073073229903 / 12500) := by
  exact
    packedTile65536 1925783808 1925914880 14 6121 43883 31 _ _ (1068929 / 50000) (2137861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1925914880 :
    ThetaLowerSegment 1925914880 1926045952 (24073073229903 / 12500)
      (192597723019649 / 100000) := by
  exact
    packedTile65536 1925914880 1926045952 14 6145 43885 31 _ _ (427573 / 20000) (534467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926045952 :
    ThetaLowerSegment 1926045952 1926177024 (192597723019649 / 100000)
      (192610689213329 / 100000) := by
  exact
    packedTile65536 1926045952 1926177024 14 6065 43886 31 _ _ (133617 / 6250) (17103 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926177024 :
    ThetaLowerSegment 1926177024 1926308096 (192610689213329 / 100000)
      (192623832893421 / 100000) := by
  exact
    packedTile65536 1926177024 1926308096 14 6148 43888 31 _ _ (2137879 / 100000) (1068941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926308096 :
    ThetaLowerSegment 1926308096 1926439168 (192623832893421 / 100000)
      (192636835516073 / 100000) := by
  exact
    packedTile65536 1926308096 1926439168 14 6082 43889 31 _ _ (1068943 / 50000) (2137889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926439168 :
    ThetaLowerSegment 1926439168 1926570240 (192636835516073 / 100000)
      (192649945069817 / 100000) := by
  exact
    packedTile65536 1926439168 1926570240 14 6132 43891 31 _ _ (534473 / 25000) (427579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926570240 :
    ThetaLowerSegment 1926570240 1926701312 (192649945069817 / 100000) (6020716249339 / 3125) := by
  exact
    packedTile65536 1926570240 1926701312 14 6069 43892 31 _ _ (2137899 / 100000) (1068951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926701312 :
    ThetaLowerSegment 1926701312 1926832384 (6020716249339 / 3125) (12042248109817 / 6250) := by
  exact
    packedTile65536 1926701312 1926832384 14 6104 43894 31 _ _ (1068953 / 50000) (2137909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926832384 :
    ThetaLowerSegment 1926832384 1926963456 (12042248109817 / 6250) (96344563236837 / 50000) := by
  exact
    packedTile65536 1926832384 1926963456 14 6154 43895 31 _ _ (2137913 / 100000) (534479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1926963456 :
    ThetaLowerSegment 1926963456 1927094528 (96344563236837 / 50000) (96351145892517 / 50000) := by
  exact
    packedTile65536 1926963456 1927094528 14 6158 43897 31 _ _ (13362 / 625) (2137923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927094528 :
    ThetaLowerSegment 1927094528 1927225600 (96351145892517 / 50000) (48178875507447 / 25000) := by
  exact
    packedTile65536 1927094528 1927225600 14 6179 43898 31 _ _ (1068963 / 50000) (2137929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927225600 :
    ThetaLowerSegment 1927225600 1927356672 (48178875507447 / 25000) (38545712532497 / 20000) := by
  exact
    packedTile65536 1927225600 1927356672 14 6109 43900 31 _ _ (2137933 / 100000) (133621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927356672 :
    ThetaLowerSegment 1927356672 1927487744 (38545712532497 / 20000) (38548319964121 / 20000) := by
  exact
    packedTile65536 1927356672 1927487744 14 6098 43901 31 _ _ (106897 / 5000) (2137943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927487744 :
    ThetaLowerSegment 1927487744 1927618816 (38548319964121 / 20000)
      (192754773850019 / 100000) := by
  exact
    packedTile65536 1927487744 1927618816 14 6162 43903 31 _ _ (2137947 / 100000) (42759 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927618816 :
    ThetaLowerSegment 1927618816 1927749888 (192754773850019 / 100000)
      (38553607543327 / 20000) := by
  exact
    packedTile65536 1927618816 1927749888 14 6204 43904 31 _ _ (1068977 / 50000) (2137957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927749888 :
    ThetaLowerSegment 1927749888 1927880960 (38553607543327 / 20000) (38556259468911 / 20000) := by
  exact
    packedTile65536 1927749888 1927880960 14 6202 43906 31 _ _ (53449 / 2500) (2137963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927880960 :
    ThetaLowerSegment 1927880960 1928012032 (38556259468911 / 20000) (19279439239243 / 10000) := by
  exact
    packedTile65536 1927880960 1928012032 14 6125 43907 31 _ _ (2137967 / 100000) (213797 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928012032 :
    ThetaLowerSegment 1928012032 1928143104 (19279439239243 / 10000) (6025228505291 / 3125) := by
  exact
    packedTile65536 1928012032 1928143104 14 6043 43909 31 _ _ (1068987 / 50000) (2137977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928143104 :
    ThetaLowerSegment 1928143104 1928274176 (6025228505291 / 3125) (192820432958709 / 100000) := by
  exact
    packedTile65536 1928143104 1928274176 14 6137 43910 31 _ _ (2137981 / 100000) (66812 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928274176 :
    ThetaLowerSegment 1928274176 1928405248 (192820432958709 / 100000)
      (38566721448153 / 20000) := by
  exact
    packedTile65536 1928274176 1928405248 14 6162 43912 31 _ _ (534497 / 25000) (2137991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928405248 :
    ThetaLowerSegment 1928405248 1928536320 (38566721448153 / 20000)
      (192846875631529 / 100000) := by
  exact
    packedTile65536 1928405248 1928536320 14 6206 43913 31 _ _ (1068997 / 50000) (2137997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928536320 :
    ThetaLowerSegment 1928536320 1928667392 (192846875631529 / 100000)
      (192859861849603 / 100000) := by
  exact
    packedTile65536 1928536320 1928667392 14 6074 43915 31 _ _ (2138001 / 100000) (534501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928667392 :
    ThetaLowerSegment 1928667392 1928798464 (192859861849603 / 100000)
      (192872982804699 / 100000) := by
  exact
    packedTile65536 1928667392 1928798464 14 6137 43916 31 _ _ (267251 / 12500) (2138011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928798464 :
    ThetaLowerSegment 1928798464 1928929536 (192872982804699 / 100000)
      (192885999040019 / 100000) := by
  exact
    packedTile65536 1928798464 1928929536 14 6088 43918 31 _ _ (427603 / 20000) (1069009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1928929536 :
    ThetaLowerSegment 1928929536 1929060608 (192885999040019 / 100000)
      (192898976833559 / 100000) := by
  exact
    packedTile65536 1928929536 1929060608 14 6070 43919 31 _ _ (1069011 / 50000) (85521 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929060608 :
    ThetaLowerSegment 1929060608 1929191680 (192898976833559 / 100000)
      (192912038046611 / 100000) := by
  exact
    packedTile65536 1929060608 1929191680 14 6109 43921 31 _ _ (534507 / 25000) (2138031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929191680 :
    ThetaLowerSegment 1929191680 1929322752 (192912038046611 / 100000)
      (192925195514001 / 100000) := by
  exact
    packedTile65536 1929191680 1929322752 14 6154 43922 31 _ _ (427607 / 20000) (1069019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929322752 :
    ThetaLowerSegment 1929322752 1929339136 (192925195514001 / 100000)
      (192926784079207 / 100000) := by
  exact
    packedTile65536 1929322752 1929339136 11 743 43924 31 _ _ (1069021 / 50000) (427609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929339136 :
    ThetaLowerSegment 1929339136 1929341184 (192926784079207 / 100000)
      (96463508562947 / 50000) := by
  exact
    packedTile65536 1929339136 1929341184 8 109 43924 31 _ _ (2138043 / 100000) (1069023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1897341184_1929341184 :
    ThetaLowerSegment 1897341184 1929341184 (37945564359169 / 20000) (96463508562947 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1897341184 cell1897472256)
                  (ThetaLowerSegment.join cell1897603328 cell1897734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1897865472 cell1897996544)
                  (ThetaLowerSegment.join cell1898127616 cell1898258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1898389760 cell1898520832)
                  (ThetaLowerSegment.join cell1898651904 cell1898782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1898914048 cell1899045120)
                  (ThetaLowerSegment.join cell1899176192 cell1899307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1899438336 cell1899569408)
                  (ThetaLowerSegment.join cell1899700480 cell1899831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1899962624 cell1900093696)
                  (ThetaLowerSegment.join cell1900224768 cell1900355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1900486912 cell1900617984)
                  (ThetaLowerSegment.join cell1900749056 cell1900880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1901011200 cell1901142272)
                  (ThetaLowerSegment.join cell1901273344 cell1901404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1901535488 cell1901666560)
                  (ThetaLowerSegment.join cell1901797632 cell1901928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1902059776 cell1902190848)
                  (ThetaLowerSegment.join cell1902321920 cell1902452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1902584064 cell1902715136)
                  (ThetaLowerSegment.join cell1902846208 cell1902977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1903108352 cell1903239424)
                  (ThetaLowerSegment.join cell1903370496 cell1903501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1903632640 cell1903763712)
                  (ThetaLowerSegment.join cell1903894784 cell1904025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1904156928 cell1904288000)
                  (ThetaLowerSegment.join cell1904419072 cell1904550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1904681216 cell1904812288)
                  (ThetaLowerSegment.join cell1904943360 cell1905074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1905205504 cell1905336576)
                  (ThetaLowerSegment.join cell1905467648 cell1905598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1905729792 cell1905860864)
                  (ThetaLowerSegment.join cell1905991936 cell1906123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1906254080 cell1906385152)
                  (ThetaLowerSegment.join cell1906516224 cell1906647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1906778368 cell1906909440)
                  (ThetaLowerSegment.join cell1907040512 cell1907171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1907302656 cell1907433728)
                  (ThetaLowerSegment.join cell1907564800 cell1907695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1907826944 cell1907958016)
                  (ThetaLowerSegment.join cell1908089088 cell1908220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1908351232 cell1908482304)
                  (ThetaLowerSegment.join cell1908613376 cell1908744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1908875520 cell1909006592)
                  (ThetaLowerSegment.join cell1909137664 cell1909268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1909399808 cell1909530880)
                  (ThetaLowerSegment.join cell1909661952 cell1909793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1909924096 cell1910055168)
                  (ThetaLowerSegment.join cell1910186240 cell1910317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1910448384 cell1910579456)
                  (ThetaLowerSegment.join cell1910710528 cell1910841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1910972672 cell1911103744)
                  (ThetaLowerSegment.join cell1911234816 cell1911365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1911496960 cell1911628032)
                  (ThetaLowerSegment.join cell1911759104 cell1911890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1912021248 cell1912152320)
                  (ThetaLowerSegment.join cell1912283392 cell1912414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1912545536 cell1912676608)
                  (ThetaLowerSegment.join cell1912807680 cell1912938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1913069824 cell1913200896)
                  (ThetaLowerSegment.join cell1913331968 cell1913463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1913594112 cell1913725184)
                  (ThetaLowerSegment.join cell1913856256 cell1913987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1914118400 cell1914249472)
                  (ThetaLowerSegment.join cell1914380544 cell1914511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1914642688 cell1914773760)
                  (ThetaLowerSegment.join cell1914904832 cell1915035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1915166976 cell1915298048)
                  (ThetaLowerSegment.join cell1915429120 cell1915560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1915691264 cell1915822336)
                  (ThetaLowerSegment.join cell1915953408 cell1916084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1916215552 cell1916346624)
                  (ThetaLowerSegment.join cell1916477696 cell1916608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1916739840 cell1916870912)
                  (ThetaLowerSegment.join cell1917001984 cell1917133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1917264128 cell1917395200)
                  (ThetaLowerSegment.join cell1917526272 cell1917657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1917788416 cell1917919488)
                  (ThetaLowerSegment.join cell1918050560 cell1918181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1918312704 cell1918443776)
                  (ThetaLowerSegment.join cell1918574848 cell1918705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1918836992 cell1918968064)
                  (ThetaLowerSegment.join cell1919099136 cell1919230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1919361280 cell1919492352)
                  (ThetaLowerSegment.join cell1919623424 cell1919754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1919885568 cell1920016640)
                  (ThetaLowerSegment.join cell1920147712 cell1920278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1920409856 cell1920540928)
                  (ThetaLowerSegment.join cell1920672000 cell1920803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1920934144 cell1921065216)
                  (ThetaLowerSegment.join cell1921196288 cell1921327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1921458432 cell1921589504)
                  (ThetaLowerSegment.join cell1921720576 cell1921851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1921982720 cell1922113792)
                  (ThetaLowerSegment.join cell1922244864 cell1922375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1922507008 cell1922638080)
                  (ThetaLowerSegment.join cell1922769152 cell1922900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1923031296 cell1923162368)
                  (ThetaLowerSegment.join cell1923293440 cell1923424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1923555584 cell1923686656)
                  (ThetaLowerSegment.join cell1923817728 cell1923948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1924079872 cell1924210944)
                  (ThetaLowerSegment.join cell1924342016 cell1924473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1924604160 cell1924735232)
                  (ThetaLowerSegment.join cell1924866304 cell1924997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1925128448 cell1925259520)
                  (ThetaLowerSegment.join cell1925390592 cell1925521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1925652736 cell1925783808)
                  (ThetaLowerSegment.join cell1925914880 cell1926045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1926177024 cell1926308096)
                  (ThetaLowerSegment.join cell1926439168 cell1926570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1926701312 cell1926832384)
                  (ThetaLowerSegment.join cell1926963456 cell1927094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1927225600 cell1927356672)
                  (ThetaLowerSegment.join cell1927487744 cell1927618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1927749888 cell1927880960)
                  (ThetaLowerSegment.join cell1928012032 cell1928143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1928274176 cell1928405248)
                  (ThetaLowerSegment.join cell1928536320 cell1928667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1928798464 cell1928929536)
                (ThetaLowerSegment.join cell1929060608 cell1929191680))
              (ThetaLowerSegment.join cell1929322752 cell1929339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
