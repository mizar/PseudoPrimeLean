/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1513341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1481341184 :
    ThetaLowerSegment 1481341184 1481472256 (74064497890991 / 50000) (74071120987121 / 50000) := by
  exact
    packedTile65536 1481341184 1481472256 14 6273 38488 30 _ _ (105581 / 5000) (2111623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481472256 :
    ThetaLowerSegment 1481472256 1481603328 (74071120987121 / 50000)
      (148155277060059 / 100000) := by
  exact
    packedTile65536 1481472256 1481603328 14 6173 38489 30 _ _ (2111629 / 100000) (131977 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481603328 :
    ThetaLowerSegment 1481603328 1481734400 (148155277060059 / 100000)
      (29633659906321 / 20000) := by
  exact
    packedTile65536 1481603328 1481734400 14 6167 38491 30 _ _ (1055819 / 50000) (2111641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481734400 :
    ThetaLowerSegment 1481734400 1481865472 (29633659906321 / 20000)
      (148181480425937 / 100000) := by
  exact
    packedTile65536 1481734400 1481865472 14 6242 38493 30 _ _ (1055823 / 50000) (2111649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481865472 :
    ThetaLowerSegment 1481865472 1481996544 (148181480425937 / 100000)
      (148194424871087 / 100000) := by
  exact
    packedTile65536 1481865472 1481996544 14 6130 38495 30 _ _ (422331 / 20000) (1055829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481996544 :
    ThetaLowerSegment 1481996544 1482127616 (148194424871087 / 100000)
      (148207483401263 / 100000) := by
  exact
    packedTile65536 1481996544 1482127616 14 6184 38496 30 _ _ (131979 / 6250) (2111667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482127616 :
    ThetaLowerSegment 1482127616 1482258688 (148207483401263 / 100000)
      (148220630677361 / 100000) := by
  exact
    packedTile65536 1482127616 1482258688 14 6226 38498 30 _ _ (2111673 / 100000) (527919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482258688 :
    ThetaLowerSegment 1482258688 1482389760 (148220630677361 / 100000)
      (29646749689189 / 20000) := by
  exact
    packedTile65536 1482258688 1482389760 14 6212 38500 30 _ _ (1055841 / 50000) (422337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482389760 :
    ThetaLowerSegment 1482389760 1482520832 (29646749689189 / 20000) (14824687260551 / 10000) := by
  exact
    packedTile65536 1482389760 1482520832 14 6215 38501 30 _ _ (2111691 / 100000) (1055847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482520832 :
    ThetaLowerSegment 1482520832 1482651904 (14824687260551 / 10000) (37064992340677 / 25000) := by
  exact
    packedTile65536 1482520832 1482651904 14 6202 38503 30 _ _ (2111699 / 100000) (1055851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482651904 :
    ThetaLowerSegment 1482651904 1482782976 (37064992340677 / 25000) (18534145150323 / 12500) := by
  exact
    packedTile65536 1482651904 1482782976 14 6247 38505 30 _ _ (527927 / 25000) (2111711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482782976 :
    ThetaLowerSegment 1482782976 1482914048 (18534145150323 / 12500) (18535779619281 / 12500) := by
  exact
    packedTile65536 1482782976 1482914048 14 6192 38506 30 _ _ (2111717 / 100000) (52793 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482914048 :
    ThetaLowerSegment 1482914048 1483045120 (18535779619281 / 12500) (7414968805671 / 5000) := by
  exact
    packedTile65536 1482914048 1483045120 14 6222 38508 30 _ _ (1055863 / 50000) (2111729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483045120 :
    ThetaLowerSegment 1483045120 1483176192 (7414968805671 / 5000) (926953194407 / 625) := by
  exact
    packedTile65536 1483045120 1483176192 14 6220 38510 30 _ _ (422347 / 20000) (1055869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483176192 :
    ThetaLowerSegment 1483176192 1483307264 (926953194407 / 625) (4635174528507 / 3125) := by
  exact
    packedTile65536 1483176192 1483307264 14 6191 38512 30 _ _ (65992 / 3125) (2111747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483307264 :
    ThetaLowerSegment 1483307264 1483438336 (4635174528507 / 3125) (37084680003971 / 25000) := by
  exact
    packedTile65536 1483307264 1483438336 14 6220 38513 30 _ _ (2111753 / 100000) (527939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483438336 :
    ThetaLowerSegment 1483438336 1483569408 (37084680003971 / 25000) (18543998790251 / 12500) := by
  exact
    packedTile65536 1483438336 1483569408 14 6284 38515 30 _ _ (2111761 / 100000) (527941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483569408 :
    ThetaLowerSegment 1483569408 1483700480 (18543998790251 / 12500) (74182517362649 / 50000) := by
  exact
    packedTile65536 1483569408 1483700480 14 6177 38517 30 _ _ (211177 / 10000) (2111773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483700480 :
    ThetaLowerSegment 1483700480 1483831552 (74182517362649 / 50000)
      (148378066513507 / 100000) := by
  exact
    packedTile65536 1483700480 1483831552 14 6171 38518 30 _ _ (2111779 / 100000) (1055891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483831552 :
    ThetaLowerSegment 1483831552 1483962624 (148378066513507 / 100000) (237425723583 / 160) := by
  exact
    packedTile65536 1483831552 1483962624 14 6161 38520 30 _ _ (527947 / 25000) (2111791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1483962624 :
    ThetaLowerSegment 1483962624 1484093696 (237425723583 / 160) (18550528952861 / 12500) := by
  exact
    packedTile65536 1483962624 1484093696 14 6229 38522 30 _ _ (2111797 / 100000) (10559 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484093696 :
    ThetaLowerSegment 1484093696 1484224768 (18550528952861 / 12500) (74208724708321 / 50000) := by
  exact
    packedTile65536 1484093696 1484224768 14 6259 38523 30 _ _ (1055903 / 50000) (2111809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484224768 :
    ThetaLowerSegment 1484224768 1484355840 (74208724708321 / 50000) (4638450036622 / 3125) := by
  exact
    packedTile65536 1484224768 1484355840 14 6133 38525 30 _ _ (1055907 / 50000) (2111817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484355840 :
    ThetaLowerSegment 1484355840 1484486912 (4638450036622 / 3125) (148443496586327 / 100000) := by
  exact
    packedTile65536 1484355840 1484486912 14 6201 38527 30 _ _ (2111823 / 100000) (1055913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484486912 :
    ThetaLowerSegment 1484486912 1484617984 (148443496586327 / 100000)
      (148456589944727 / 100000) := by
  exact
    packedTile65536 1484486912 1484617984 14 6200 38529 30 _ _ (263979 / 12500) (422367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484617984 :
    ThetaLowerSegment 1484617984 1484749056 (148456589944727 / 100000)
      (74234794163041 / 50000) := by
  exact
    packedTile65536 1484617984 1484749056 14 6155 38530 30 _ _ (2111841 / 100000) (527961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484749056 :
    ThetaLowerSegment 1484749056 1484880128 (74234794163041 / 50000) (18560358190879 / 12500) := by
  exact
    packedTile65536 1484749056 1484880128 14 6287 38532 30 _ _ (42237 / 2000) (2111853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1484880128 :
    ThetaLowerSegment 1484880128 1485011200 (18560358190879 / 12500) (9281008527669 / 6250) := by
  exact
    packedTile65536 1484880128 1485011200 14 6284 38534 30 _ _ (1055929 / 50000) (2111861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485011200 :
    ThetaLowerSegment 1485011200 1485142272 (9281008527669 / 6250) (29701847270741 / 20000) := by
  exact
    packedTile65536 1485011200 1485142272 14 6203 38535 30 _ _ (2111867 / 100000) (211187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485142272 :
    ThetaLowerSegment 1485142272 1485273344 (29701847270741 / 20000)
      (148522239174237 / 100000) := by
  exact
    packedTile65536 1485142272 1485273344 14 6157 38537 30 _ _ (527969 / 25000) (2111879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485273344 :
    ThetaLowerSegment 1485273344 1485404416 (148522239174237 / 100000)
      (148535353980087 / 100000) := by
  exact
    packedTile65536 1485273344 1485404416 14 6210 38539 30 _ _ (422377 / 20000) (131993 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485404416 :
    ThetaLowerSegment 1485404416 1485535488 (148535353980087 / 100000)
      (29709698836911 / 20000) := by
  exact
    packedTile65536 1485404416 1485535488 14 6222 38540 30 _ _ (1055947 / 50000) (2111897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485535488 :
    ThetaLowerSegment 1485535488 1485666560 (29709698836911 / 20000) (18570205625567 / 12500) := by
  exact
    packedTile65536 1485535488 1485666560 14 6227 38542 30 _ _ (2111903 / 100000) (1055953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485666560 :
    ThetaLowerSegment 1485666560 1485797632 (18570205625567 / 12500) (74287379985923 / 50000) := by
  exact
    packedTile65536 1485666560 1485797632 14 6210 38544 30 _ _ (2111911 / 100000) (1055957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485797632 :
    ThetaLowerSegment 1485797632 1485928704 (74287379985923 / 50000) (74293919546203 / 50000) := by
  exact
    packedTile65536 1485797632 1485928704 14 6193 38546 30 _ _ (26399 / 1250) (2111923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1485928704 :
    ThetaLowerSegment 1485928704 1486059776 (74293919546203 / 50000) (74300500316967 / 50000) := by
  exact
    packedTile65536 1485928704 1486059776 14 6232 38547 30 _ _ (2111929 / 100000) (527983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486059776 :
    ThetaLowerSegment 1486059776 1486190848 (74300500316967 / 50000) (7430701247779 / 5000) := by
  exact
    packedTile65536 1486059776 1486190848 14 6167 38549 30 _ _ (1055969 / 50000) (2111941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486190848 :
    ThetaLowerSegment 1486190848 1486321920 (7430701247779 / 5000) (148627197169019 / 100000) := by
  exact
    packedTile65536 1486190848 1486321920 14 6237 38551 30 _ _ (2111947 / 100000) (42239 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486321920 :
    ThetaLowerSegment 1486321920 1486452992 (148627197169019 / 100000)
      (148640312415779 / 100000) := by
  exact
    packedTile65536 1486321920 1486452992 14 6210 38552 30 _ _ (527989 / 25000) (2111959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486452992 :
    ThetaLowerSegment 1486452992 1486584064 (148640312415779 / 100000)
      (148653476287391 / 100000) := by
  exact
    packedTile65536 1486452992 1486584064 14 6233 38554 30 _ _ (527991 / 25000) (2111967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486584064 :
    ThetaLowerSegment 1486584064 1486715136 (148653476287391 / 100000)
      (29733355498669 / 20000) := by
  exact
    packedTile65536 1486584064 1486715136 14 6298 38556 30 _ _ (2111973 / 100000) (263997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486715136 :
    ThetaLowerSegment 1486715136 1486846208 (29733355498669 / 20000)
      (148679846437961 / 100000) := by
  exact
    packedTile65536 1486715136 1486846208 14 6188 38557 30 _ _ (1055991 / 50000) (422397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486846208 :
    ThetaLowerSegment 1486846208 1486977280 (148679846437961 / 100000) (7434654325477 / 5000) := by
  exact
    packedTile65536 1486846208 1486977280 14 6269 38559 30 _ _ (2111991 / 100000) (1055997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1486977280 :
    ThetaLowerSegment 1486977280 1487108352 (7434654325477 / 5000) (7435315592677 / 5000) := by
  exact
    packedTile65536 1486977280 1487108352 14 6262 38561 30 _ _ (528 / 25) (2112003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487108352 :
    ThetaLowerSegment 1487108352 1487239424 (7435315592677 / 5000) (37179862663827 / 25000) := by
  exact
    packedTile65536 1487108352 1487239424 14 6221 38563 30 _ _ (264001 / 12500) (2112011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487239424 :
    ThetaLowerSegment 1487239424 1487370496 (37179862663827 / 25000) (18591569201097 / 12500) := by
  exact
    packedTile65536 1487239424 1487370496 14 6204 38564 30 _ _ (2112017 / 100000) (105601 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487370496 :
    ThetaLowerSegment 1487370496 1487501568 (18591569201097 / 12500) (74372799796689 / 50000) := by
  exact
    packedTile65536 1487370496 1487501568 14 6177 38566 30 _ _ (1056013 / 50000) (2112029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487501568 :
    ThetaLowerSegment 1487501568 1487632640 (74372799796689 / 50000) (9297422876223 / 6250) := by
  exact
    packedTile65536 1487501568 1487632640 14 6234 38568 30 _ _ (422407 / 20000) (1056019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487632640 :
    ThetaLowerSegment 1487632640 1487763712 (9297422876223 / 6250) (37192947748729 / 25000) := by
  exact
    packedTile65536 1487632640 1487763712 14 6167 38569 30 _ _ (528011 / 25000) (2112047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487763712 :
    ThetaLowerSegment 1487763712 1487894784 (37192947748729 / 25000) (37196262614343 / 25000) := by
  exact
    packedTile65536 1487763712 1487894784 14 6278 38571 30 _ _ (528013 / 25000) (422411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487894784 :
    ThetaLowerSegment 1487894784 1488025856 (37196262614343 / 25000) (37199553205381 / 25000) := by
  exact
    packedTile65536 1487894784 1488025856 14 6232 38573 30 _ _ (2112061 / 100000) (66002 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488025856 :
    ThetaLowerSegment 1488025856 1488156928 (37199553205381 / 25000) (74405673892427 / 50000) := by
  exact
    packedTile65536 1488025856 1488156928 14 6219 38574 30 _ _ (211207 / 10000) (2112073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488156928 :
    ThetaLowerSegment 1488156928 1488288000 (74405673892427 / 50000) (4650767925736 / 3125) := by
  exact
    packedTile65536 1488156928 1488288000 14 6262 38576 30 _ _ (2112079 / 100000) (1056041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488288000 :
    ThetaLowerSegment 1488288000 1488419072 (4650767925736 / 3125) (4651176350753 / 3125) := by
  exact
    packedTile65536 1488288000 1488419072 14 6188 38578 30 _ _ (264011 / 12500) (2112091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488419072 :
    ThetaLowerSegment 1488419072 1488550144 (4651176350753 / 3125) (29770180171393 / 20000) := by
  exact
    packedTile65536 1488419072 1488550144 14 6277 38580 30 _ _ (2112097 / 100000) (21121 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488550144 :
    ThetaLowerSegment 1488550144 1488681216 (29770180171393 / 20000) (5954554091393 / 4000) := by
  exact
    packedTile65536 1488550144 1488681216 14 6132 38581 30 _ _ (422421 / 20000) (528027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488681216 :
    ThetaLowerSegment 1488681216 1488812288 (5954554091393 / 4000) (148876913597801 / 100000) := by
  exact
    packedTile65536 1488681216 1488812288 14 6184 38583 30 _ _ (1056057 / 50000) (2112117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488812288 :
    ThetaLowerSegment 1488812288 1488943360 (148876913597801 / 100000)
      (148890055227107 / 100000) := by
  exact
    packedTile65536 1488812288 1488943360 14 6222 38585 30 _ _ (2112123 / 100000) (1056063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1488943360 :
    ThetaLowerSegment 1488943360 1489074432 (148890055227107 / 100000)
      (148903186351751 / 100000) := by
  exact
    packedTile65536 1488943360 1489074432 14 6217 38586 30 _ _ (528033 / 25000) (422427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489074432 :
    ThetaLowerSegment 1489074432 1489205504 (148903186351751 / 100000) (4653632018692 / 3125) := by
  exact
    packedTile65536 1489074432 1489205504 14 6173 38588 30 _ _ (2112141 / 100000) (132009 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489205504 :
    ThetaLowerSegment 1489205504 1489336576 (4653632018692 / 3125) (148929237548133 / 100000) := by
  exact
    packedTile65536 1489205504 1489336576 14 6161 38590 30 _ _ (2112149 / 100000) (264019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489336576 :
    ThetaLowerSegment 1489336576 1489467648 (148929237548133 / 100000)
      (148942294908889 / 100000) := by
  exact
    packedTile65536 1489336576 1489467648 14 6182 38591 30 _ _ (1056079 / 50000) (2112161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489467648 :
    ThetaLowerSegment 1489467648 1489598720 (148942294908889 / 100000) (9309715196779 / 6250) := by
  exact
    packedTile65536 1489467648 1489598720 14 6225 38593 30 _ _ (2112167 / 100000) (211217 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489598720 :
    ThetaLowerSegment 1489598720 1489729792 (9309715196779 / 6250) (4655263070176 / 3125) := by
  exact
    packedTile65536 1489598720 1489729792 14 6143 38595 30 _ _ (132011 / 6250) (2112179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489729792 :
    ThetaLowerSegment 1489729792 1489860864 (4655263070176 / 3125) (148981515904817 / 100000) := by
  exact
    packedTile65536 1489729792 1489860864 14 6201 38597 30 _ _ (422437 / 20000) (528047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489860864 :
    ThetaLowerSegment 1489860864 1489991936 (148981515904817 / 100000)
      (74497315255577 / 50000) := by
  exact
    packedTile65536 1489860864 1489991936 14 6209 38598 30 _ _ (2112193 / 100000) (528049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1489991936 :
    ThetaLowerSegment 1489991936 1490123008 (74497315255577 / 50000) (37251913059121 / 25000) := by
  exact
    packedTile65536 1489991936 1490123008 14 6165 38600 30 _ _ (1056101 / 50000) (422441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490123008 :
    ThetaLowerSegment 1490123008 1490254080 (37251913059121 / 25000)
      (149020699363831 / 100000) := by
  exact
    packedTile65536 1490123008 1490254080 14 6177 38602 30 _ _ (2112211 / 100000) (1056107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490254080 :
    ThetaLowerSegment 1490254080 1490385152 (149020699363831 / 100000)
      (149033934534351 / 100000) := by
  exact
    packedTile65536 1490254080 1490385152 14 6266 38603 30 _ _ (105611 / 5000) (2112223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490385152 :
    ThetaLowerSegment 1490385152 1490516224 (149033934534351 / 100000)
      (18630890675557 / 12500) := by
  exact
    packedTile65536 1490385152 1490516224 14 6245 38605 30 _ _ (2112229 / 100000) (264029 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490516224 :
    ThetaLowerSegment 1490516224 1490647296 (18630890675557 / 12500)
      (149060379691631 / 100000) := by
  exact
    packedTile65536 1490516224 1490647296 14 6275 38607 30 _ _ (2112237 / 100000) (26403 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490647296 :
    ThetaLowerSegment 1490647296 1490778368 (149060379691631 / 100000)
      (149073646708757 / 100000) := by
  exact
    packedTile65536 1490647296 1490778368 14 6281 38608 30 _ _ (1056123 / 50000) (2112249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490778368 :
    ThetaLowerSegment 1490778368 1490909440 (149073646708757 / 100000)
      (149086835628977 / 100000) := by
  exact
    packedTile65536 1490778368 1490909440 14 6244 38610 30 _ _ (422451 / 20000) (1056129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1490909440 :
    ThetaLowerSegment 1490909440 1491040512 (149086835628977 / 100000)
      (149100003482753 / 100000) := by
  exact
    packedTile65536 1490909440 1491040512 14 6234 38612 30 _ _ (264033 / 12500) (2112267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491040512 :
    ThetaLowerSegment 1491040512 1491171584 (149100003482753 / 100000)
      (74556588864727 / 50000) := by
  exact
    packedTile65536 1491040512 1491171584 14 6237 38613 30 _ _ (2112273 / 100000) (528069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491171584 :
    ThetaLowerSegment 1491171584 1491302656 (74556588864727 / 50000) (37281546288963 / 25000) := by
  exact
    packedTile65536 1491171584 1491302656 14 6158 38615 30 _ _ (2112281 / 100000) (528071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491302656 :
    ThetaLowerSegment 1491302656 1491433728 (37281546288963 / 25000) (4660601618181 / 3125) := by
  exact
    packedTile65536 1491302656 1491433728 14 6186 38617 30 _ _ (211229 / 10000) (2112293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491433728 :
    ThetaLowerSegment 1491433728 1491564800 (4660601618181 / 3125) (29830464115141 / 20000) := by
  exact
    packedTile65536 1491433728 1491564800 14 6187 38619 30 _ _ (2112299 / 100000) (1056151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491564800 :
    ThetaLowerSegment 1491564800 1491695872 (29830464115141 / 20000)
      (149165461243773 / 100000) := by
  exact
    packedTile65536 1491564800 1491695872 14 6221 38620 30 _ _ (528077 / 25000) (2112311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491695872 :
    ThetaLowerSegment 1491695872 1491826944 (149165461243773 / 100000)
      (29835712365521 / 20000) := by
  exact
    packedTile65536 1491695872 1491826944 14 6202 38622 30 _ _ (528079 / 25000) (2112319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491826944 :
    ThetaLowerSegment 1491826944 1491958016 (29835712365521 / 20000) (14919152516613 / 10000) := by
  exact
    packedTile65536 1491826944 1491958016 14 6137 38624 30 _ _ (84493 / 4000) (264041 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491958016 :
    ThetaLowerSegment 1491958016 1492089088 (14919152516613 / 10000) (74602431221503 / 50000) := by
  exact
    packedTile65536 1491958016 1492089088 14 6314 38625 30 _ _ (1056167 / 50000) (2112337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492089088 :
    ThetaLowerSegment 1492089088 1492220160 (74602431221503 / 50000) (29843601510699 / 20000) := by
  exact
    packedTile65536 1492089088 1492220160 14 6223 38627 30 _ _ (2112343 / 100000) (1056173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492220160 :
    ThetaLowerSegment 1492220160 1492351232 (29843601510699 / 20000)
      (149231184405271 / 100000) := by
  exact
    packedTile65536 1492220160 1492351232 14 6238 38629 30 _ _ (66011 / 3125) (422471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492351232 :
    ThetaLowerSegment 1492351232 1492482304 (149231184405271 / 100000)
      (149244266250751 / 100000) := by
  exact
    packedTile65536 1492351232 1492482304 14 6193 38630 30 _ _ (52809 / 2500) (2112363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492482304 :
    ThetaLowerSegment 1492482304 1492613376 (149244266250751 / 100000)
      (74628697312043 / 50000) := by
  exact
    packedTile65536 1492482304 1492613376 14 6215 38632 30 _ _ (2112369 / 100000) (528093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492613376 :
    ThetaLowerSegment 1492613376 1492744448 (74628697312043 / 50000) (18658812741197 / 12500) := by
  exact
    packedTile65536 1492613376 1492744448 14 6205 38634 30 _ _ (1056189 / 50000) (2112381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492744448 :
    ThetaLowerSegment 1492744448 1492875520 (18658812741197 / 12500) (18660435054413 / 12500) := by
  exact
    packedTile65536 1492744448 1492875520 14 6144 38636 30 _ _ (2112387 / 100000) (211239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1492875520 :
    ThetaLowerSegment 1492875520 1493006592 (18660435054413 / 12500) (37324197130951 / 25000) := by
  exact
    packedTile65536 1492875520 1493006592 14 6300 38637 30 _ _ (422479 / 20000) (1056199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493006592 :
    ThetaLowerSegment 1493006592 1493137664 (37324197130951 / 25000) (4665932665404 / 3125) := by
  exact
    packedTile65536 1493006592 1493137664 14 6181 38639 30 _ _ (528101 / 25000) (2112407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493137664 :
    ThetaLowerSegment 1493137664 1493268736 (4665932665404 / 3125) (37330767249577 / 25000) := by
  exact
    packedTile65536 1493137664 1493268736 14 6260 38641 30 _ _ (2112413 / 100000) (66013 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493268736 :
    ThetaLowerSegment 1493268736 1493399808 (37330767249577 / 25000) (9333511696183 / 6250) := by
  exact
    packedTile65536 1493268736 1493399808 14 6210 38642 30 _ _ (1056211 / 50000) (84497 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493399808 :
    ThetaLowerSegment 1493399808 1493530880 (9333511696183 / 6250) (9334331319411 / 6250) := by
  exact
    packedTile65536 1493399808 1493530880 14 6208 38644 30 _ _ (2112431 / 100000) (1056217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493530880 :
    ThetaLowerSegment 1493530880 1493661952 (9334331319411 / 6250) (149362467942863 / 100000) := by
  exact
    packedTile65536 1493530880 1493661952 14 6233 38646 30 _ _ (2112439 / 100000) (1056221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493661952 :
    ThetaLowerSegment 1493661952 1493793024 (149362467942863 / 100000)
      (149375503859471 / 100000) := by
  exact
    packedTile65536 1493661952 1493793024 14 6171 38647 30 _ _ (66014 / 3125) (2112451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493793024 :
    ThetaLowerSegment 1493793024 1493924096 (149375503859471 / 100000)
      (74694303715121 / 50000) := by
  exact
    packedTile65536 1493793024 1493924096 14 6203 38649 30 _ _ (2112457 / 100000) (105623 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1493924096 :
    ThetaLowerSegment 1493924096 1494055168 (74694303715121 / 50000) (37350420370579 / 25000) := by
  exact
    packedTile65536 1493924096 1494055168 14 6189 38651 30 _ _ (1056233 / 50000) (2112469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494055168 :
    ThetaLowerSegment 1494055168 1494186240 (37350420370579 / 25000) (74707407366587 / 50000) := by
  exact
    packedTile65536 1494055168 1494186240 14 6217 38653 30 _ _ (1056237 / 50000) (2112477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494186240 :
    ThetaLowerSegment 1494186240 1494317312 (74707407366587 / 50000) (14942789522791 / 10000) := by
  exact
    packedTile65536 1494186240 1494317312 14 6192 38654 30 _ _ (2112483 / 100000) (1056243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494317312 :
    ThetaLowerSegment 1494317312 1494448384 (14942789522791 / 10000) (74720545982717 / 50000) := by
  exact
    packedTile65536 1494317312 1494448384 14 6247 38656 30 _ _ (528123 / 25000) (422499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494448384 :
    ThetaLowerSegment 1494448384 1494579456 (74720545982717 / 50000) (29890859441837 / 20000) := by
  exact
    packedTile65536 1494448384 1494579456 14 6251 38658 30 _ _ (2112501 / 100000) (264063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494579456 :
    ThetaLowerSegment 1494579456 1494710528 (29890859441837 / 20000) (29893492051799 / 20000) := by
  exact
    packedTile65536 1494579456 1494710528 14 6231 38659 30 _ _ (211251 / 10000) (2112513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494710528 :
    ThetaLowerSegment 1494710528 1494841600 (29893492051799 / 20000) (29896122136709 / 20000) := by
  exact
    packedTile65536 1494710528 1494841600 14 6225 38661 30 _ _ (1056259 / 50000) (2112521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494841600 :
    ThetaLowerSegment 1494841600 1494972672 (29896122136709 / 20000)
      (149493822427403 / 100000) := by
  exact
    packedTile65536 1494841600 1494972672 14 6254 38663 30 _ _ (2112527 / 100000) (211253 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1494972672 :
    ThetaLowerSegment 1494972672 1495103744 (149493822427403 / 100000)
      (149506875787347 / 100000) := by
  exact
    packedTile65536 1494972672 1495103744 14 6179 38664 30 _ _ (264067 / 12500) (2112539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495103744 :
    ThetaLowerSegment 1495103744 1495234816 (149506875787347 / 100000)
      (74760006852351 / 50000) := by
  exact
    packedTile65536 1495103744 1495234816 14 6219 38666 30 _ _ (422509 / 20000) (528137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495234816 :
    ThetaLowerSegment 1495234816 1495365888 (74760006852351 / 50000) (74766521965803 / 50000) := by
  exact
    packedTile65536 1495234816 1495365888 14 6168 38668 30 _ _ (2112553 / 100000) (528139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495365888 :
    ThetaLowerSegment 1495365888 1495496960 (74766521965803 / 50000) (14954610378989 / 10000) := by
  exact
    packedTile65536 1495365888 1495496960 14 6182 38669 30 _ _ (1056281 / 50000) (422513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495496960 :
    ThetaLowerSegment 1495496960 1495628032 (14954610378989 / 10000)
      (149559368623199 / 100000) := by
  exact
    packedTile65536 1495496960 1495628032 14 6279 38671 30 _ _ (2112571 / 100000) (1056287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495628032 :
    ThetaLowerSegment 1495628032 1495759104 (149559368623199 / 100000)
      (149572363102779 / 100000) := by
  exact
    packedTile65536 1495628032 1495759104 14 6151 38673 30 _ _ (105629 / 5000) (2112583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495759104 :
    ThetaLowerSegment 1495759104 1495890176 (149572363102779 / 100000)
      (29917084624359 / 20000) := by
  exact
    packedTile65536 1495759104 1495890176 14 6182 38675 30 _ _ (528147 / 25000) (2112591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495890176 :
    ThetaLowerSegment 1495890176 1496021248 (29917084624359 / 20000) (18699813304377 / 12500) := by
  exact
    packedTile65536 1495890176 1496021248 14 6193 38676 30 _ _ (2112597 / 100000) (10563 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496021248 :
    ThetaLowerSegment 1496021248 1496152320 (18699813304377 / 12500) (18701452686633 / 12500) := by
  exact
    packedTile65536 1496021248 1496152320 14 6208 38678 30 _ _ (1056303 / 50000) (2112609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496152320 :
    ThetaLowerSegment 1496152320 1496283392 (18701452686633 / 12500)
      (149624802098049 / 100000) := by
  exact
    packedTile65536 1496152320 1496283392 14 6239 38680 30 _ _ (422523 / 20000) (1056309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496283392 :
    ThetaLowerSegment 1496283392 1496414464 (149624802098049 / 100000)
      (149637864452241 / 100000) := by
  exact
    packedTile65536 1496283392 1496414464 14 6183 38681 30 _ _ (132039 / 6250) (2112627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496414464 :
    ThetaLowerSegment 1496414464 1496545536 (149637864452241 / 100000)
      (149651119105409 / 100000) := by
  exact
    packedTile65536 1496414464 1496545536 14 6274 38683 30 _ _ (264079 / 12500) (422527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496545536 :
    ThetaLowerSegment 1496545536 1496676608 (149651119105409 / 100000)
      (149664259732429 / 100000) := by
  exact
    packedTile65536 1496545536 1496676608 14 6220 38685 30 _ _ (2112641 / 100000) (528161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496676608 :
    ThetaLowerSegment 1496676608 1496807680 (149664259732429 / 100000)
      (149677250417279 / 100000) := by
  exact
    packedTile65536 1496676608 1496807680 14 6149 38686 30 _ _ (42253 / 2000) (2112653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496807680 :
    ThetaLowerSegment 1496807680 1496938752 (149677250417279 / 100000)
      (149690429184121 / 100000) := by
  exact
    packedTile65536 1496807680 1496938752 14 6238 38688 30 _ _ (2112659 / 100000) (1056331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1496938752 :
    ThetaLowerSegment 1496938752 1497069824 (149690429184121 / 100000)
      (74851733226089 / 50000) := by
  exact
    packedTile65536 1496938752 1497069824 14 6171 38690 30 _ _ (2112667 / 100000) (211267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497069824 :
    ThetaLowerSegment 1497069824 1497200896 (74851733226089 / 50000) (74858281465351 / 50000) := by
  exact
    packedTile65536 1497069824 1497200896 14 6199 38691 30 _ _ (528169 / 25000) (2112679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497200896 :
    ThetaLowerSegment 1497200896 1497331968 (74858281465351 / 50000)
      (149729803127597 / 100000) := by
  exact
    packedTile65536 1497200896 1497331968 14 6267 38693 30 _ _ (422537 / 20000) (132043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497331968 :
    ThetaLowerSegment 1497331968 1497463040 (149729803127597 / 100000)
      (149742918731949 / 100000) := by
  exact
    packedTile65536 1497331968 1497463040 14 6208 38695 30 _ _ (1056347 / 50000) (2112697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497463040 :
    ThetaLowerSegment 1497463040 1497594112 (149742918731949 / 100000)
      (29951206877193 / 20000) := by
  exact
    packedTile65536 1497463040 1497594112 14 6208 38697 30 _ _ (1056351 / 50000) (422541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497594112 :
    ThetaLowerSegment 1497594112 1497725184 (29951206877193 / 20000) (74884565540727 / 50000) := by
  exact
    packedTile65536 1497594112 1497725184 14 6199 38698 30 _ _ (2112711 / 100000) (1056357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497725184 :
    ThetaLowerSegment 1497725184 1497856256 (74884565540727 / 50000) (74891097014607 / 50000) := by
  exact
    packedTile65536 1497725184 1497856256 14 6183 38700 30 _ _ (26409 / 1250) (2112723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497856256 :
    ThetaLowerSegment 1497856256 1497987328 (74891097014607 / 50000) (29959070843631 / 20000) := by
  exact
    packedTile65536 1497856256 1497987328 14 6229 38702 30 _ _ (2112729 / 100000) (528183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1497987328 :
    ThetaLowerSegment 1497987328 1498118400 (29959070843631 / 20000)
      (149808541922509 / 100000) := by
  exact
    packedTile65536 1497987328 1498118400 14 6242 38703 30 _ _ (2112737 / 100000) (105637 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498118400 :
    ThetaLowerSegment 1498118400 1498249472 (149808541922509 / 100000)
      (29964313822869 / 20000) := by
  exact
    packedTile65536 1498118400 1498249472 14 6166 38705 30 _ _ (1056373 / 50000) (2112749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498249472 :
    ThetaLowerSegment 1498249472 1498380544 (29964313822869 / 20000) (14983468298463 / 10000) := by
  exact
    packedTile65536 1498249472 1498380544 14 6207 38707 30 _ _ (422551 / 20000) (1056379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498380544 :
    ThetaLowerSegment 1498380544 1498511616 (14983468298463 / 10000) (14984783494053 / 10000) := by
  exact
    packedTile65536 1498380544 1498511616 14 6225 38708 30 _ _ (528191 / 25000) (2112767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498511616 :
    ThetaLowerSegment 1498511616 1498642688 (14984783494053 / 10000) (14986082848833 / 10000) := by
  exact
    packedTile65536 1498511616 1498642688 14 6150 38710 30 _ _ (528193 / 25000) (84511 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498642688 :
    ThetaLowerSegment 1498642688 1498773760 (14986082848833 / 10000) (37468478763461 / 25000) := by
  exact
    packedTile65536 1498642688 1498773760 14 6194 38712 30 _ _ (2112781 / 100000) (132049 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498773760 :
    ThetaLowerSegment 1498773760 1498904832 (37468478763461 / 25000) (74943493442787 / 50000) := by
  exact
    packedTile65536 1498773760 1498904832 14 6187 38713 30 _ _ (211279 / 10000) (2112793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1498904832 :
    ThetaLowerSegment 1498904832 1499035904 (74943493442787 / 50000)
      (149900079900977 / 100000) := by
  exact
    packedTile65536 1498904832 1499035904 14 6197 38715 30 _ _ (2112799 / 100000) (1056401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499035904 :
    ThetaLowerSegment 1499035904 1499166976 (149900079900977 / 100000)
      (14991313493543 / 10000) := by
  exact
    packedTile65536 1499035904 1499166976 14 6179 38717 30 _ _ (2112807 / 100000) (211281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499166976 :
    ThetaLowerSegment 1499166976 1499298048 (14991313493543 / 10000) (74963177412571 / 50000) := by
  exact
    packedTile65536 1499166976 1499298048 14 6257 38719 30 _ _ (132051 / 6250) (2112819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499298048 :
    ThetaLowerSegment 1499298048 1499429120 (74963177412571 / 50000) (37484858302973 / 25000) := by
  exact
    packedTile65536 1499298048 1499429120 14 6190 38720 30 _ _ (84513 / 4000) (528207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499429120 :
    ThetaLowerSegment 1499429120 1499560192 (37484858302973 / 25000) (74976313930111 / 50000) := by
  exact
    packedTile65536 1499429120 1499560192 14 6245 38722 30 _ _ (1056417 / 50000) (2112837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499560192 :
    ThetaLowerSegment 1499560192 1499691264 (74976313930111 / 50000) (1499656408541 / 1000) := by
  exact
    packedTile65536 1499560192 1499691264 14 6159 38724 30 _ _ (1056421 / 50000) (422569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499691264 :
    ThetaLowerSegment 1499691264 1499822336 (1499656408541 / 1000) (18747335171309 / 12500) := by
  exact
    packedTile65536 1499691264 1499822336 14 6172 38725 30 _ _ (2112851 / 100000) (1056427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499822336 :
    ThetaLowerSegment 1499822336 1499953408 (18747335171309 / 12500) (18748967355659 / 12500) := by
  exact
    packedTile65536 1499822336 1499953408 14 6180 38727 30 _ _ (105643 / 5000) (2112863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499953408 :
    ThetaLowerSegment 1499953408 1500084480 (18748967355659 / 12500) (3750121810819 / 2500) := by
  exact
    packedTile65536 1499953408 1500084480 14 6216 38729 30 _ _ (528217 / 25000) (2112871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500084480 :
    ThetaLowerSegment 1500084480 1500215552 (3750121810819 / 2500) (150018016640577 / 100000) := by
  exact
    packedTile65536 1500084480 1500215552 14 6221 38730 30 _ _ (2112877 / 100000) (26411 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500215552 :
    ThetaLowerSegment 1500215552 1500346624 (150018016640577 / 100000)
      (150031184146129 / 100000) := by
  exact
    packedTile65536 1500215552 1500346624 14 6232 38732 30 _ _ (1056443 / 50000) (2112889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500346624 :
    ThetaLowerSegment 1500346624 1500477696 (150031184146129 / 100000)
      (150044224934069 / 100000) := by
  exact
    packedTile65536 1500346624 1500477696 14 6172 38734 30 _ _ (422579 / 20000) (1056449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500477696 :
    ThetaLowerSegment 1500477696 1500608768 (150044224934069 / 100000)
      (75028703667943 / 50000) := by
  exact
    packedTile65536 1500477696 1500608768 14 6239 38736 30 _ _ (2112903 / 100000) (1056453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500608768 :
    ThetaLowerSegment 1500608768 1500739840 (75028703667943 / 50000) (75035258977423 / 50000) := by
  exact
    packedTile65536 1500608768 1500739840 14 6205 38737 30 _ _ (132057 / 6250) (422583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500739840 :
    ThetaLowerSegment 1500739840 1500870912 (75035258977423 / 50000)
      (150083497628549 / 100000) := by
  exact
    packedTile65536 1500739840 1500870912 14 6143 38739 30 _ _ (2112921 / 100000) (528231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1500870912 :
    ThetaLowerSegment 1500870912 1501001984 (150083497628549 / 100000)
      (150096559761809 / 100000) := by
  exact
    packedTile65536 1500870912 1501001984 14 6182 38741 30 _ _ (211293 / 10000) (2112933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501001984 :
    ThetaLowerSegment 1501001984 1501133056 (150096559761809 / 100000)
      (150109605041021 / 100000) := by
  exact
    packedTile65536 1501001984 1501133056 14 6174 38742 30 _ _ (1056469 / 50000) (2112941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501133056 :
    ThetaLowerSegment 1501133056 1501264128 (150109605041021 / 100000)
      (150122891251757 / 100000) := by
  exact
    packedTile65536 1501133056 1501264128 14 6288 38744 30 _ _ (2112947 / 100000) (42259 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501264128 :
    ThetaLowerSegment 1501264128 1501395200 (150122891251757 / 100000)
      (150135949319837 / 100000) := by
  exact
    packedTile65536 1501264128 1501395200 14 6180 38746 30 _ _ (528239 / 25000) (2112959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501395200 :
    ThetaLowerSegment 1501395200 1501526272 (150135949319837 / 100000)
      (150149121543647 / 100000) := by
  exact
    packedTile65536 1501395200 1501526272 14 6234 38747 30 _ _ (422593 / 20000) (264121 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501526272 :
    ThetaLowerSegment 1501526272 1501657344 (150149121543647 / 100000)
      (30032413123249 / 20000) := by
  exact
    packedTile65536 1501526272 1501657344 14 6126 38749 30 _ _ (2112973 / 100000) (132061 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501657344 :
    ThetaLowerSegment 1501657344 1501788416 (30032413123249 / 20000)
      (150175214703231 / 100000) := by
  exact
    packedTile65536 1501657344 1501788416 14 6223 38751 30 _ _ (1056491 / 50000) (422597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501788416 :
    ThetaLowerSegment 1501788416 1501919488 (150175214703231 / 100000)
      (37547050814727 / 25000) := by
  exact
    packedTile65536 1501788416 1501919488 14 6147 38752 30 _ _ (2112991 / 100000) (1056497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1501919488 :
    ThetaLowerSegment 1501919488 1502050560 (37547050814727 / 25000)
      (150201305965707 / 100000) := by
  exact
    packedTile65536 1501919488 1502050560 14 6201 38754 30 _ _ (2112999 / 100000) (1056501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502050560 :
    ThetaLowerSegment 1502050560 1502181632 (150201305965707 / 100000)
      (30042877519647 / 20000) := by
  exact
    packedTile65536 1502050560 1502181632 14 6191 38756 30 _ _ (132063 / 6250) (2113011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502181632 :
    ThetaLowerSegment 1502181632 1502312704 (30042877519647 / 20000)
      (150227374200717 / 100000) := by
  exact
    packedTile65536 1502181632 1502312704 14 6146 38757 30 _ _ (2113017 / 100000) (105651 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502312704 :
    ThetaLowerSegment 1502312704 1502443776 (150227374200717 / 100000)
      (150240525674541 / 100000) := by
  exact
    packedTile65536 1502312704 1502443776 14 6224 38759 30 _ _ (1056513 / 50000) (2113029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502443776 :
    ThetaLowerSegment 1502443776 1502574848 (150240525674541 / 100000)
      (30050717267539 / 20000) := by
  exact
    packedTile65536 1502443776 1502574848 14 6181 38761 30 _ _ (1056517 / 50000) (2113037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502574848 :
    ThetaLowerSegment 1502574848 1502705920 (30050717267539 / 20000)
      (150266653395607 / 100000) := by
  exact
    packedTile65536 1502574848 1502705920 14 6184 38763 30 _ _ (2113043 / 100000) (1056523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502705920 :
    ThetaLowerSegment 1502705920 1502836992 (150266653395607 / 100000)
      (150279811370411 / 100000) := by
  exact
    packedTile65536 1502705920 1502836992 14 6227 38764 30 _ _ (528263 / 25000) (422611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502836992 :
    ThetaLowerSegment 1502836992 1502968064 (150279811370411 / 100000)
      (37573205371747 / 25000) := by
  exact
    packedTile65536 1502836992 1502968064 14 6157 38766 30 _ _ (2113061 / 100000) (264133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1502968064 :
    ThetaLowerSegment 1502968064 1503099136 (37573205371747 / 25000) (75152967596601 / 50000) := by
  exact
    packedTile65536 1502968064 1503099136 14 6206 38768 30 _ _ (2113069 / 100000) (132067 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503099136 :
    ThetaLowerSegment 1503099136 1503230208 (75152967596601 / 50000) (75159549834571 / 50000) := by
  exact
    packedTile65536 1503099136 1503230208 14 6230 38769 30 _ _ (1056539 / 50000) (2113081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503230208 :
    ThetaLowerSegment 1503230208 1503361280 (75159549834571 / 50000) (75166087725749 / 50000) := by
  exact
    packedTile65536 1503230208 1503361280 14 6188 38771 30 _ _ (2113087 / 100000) (211309 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503361280 :
    ThetaLowerSegment 1503361280 1503492352 (75166087725749 / 50000) (37586301198817 / 25000) := by
  exact
    packedTile65536 1503361280 1503492352 14 6166 38773 30 _ _ (422619 / 20000) (1056549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503492352 :
    ThetaLowerSegment 1503492352 1503623424 (37586301198817 / 25000) (37589577566569 / 25000) := by
  exact
    packedTile65536 1503492352 1503623424 14 6202 38774 30 _ _ (132069 / 6250) (2113107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503623424 :
    ThetaLowerSegment 1503623424 1503754496 (37589577566569 / 25000) (75185712122777 / 50000) := by
  exact
    packedTile65536 1503623424 1503754496 14 6206 38776 30 _ _ (2113113 / 100000) (528279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503754496 :
    ThetaLowerSegment 1503754496 1503885568 (75185712122777 / 50000) (37596119250037 / 25000) := by
  exact
    packedTile65536 1503754496 1503885568 14 6177 38778 30 _ _ (1056561 / 50000) (3381 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503885568 :
    ThetaLowerSegment 1503885568 1504016640 (37596119250037 / 25000) (75198760675819 / 50000) := by
  exact
    packedTile65536 1503885568 1504016640 14 6173 38779 30 _ _ (211313 / 10000) (2113133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504016640 :
    ThetaLowerSegment 1504016640 1504147712 (75198760675819 / 50000)
      (150410806656531 / 100000) := by
  exact
    packedTile65536 1504016640 1504147712 14 6287 38781 30 _ _ (2113139 / 100000) (1056571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504147712 :
    ThetaLowerSegment 1504147712 1504278784 (150410806656531 / 100000)
      (150424005378939 / 100000) := by
  exact
    packedTile65536 1504147712 1504278784 14 6246 38783 30 _ _ (528287 / 25000) (2113151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504278784 :
    ThetaLowerSegment 1504278784 1504409856 (150424005378939 / 100000)
      (150437322488051 / 100000) := by
  exact
    packedTile65536 1504278784 1504409856 14 6302 38785 30 _ _ (528289 / 25000) (2113159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504409856 :
    ThetaLowerSegment 1504409856 1504540928 (150437322488051 / 100000)
      (150450453695361 / 100000) := by
  exact
    packedTile65536 1504409856 1504540928 14 6214 38786 30 _ _ (422633 / 20000) (132073 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504540928 :
    ThetaLowerSegment 1504540928 1504672000 (150450453695361 / 100000) (6018541031589 / 4000) := by
  exact
    packedTile65536 1504540928 1504672000 14 6186 38788 30 _ _ (1056587 / 50000) (2113177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504672000 :
    ThetaLowerSegment 1504672000 1504803072 (6018541031589 / 4000) (150476623297959 / 100000) := by
  exact
    packedTile65536 1504672000 1504803072 14 6198 38790 30 _ _ (2113183 / 100000) (1056593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504803072 :
    ThetaLowerSegment 1504803072 1504934144 (150476623297959 / 100000)
      (75244812881091 / 50000) := by
  exact
    packedTile65536 1504803072 1504934144 14 6153 38791 30 _ _ (2113191 / 100000) (1056597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1504934144 :
    ThetaLowerSegment 1504934144 1505065216 (75244812881091 / 50000) (75251416631091 / 50000) := by
  exact
    packedTile65536 1504934144 1505065216 14 6250 38793 30 _ _ (5283 / 250) (2113203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505065216 :
    ThetaLowerSegment 1505065216 1505196288 (75251416631091 / 50000) (4703624162367 / 3125) := by
  exact
    packedTile65536 1505065216 1505196288 14 6218 38795 30 _ _ (2113209 / 100000) (528303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505196288 :
    ThetaLowerSegment 1505196288 1505327360 (4703624162367 / 3125) (150529212500249 / 100000) := by
  exact
    packedTile65536 1505196288 1505327360 14 6265 38796 30 _ _ (2113217 / 100000) (105661 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505327360 :
    ThetaLowerSegment 1505327360 1505458432 (150529212500249 / 100000)
      (150542403256941 / 100000) := by
  exact
    packedTile65536 1505327360 1505458432 14 6242 38798 30 _ _ (1056613 / 50000) (2113229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505458432 :
    ThetaLowerSegment 1505458432 1505589504 (150542403256941 / 100000)
      (150555577163931 / 100000) := by
  exact
    packedTile65536 1505458432 1505589504 14 6234 38800 30 _ _ (422647 / 20000) (1056619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505589504 :
    ThetaLowerSegment 1505589504 1505720576 (150555577163931 / 100000)
      (150568706748903 / 100000) := by
  exact
    packedTile65536 1505589504 1505720576 14 6213 38801 30 _ _ (528311 / 25000) (2113247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505720576 :
    ThetaLowerSegment 1505720576 1505851648 (150568706748903 / 100000)
      (150581846949839 / 100000) := by
  exact
    packedTile65536 1505720576 1505851648 14 6218 38803 30 _ _ (528313 / 25000) (422651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505851648 :
    ThetaLowerSegment 1505851648 1505982720 (150581846949839 / 100000)
      (150594953394561 / 100000) := by
  exact
    packedTile65536 1505851648 1505982720 14 6202 38805 30 _ _ (2113261 / 100000) (132079 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1505982720 :
    ThetaLowerSegment 1505982720 1506113792 (150594953394561 / 100000)
      (150608178238221 / 100000) := by
  exact
    packedTile65536 1505982720 1506113792 14 6258 38806 30 _ _ (211327 / 10000) (2113273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506113792 :
    ThetaLowerSegment 1506113792 1506244864 (150608178238221 / 100000)
      (150621303807879 / 100000) := by
  exact
    packedTile65536 1506113792 1506244864 14 6211 38808 30 _ _ (1056639 / 50000) (2113281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506244864 :
    ThetaLowerSegment 1506244864 1506375936 (150621303807879 / 100000)
      (150634313202651 / 100000) := by
  exact
    packedTile65536 1506244864 1506375936 14 6156 38810 30 _ _ (2113287 / 100000) (211329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506375936 :
    ThetaLowerSegment 1506375936 1506507008 (150634313202651 / 100000)
      (150647352238971 / 100000) := by
  exact
    packedTile65536 1506375936 1506507008 14 6170 38812 30 _ _ (132081 / 6250) (2113299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506507008 :
    ThetaLowerSegment 1506507008 1506638080 (150647352238971 / 100000)
      (150660461063683 / 100000) := by
  exact
    packedTile65536 1506507008 1506638080 14 6203 38813 30 _ _ (264163 / 12500) (2113307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506638080 :
    ThetaLowerSegment 1506638080 1506769152 (150660461063683 / 100000)
      (37668391429399 / 25000) := by
  exact
    packedTile65536 1506638080 1506769152 14 6201 38815 30 _ _ (2113313 / 100000) (528329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506769152 :
    ThetaLowerSegment 1506769152 1506900224 (37668391429399 / 25000) (75343354233557 / 50000) := by
  exact
    packedTile65536 1506769152 1506900224 14 6219 38817 30 _ _ (1056661 / 50000) (84533 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1506900224 :
    ThetaLowerSegment 1506900224 1507031296 (75343354233557 / 50000) (15069967586613 / 10000) := by
  exact
    packedTile65536 1506900224 1507031296 14 6136 38818 30 _ _ (2113331 / 100000) (1056667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507031296 :
    ThetaLowerSegment 1507031296 1507162368 (15069967586613 / 10000)
      (150712691921031 / 100000) := by
  exact
    packedTile65536 1507031296 1507162368 14 6159 38820 30 _ _ (2113339 / 100000) (1056671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507162368 :
    ThetaLowerSegment 1507162368 1507293440 (150712691921031 / 100000)
      (150725845398983 / 100000) := by
  exact
    packedTile65536 1507162368 1507293440 14 6224 38822 30 _ _ (528337 / 25000) (2113351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507293440 :
    ThetaLowerSegment 1507293440 1507424512 (150725845398983 / 100000)
      (18842380414181 / 12500) := by
  exact
    packedTile65536 1507293440 1507424512 14 6245 38823 30 _ _ (2113357 / 100000) (26417 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507424512 :
    ThetaLowerSegment 1507424512 1507555584 (18842380414181 / 12500) (18844007705231 / 12500) := by
  exact
    packedTile65536 1507424512 1507555584 14 6160 38825 30 _ _ (422673 / 20000) (264171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507555584 :
    ThetaLowerSegment 1507555584 1507686656 (18844007705231 / 12500) (18845649796829 / 12500) := by
  exact
    packedTile65536 1507555584 1507686656 14 6216 38827 30 _ _ (1056687 / 50000) (2113377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507686656 :
    ThetaLowerSegment 1507686656 1507817728 (18845649796829 / 12500) (75389169695063 / 50000) := by
  exact
    packedTile65536 1507686656 1507817728 14 6218 38828 30 _ _ (2113383 / 100000) (1056693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507817728 :
    ThetaLowerSegment 1507817728 1507948800 (75389169695063 / 50000) (75395733887509 / 50000) := by
  exact
    packedTile65536 1507817728 1507948800 14 6212 38830 30 _ _ (2113391 / 100000) (1056697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507948800 :
    ThetaLowerSegment 1507948800 1508079872 (75395733887509 / 50000) (75402315015109 / 50000) := by
  exact
    packedTile65536 1507948800 1508079872 14 6228 38832 30 _ _ (10567 / 500) (2113403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508079872 :
    ThetaLowerSegment 1508079872 1508210944 (75402315015109 / 50000) (37704447028663 / 25000) := by
  exact
    packedTile65536 1508079872 1508210944 14 6226 38834 30 _ _ (2113409 / 100000) (528353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508210944 :
    ThetaLowerSegment 1508210944 1508342016 (37704447028663 / 25000) (37707748186017 / 25000) := by
  exact
    packedTile65536 1508210944 1508342016 14 6248 38835 30 _ _ (2113417 / 100000) (105671 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508342016 :
    ThetaLowerSegment 1508342016 1508473088 (37707748186017 / 25000) (75422101884997 / 50000) := by
  exact
    packedTile65536 1508342016 1508473088 14 6251 38837 30 _ _ (1056713 / 50000) (2113429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508473088 :
    ThetaLowerSegment 1508473088 1508604160 (75422101884997 / 50000)
      (150857334541649 / 100000) := by
  exact
    packedTile65536 1508473088 1508604160 14 6213 38839 30 _ _ (422687 / 20000) (1056719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508604160 :
    ThetaLowerSegment 1508604160 1508735232 (150857334541649 / 100000)
      (150870480163329 / 100000) := by
  exact
    packedTile65536 1508604160 1508735232 14 6220 38840 30 _ _ (528361 / 25000) (2113447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508735232 :
    ThetaLowerSegment 1508735232 1508866304 (150870480163329 / 100000)
      (150883704032493 / 100000) := by
  exact
    packedTile65536 1508735232 1508866304 14 6257 38842 30 _ _ (528363 / 25000) (422691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508866304 :
    ThetaLowerSegment 1508866304 1508997376 (150883704032493 / 100000)
      (15089663207343 / 10000) := by
  exact
    packedTile65536 1508866304 1508997376 14 6117 38844 30 _ _ (2113461 / 100000) (264183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1508997376 :
    ThetaLowerSegment 1508997376 1509128448 (15089663207343 / 10000) (15090973981437 / 10000) := by
  exact
    packedTile65536 1508997376 1509128448 14 6202 38845 30 _ _ (211347 / 10000) (2113473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509128448 :
    ThetaLowerSegment 1509128448 1509259520 (15090973981437 / 10000) (15092267429973 / 10000) := by
  exact
    packedTile65536 1509128448 1509259520 14 6120 38847 30 _ _ (1056739 / 50000) (2113481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509259520 :
    ThetaLowerSegment 1509259520 1509390592 (15092267429973 / 10000) (18866951633393 / 12500) := by
  exact
    packedTile65536 1509259520 1509390592 14 6122 38849 30 _ _ (2113487 / 100000) (211349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509390592 :
    ThetaLowerSegment 1509390592 1509521664 (18866951633393 / 12500) (4717143237253 / 3125) := by
  exact
    packedTile65536 1509390592 1509521664 14 6137 38850 30 _ _ (264187 / 12500) (2113499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509521664 :
    ThetaLowerSegment 1509521664 1509652736 (4717143237253 / 3125) (4717557219849 / 3125) := by
  exact
    packedTile65536 1509521664 1509652736 14 6268 38852 30 _ _ (66047 / 3125) (2113507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509652736 :
    ThetaLowerSegment 1509652736 1509783808 (4717557219849 / 3125) (18871858397919 / 12500) := by
  exact
    packedTile65536 1509652736 1509783808 14 6168 38854 30 _ _ (2113513 / 100000) (528379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509783808 :
    ThetaLowerSegment 1509783808 1509914880 (18871858397919 / 12500) (37746962108869 / 25000) := by
  exact
    packedTile65536 1509783808 1509914880 14 6142 38855 30 _ _ (1056761 / 50000) (84541 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1509914880 :
    ThetaLowerSegment 1509914880 1510045952 (37746962108869 / 25000) (75500420152193 / 50000) := by
  exact
    packedTile65536 1509914880 1510045952 14 6147 38857 30 _ _ (211353 / 10000) (2113533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510045952 :
    ThetaLowerSegment 1510045952 1510177024 (75500420152193 / 50000)
      (151014077399143 / 100000) := by
  exact
    packedTile65536 1510045952 1510177024 14 6263 38859 30 _ _ (2113539 / 100000) (1056771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510177024 :
    ThetaLowerSegment 1510177024 1510308096 (151014077399143 / 100000)
      (151027164488359 / 100000) := by
  exact
    packedTile65536 1510177024 1510308096 14 6192 38860 30 _ _ (528387 / 25000) (2113551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510308096 :
    ThetaLowerSegment 1510308096 1510439168 (151027164488359 / 100000)
      (151040137495087 / 100000) := by
  exact
    packedTile65536 1510308096 1510439168 14 6138 38862 30 _ _ (528389 / 25000) (2113559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510439168 :
    ThetaLowerSegment 1510439168 1510570240 (151040137495087 / 100000)
      (151053254279477 / 100000) := by
  exact
    packedTile65536 1510439168 1510570240 14 6206 38864 30 _ _ (422713 / 20000) (66049 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510570240 :
    ThetaLowerSegment 1510570240 1510701312 (151053254279477 / 100000)
      (151066123831563 / 100000) := by
  exact
    packedTile65536 1510570240 1510701312 14 6089 38866 30 _ _ (1056787 / 50000) (2113577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510701312 :
    ThetaLowerSegment 1510701312 1510832384 (151066123831563 / 100000)
      (151079088543551 / 100000) := by
  exact
    packedTile65536 1510701312 1510832384 14 6134 38867 30 _ _ (1056791 / 50000) (422717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510832384 :
    ThetaLowerSegment 1510832384 1510963456 (151079088543551 / 100000)
      (151092192807751 / 100000) := by
  exact
    packedTile65536 1510832384 1510963456 14 6200 38869 30 _ _ (2113591 / 100000) (1056797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1510963456 :
    ThetaLowerSegment 1510963456 1511094528 (151092192807751 / 100000)
      (151105288673351 / 100000) := by
  exact
    packedTile65536 1510963456 1511094528 14 6196 38871 30 _ _ (2642 / 125) (2113603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511094528 :
    ThetaLowerSegment 1511094528 1511225600 (151105288673351 / 100000)
      (37779583995427 / 25000) := by
  exact
    packedTile65536 1511094528 1511225600 14 6173 38872 30 _ _ (2113609 / 100000) (528403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511225600 :
    ThetaLowerSegment 1511225600 1511356672 (37779583995427 / 25000) (18891448016633 / 12500) := by
  exact
    packedTile65536 1511225600 1511356672 14 6268 38874 30 _ _ (2113617 / 100000) (105681 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511356672 :
    ThetaLowerSegment 1511356672 1511487744 (18891448016633 / 12500) (75572379181961 / 50000) := by
  exact
    packedTile65536 1511356672 1511487744 14 6233 38876 30 _ _ (1056813 / 50000) (2113629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511487744 :
    ThetaLowerSegment 1511487744 1511618816 (75572379181961 / 50000) (37789435077523 / 25000) := by
  exact
    packedTile65536 1511487744 1511618816 14 6142 38877 30 _ _ (422727 / 20000) (1056819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511618816 :
    ThetaLowerSegment 1511618816 1511749888 (37789435077523 / 25000)
      (151170792055617 / 100000) := by
  exact
    packedTile65536 1511618816 1511749888 14 6175 38879 30 _ _ (2113643 / 100000) (1056823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511749888 :
    ThetaLowerSegment 1511749888 1511880960 (151170792055617 / 100000)
      (30236766234961 / 20000) := by
  exact
    packedTile65536 1511749888 1511880960 14 6169 38881 30 _ _ (528413 / 25000) (422731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511880960 :
    ThetaLowerSegment 1511880960 1512012032 (30236766234961 / 20000)
      (151197024646767 / 100000) := by
  exact
    packedTile65536 1511880960 1512012032 14 6242 38882 30 _ _ (2113661 / 100000) (66052 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512012032 :
    ThetaLowerSegment 1512012032 1512143104 (151197024646767 / 100000) (3780253076339 / 2500) := by
  exact
    packedTile65536 1512012032 1512143104 14 6197 38884 30 _ _ (2113669 / 100000) (264209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512143104 :
    ThetaLowerSegment 1512143104 1512274176 (3780253076339 / 2500) (75611551575079 / 50000) := by
  exact
    packedTile65536 1512143104 1512274176 14 6141 38886 30 _ _ (1056839 / 50000) (2113681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512274176 :
    ThetaLowerSegment 1512274176 1512405248 (75611551575079 / 50000)
      (151236332717091 / 100000) := by
  exact
    packedTile65536 1512274176 1512405248 14 6259 38887 30 _ _ (2113687 / 100000) (211369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512405248 :
    ThetaLowerSegment 1512405248 1512536320 (151236332717091 / 100000)
      (75624635322093 / 50000) := by
  exact
    packedTile65536 1512405248 1512536320 14 6121 38889 30 _ _ (422739 / 20000) (1056849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512536320 :
    ThetaLowerSegment 1512536320 1512667392 (75624635322093 / 50000) (75631182520233 / 50000) := by
  exact
    packedTile65536 1512536320 1512667392 14 6195 38891 30 _ _ (264213 / 12500) (2113707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512667392 :
    ThetaLowerSegment 1512667392 1512798464 (75631182520233 / 50000) (15127565606781 / 10000) := by
  exact
    packedTile65536 1512667392 1512798464 14 6288 38893 30 _ _ (2113713 / 100000) (528429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512798464 :
    ThetaLowerSegment 1512798464 1512929536 (15127565606781 / 10000) (18911098841263 / 12500) := by
  exact
    packedTile65536 1512798464 1512929536 14 6214 38894 30 _ _ (2113721 / 100000) (528431 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1512929536 :
    ThetaLowerSegment 1512929536 1513060608 (18911098841263 / 12500) (37825485589541 / 25000) := by
  exact
    packedTile65536 1512929536 1513060608 14 6222 38896 30 _ _ (211373 / 10000) (2113733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513060608 :
    ThetaLowerSegment 1513060608 1513191680 (37825485589541 / 25000) (30262992175333 / 20000) := by
  exact
    packedTile65536 1513060608 1513191680 14 6159 38898 30 _ _ (2113739 / 100000) (1056871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513191680 :
    ThetaLowerSegment 1513191680 1513322752 (30262992175333 / 20000)
      (151328184477897 / 100000) := by
  exact
    packedTile65536 1513191680 1513322752 14 6256 38899 30 _ _ (2113747 / 100000) (1691 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513322752 :
    ThetaLowerSegment 1513322752 1513339136 (151328184477897 / 100000)
      (151329805728749 / 100000) := by
  exact
    packedTile65536 1513322752 1513339136 11 767 38901 30 _ _ (528439 / 25000) (2113759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1513339136 :
    ThetaLowerSegment 1513339136 1513341184 (151329805728749 / 100000)
      (151330029786991 / 100000) := by
  exact
    packedTile65536 1513339136 1513341184 8 106 38901 30 _ _ (2113757 / 100000) (13211 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1481341184_1513341184 :
    ThetaLowerSegment 1481341184 1513341184 (74064497890991 / 50000)
      (151330029786991 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1481341184 cell1481472256)
                  (ThetaLowerSegment.join cell1481603328 cell1481734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1481865472 cell1481996544)
                  (ThetaLowerSegment.join cell1482127616 cell1482258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1482389760 cell1482520832)
                  (ThetaLowerSegment.join cell1482651904 cell1482782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1482914048 cell1483045120)
                  (ThetaLowerSegment.join cell1483176192 cell1483307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1483438336 cell1483569408)
                  (ThetaLowerSegment.join cell1483700480 cell1483831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1483962624 cell1484093696)
                  (ThetaLowerSegment.join cell1484224768 cell1484355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1484486912 cell1484617984)
                  (ThetaLowerSegment.join cell1484749056 cell1484880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1485011200 cell1485142272)
                  (ThetaLowerSegment.join cell1485273344 cell1485404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1485535488 cell1485666560)
                  (ThetaLowerSegment.join cell1485797632 cell1485928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1486059776 cell1486190848)
                  (ThetaLowerSegment.join cell1486321920 cell1486452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1486584064 cell1486715136)
                  (ThetaLowerSegment.join cell1486846208 cell1486977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1487108352 cell1487239424)
                  (ThetaLowerSegment.join cell1487370496 cell1487501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1487632640 cell1487763712)
                  (ThetaLowerSegment.join cell1487894784 cell1488025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1488156928 cell1488288000)
                  (ThetaLowerSegment.join cell1488419072 cell1488550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1488681216 cell1488812288)
                  (ThetaLowerSegment.join cell1488943360 cell1489074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1489205504 cell1489336576)
                  (ThetaLowerSegment.join cell1489467648 cell1489598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1489729792 cell1489860864)
                  (ThetaLowerSegment.join cell1489991936 cell1490123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1490254080 cell1490385152)
                  (ThetaLowerSegment.join cell1490516224 cell1490647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1490778368 cell1490909440)
                  (ThetaLowerSegment.join cell1491040512 cell1491171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1491302656 cell1491433728)
                  (ThetaLowerSegment.join cell1491564800 cell1491695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1491826944 cell1491958016)
                  (ThetaLowerSegment.join cell1492089088 cell1492220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1492351232 cell1492482304)
                  (ThetaLowerSegment.join cell1492613376 cell1492744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1492875520 cell1493006592)
                  (ThetaLowerSegment.join cell1493137664 cell1493268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1493399808 cell1493530880)
                  (ThetaLowerSegment.join cell1493661952 cell1493793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1493924096 cell1494055168)
                  (ThetaLowerSegment.join cell1494186240 cell1494317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1494448384 cell1494579456)
                  (ThetaLowerSegment.join cell1494710528 cell1494841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1494972672 cell1495103744)
                  (ThetaLowerSegment.join cell1495234816 cell1495365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1495496960 cell1495628032)
                  (ThetaLowerSegment.join cell1495759104 cell1495890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1496021248 cell1496152320)
                  (ThetaLowerSegment.join cell1496283392 cell1496414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1496545536 cell1496676608)
                  (ThetaLowerSegment.join cell1496807680 cell1496938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1497069824 cell1497200896)
                  (ThetaLowerSegment.join cell1497331968 cell1497463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1497594112 cell1497725184)
                  (ThetaLowerSegment.join cell1497856256 cell1497987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1498118400 cell1498249472)
                  (ThetaLowerSegment.join cell1498380544 cell1498511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1498642688 cell1498773760)
                  (ThetaLowerSegment.join cell1498904832 cell1499035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1499166976 cell1499298048)
                  (ThetaLowerSegment.join cell1499429120 cell1499560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1499691264 cell1499822336)
                  (ThetaLowerSegment.join cell1499953408 cell1500084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1500215552 cell1500346624)
                  (ThetaLowerSegment.join cell1500477696 cell1500608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1500739840 cell1500870912)
                  (ThetaLowerSegment.join cell1501001984 cell1501133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1501264128 cell1501395200)
                  (ThetaLowerSegment.join cell1501526272 cell1501657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1501788416 cell1501919488)
                  (ThetaLowerSegment.join cell1502050560 cell1502181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1502312704 cell1502443776)
                  (ThetaLowerSegment.join cell1502574848 cell1502705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1502836992 cell1502968064)
                  (ThetaLowerSegment.join cell1503099136 cell1503230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1503361280 cell1503492352)
                  (ThetaLowerSegment.join cell1503623424 cell1503754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1503885568 cell1504016640)
                  (ThetaLowerSegment.join cell1504147712 cell1504278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1504409856 cell1504540928)
                  (ThetaLowerSegment.join cell1504672000 cell1504803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1504934144 cell1505065216)
                  (ThetaLowerSegment.join cell1505196288 cell1505327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1505458432 cell1505589504)
                  (ThetaLowerSegment.join cell1505720576 cell1505851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1505982720 cell1506113792)
                  (ThetaLowerSegment.join cell1506244864 cell1506375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1506507008 cell1506638080)
                  (ThetaLowerSegment.join cell1506769152 cell1506900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1507031296 cell1507162368)
                  (ThetaLowerSegment.join cell1507293440 cell1507424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1507555584 cell1507686656)
                  (ThetaLowerSegment.join cell1507817728 cell1507948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1508079872 cell1508210944)
                  (ThetaLowerSegment.join cell1508342016 cell1508473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1508604160 cell1508735232)
                  (ThetaLowerSegment.join cell1508866304 cell1508997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1509128448 cell1509259520)
                  (ThetaLowerSegment.join cell1509390592 cell1509521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1509652736 cell1509783808)
                  (ThetaLowerSegment.join cell1509914880 cell1510045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1510177024 cell1510308096)
                  (ThetaLowerSegment.join cell1510439168 cell1510570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1510701312 cell1510832384)
                  (ThetaLowerSegment.join cell1510963456 cell1511094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1511225600 cell1511356672)
                  (ThetaLowerSegment.join cell1511487744 cell1511618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1511749888 cell1511880960)
                  (ThetaLowerSegment.join cell1512012032 cell1512143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1512274176 cell1512405248)
                  (ThetaLowerSegment.join cell1512536320 cell1512667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1512798464 cell1512929536)
                (ThetaLowerSegment.join cell1513060608 cell1513191680))
              (ThetaLowerSegment.join cell1513322752 cell1513339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
