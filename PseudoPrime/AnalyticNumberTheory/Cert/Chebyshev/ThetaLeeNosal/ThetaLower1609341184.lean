/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1609341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1577341184 :
    ThetaLowerSegment 1577341184 1577472256 (157729148577773 / 100000)
      (157742461690887 / 100000) := by
  exact
    packedTile65536 1577341184 1577472256 14 6286 39715 31 _ _ (2117899 / 100000) (1058951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577472256 :
    ThetaLowerSegment 1577472256 1577603328 (157742461690887 / 100000)
      (39438906120723 / 25000) := by
  exact
    packedTile65536 1577472256 1577603328 14 6215 39717 31 _ _ (2117907 / 100000) (211791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577603328 :
    ThetaLowerSegment 1577603328 1577734400 (39438906120723 / 25000) (39442232307801 / 25000) := by
  exact
    packedTile65536 1577603328 1577734400 14 6282 39719 31 _ _ (529479 / 25000) (2117919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577734400 :
    ThetaLowerSegment 1577734400 1577865472 (39442232307801 / 25000) (39445550035747 / 25000) := by
  exact
    packedTile65536 1577734400 1577865472 14 6266 39720 31 _ _ (529481 / 25000) (2117927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577865472 :
    ThetaLowerSegment 1577865472 1577996544 (39445550035747 / 25000) (19724428328541 / 12500) := by
  exact
    packedTile65536 1577865472 1577996544 14 6245 39722 31 _ _ (529483 / 25000) (423587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577996544 :
    ThetaLowerSegment 1577996544 1578127616 (19724428328541 / 12500)
      (157808462555183 / 100000) := by
  exact
    packedTile65536 1577996544 1578127616 14 6155 39724 31 _ _ (2117941 / 100000) (264743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578127616 :
    ThetaLowerSegment 1578127616 1578258688 (157808462555183 / 100000) (6312864431303 / 4000) := by
  exact
    packedTile65536 1578127616 1578258688 14 6208 39725 31 _ _ (2117949 / 100000) (66186 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578258688 :
    ThetaLowerSegment 1578258688 1578389760 (6312864431303 / 4000) (157834670105437 / 100000) := by
  exact
    packedTile65536 1578258688 1578389760 14 6166 39727 31 _ _ (2117957 / 100000) (52949 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578389760 :
    ThetaLowerSegment 1578389760 1578520832 (157834670105437 / 100000)
      (31569614518857 / 20000) := by
  exact
    packedTile65536 1578389760 1578520832 14 6328 39728 31 _ _ (1058983 / 50000) (2117969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578520832 :
    ThetaLowerSegment 1578520832 1578651904 (31569614518857 / 20000)
      (157861079072619 / 100000) := by
  exact
    packedTile65536 1578520832 1578651904 14 6141 39730 31 _ _ (1058987 / 50000) (2117977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578651904 :
    ThetaLowerSegment 1578651904 1578782976 (157861079072619 / 100000)
      (157874369409669 / 100000) := by
  exact
    packedTile65536 1578651904 1578782976 14 6275 39732 31 _ _ (1058991 / 50000) (423597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578782976 :
    ThetaLowerSegment 1578782976 1578914048 (157874369409669 / 100000)
      (157887433178157 / 100000) := by
  exact
    packedTile65536 1578782976 1578914048 14 6168 39733 31 _ _ (2117991 / 100000) (1058997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1578914048 :
    ThetaLowerSegment 1578914048 1579045120 (157887433178157 / 100000)
      (19737544386257 / 12500) := by
  exact
    packedTile65536 1578914048 1579045120 14 6101 39735 31 _ _ (2117999 / 100000) (1059001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579045120 :
    ThetaLowerSegment 1579045120 1579176192 (19737544386257 / 12500) (6316536673569 / 4000) := by
  exact
    packedTile65536 1579045120 1579176192 14 6167 39737 31 _ _ (2118007 / 100000) (211801 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579176192 :
    ThetaLowerSegment 1579176192 1579307264 (6316536673569 / 4000) (31585304623209 / 20000) := by
  exact
    packedTile65536 1579176192 1579307264 14 6188 39738 31 _ _ (423603 / 20000) (1059009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579307264 :
    ThetaLowerSegment 1579307264 1579438336 (31585304623209 / 20000) (31587903438657 / 20000) := by
  exact
    packedTile65536 1579307264 1579438336 14 6135 39740 31 _ _ (264753 / 12500) (2118027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579438336 :
    ThetaLowerSegment 1579438336 1579569408 (31587903438657 / 20000)
      (157952604513013 / 100000) := by
  exact
    packedTile65536 1579438336 1579569408 14 6179 39742 31 _ _ (132377 / 6250) (423607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579569408 :
    ThetaLowerSegment 1579569408 1579700480 (157952604513013 / 100000)
      (157965791430053 / 100000) := by
  exact
    packedTile65536 1579569408 1579700480 14 6226 39743 31 _ _ (52951 / 2500) (2118043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579700480 :
    ThetaLowerSegment 1579700480 1579831552 (157965791430053 / 100000)
      (157978991111421 / 100000) := by
  exact
    packedTile65536 1579700480 1579831552 14 6232 39745 31 _ _ (2118049 / 100000) (529513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579831552 :
    ThetaLowerSegment 1579831552 1579962624 (157978991111421 / 100000)
      (31598438168529 / 20000) := by
  exact
    packedTile65536 1579831552 1579962624 14 6232 39747 31 _ _ (2118057 / 100000) (105903 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1579962624 :
    ThetaLowerSegment 1579962624 1580093696 (31598438168529 / 20000) (987533307499 / 625) := by
  exact
    packedTile65536 1579962624 1580093696 14 6203 39748 31 _ _ (423613 / 20000) (529517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580093696 :
    ThetaLowerSegment 1580093696 1580224768 (987533307499 / 625) (4938077443657 / 3125) := by
  exact
    packedTile65536 1580093696 1580224768 14 6208 39750 31 _ _ (2118073 / 100000) (529519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580224768 :
    ThetaLowerSegment 1580224768 1580355840 (4938077443657 / 3125) (79015732078883 / 50000) := by
  exact
    packedTile65536 1580224768 1580355840 14 6131 39752 31 _ _ (1059041 / 50000) (423617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580355840 :
    ThetaLowerSegment 1580355840 1580486912 (79015732078883 / 50000) (79022215552373 / 50000) := by
  exact
    packedTile65536 1580355840 1580486912 14 6122 39753 31 _ _ (211809 / 10000) (2118093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580486912 :
    ThetaLowerSegment 1580486912 1580617984 (79022215552373 / 50000) (39514359586141 / 25000) := by
  exact
    packedTile65536 1580486912 1580617984 14 6141 39755 31 _ _ (1059049 / 50000) (2118101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580617984 :
    ThetaLowerSegment 1580617984 1580749056 (39514359586141 / 25000) (19758826621263 / 12500) := by
  exact
    packedTile65536 1580617984 1580749056 14 6220 39756 31 _ _ (2118107 / 100000) (211811 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580749056 :
    ThetaLowerSegment 1580749056 1580880128 (19758826621263 / 12500)
      (158083768582369 / 100000) := by
  exact
    packedTile65536 1580749056 1580880128 14 6211 39758 31 _ _ (423623 / 20000) (1059059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1580880128 :
    ThetaLowerSegment 1580880128 1581011200 (158083768582369 / 100000)
      (79048474830899 / 50000) := by
  exact
    packedTile65536 1580880128 1581011200 14 6223 39760 31 _ _ (2118123 / 100000) (1059063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581011200 :
    ThetaLowerSegment 1581011200 1581142272 (79048474830899 / 50000) (79055088698069 / 50000) := by
  exact
    packedTile65536 1581011200 1581142272 14 6245 39761 31 _ _ (529533 / 25000) (423627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581142272 :
    ThetaLowerSegment 1581142272 1581273344 (79055088698069 / 50000) (79061651754859 / 50000) := by
  exact
    packedTile65536 1581142272 1581273344 14 6197 39763 31 _ _ (105907 / 5000) (2118143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581273344 :
    ThetaLowerSegment 1581273344 1581404416 (79061651754859 / 50000) (15813638095547 / 10000) := by
  exact
    packedTile65536 1581273344 1581404416 14 6174 39765 31 _ _ (529537 / 25000) (2118151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581404416 :
    ThetaLowerSegment 1581404416 1581535488 (15813638095547 / 10000) (79074747229633 / 50000) := by
  exact
    packedTile65536 1581404416 1581535488 14 6191 39766 31 _ _ (529539 / 25000) (2118159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581535488 :
    ThetaLowerSegment 1581535488 1581666560 (79074747229633 / 50000)
      (158162633436761 / 100000) := by
  exact
    packedTile65536 1581535488 1581666560 14 6203 39768 31 _ _ (423633 / 20000) (264771 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581666560 :
    ThetaLowerSegment 1581666560 1581797632 (158162633436761 / 100000) (4942996596299 / 3125) := by
  exact
    packedTile65536 1581666560 1581797632 14 6259 39770 31 _ _ (2118173 / 100000) (66193 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581797632 :
    ThetaLowerSegment 1581797632 1581928704 (4942996596299 / 3125) (158188839522021 / 100000) := by
  exact
    packedTile65536 1581797632 1581928704 14 6113 39771 31 _ _ (2118181 / 100000) (264773 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581928704 :
    ThetaLowerSegment 1581928704 1582059776 (158188839522021 / 100000)
      (158201849445001 / 100000) := by
  exact
    packedTile65536 1581928704 1582059776 14 6142 39773 31 _ _ (211819 / 10000) (2118193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582059776 :
    ThetaLowerSegment 1582059776 1582190848 (158201849445001 / 100000)
      (158214942026839 / 100000) := by
  exact
    packedTile65536 1582059776 1582190848 14 6181 39775 31 _ _ (1059099 / 50000) (2118201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582190848 :
    ThetaLowerSegment 1582190848 1582321920 (158214942026839 / 100000)
      (158227909683971 / 100000) := by
  exact
    packedTile65536 1582190848 1582321920 14 6122 39776 31 _ _ (1059103 / 50000) (2118209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582321920 :
    ThetaLowerSegment 1582321920 1582452992 (158227909683971 / 100000)
      (158241142166829 / 100000) := by
  exact
    packedTile65536 1582321920 1582452992 14 6247 39778 31 _ _ (1059107 / 50000) (2118217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582452992 :
    ThetaLowerSegment 1582452992 1582584064 (158241142166829 / 100000)
      (158254122637373 / 100000) := by
  exact
    packedTile65536 1582452992 1582584064 14 6128 39780 31 _ _ (2118223 / 100000) (1059113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582584064 :
    ThetaLowerSegment 1582584064 1582715136 (158254122637373 / 100000) (4945853659321 / 3125) := by
  exact
    packedTile65536 1582584064 1582715136 14 6229 39781 31 _ _ (2118231 / 100000) (1059117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582715136 :
    ThetaLowerSegment 1582715136 1582846208 (4945853659321 / 3125) (31656105710983 / 20000) := by
  exact
    packedTile65536 1582715136 1582846208 14 6237 39783 31 _ _ (2118239 / 100000) (1059121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582846208 :
    ThetaLowerSegment 1582846208 1582977280 (31656105710983 / 20000) (31658715392519 / 20000) := by
  exact
    packedTile65536 1582846208 1582977280 14 6160 39784 31 _ _ (264781 / 12500) (2118251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1582977280 :
    ThetaLowerSegment 1582977280 1583108352 (31658715392519 / 20000)
      (158306843599923 / 100000) := by
  exact
    packedTile65536 1582977280 1583108352 14 6263 39786 31 _ _ (132391 / 6250) (2118259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583108352 :
    ThetaLowerSegment 1583108352 1583239424 (158306843599923 / 100000)
      (31664026293999 / 20000) := by
  exact
    packedTile65536 1583108352 1583239424 14 6273 39788 31 _ _ (264783 / 12500) (2118267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583239424 :
    ThetaLowerSegment 1583239424 1583370496 (31664026293999 / 20000)
      (158333173670699 / 100000) := by
  exact
    packedTile65536 1583239424 1583370496 14 6157 39789 31 _ _ (66196 / 3125) (84731 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583370496 :
    ThetaLowerSegment 1583370496 1583501568 (158333173670699 / 100000)
      (158346336668833 / 100000) := by
  exact
    packedTile65536 1583370496 1583501568 14 6214 39791 31 _ _ (2118281 / 100000) (529571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583501568 :
    ThetaLowerSegment 1583501568 1583632640 (158346336668833 / 100000)
      (79179719143149 / 50000) := by
  exact
    packedTile65536 1583501568 1583632640 14 6185 39793 31 _ _ (2118289 / 100000) (529573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583632640 :
    ThetaLowerSegment 1583632640 1583763712 (79179719143149 / 50000)
      (158372628921717 / 100000) := by
  exact
    packedTile65536 1583632640 1583763712 14 6227 39794 31 _ _ (2118297 / 100000) (21183 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583763712 :
    ThetaLowerSegment 1583763712 1583894784 (158372628921717 / 100000)
      (79192916158391 / 50000) := by
  exact
    packedTile65536 1583763712 1583894784 14 6233 39796 31 _ _ (423661 / 20000) (529577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1583894784 :
    ThetaLowerSegment 1583894784 1584025856 (79192916158391 / 50000) (39599690096781 / 25000) := by
  exact
    packedTile65536 1583894784 1584025856 14 6103 39798 31 _ _ (1059157 / 50000) (2118317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584025856 :
    ThetaLowerSegment 1584025856 1584156928 (39599690096781 / 25000) (79206007363939 / 50000) := by
  exact
    packedTile65536 1584025856 1584156928 14 6257 39799 31 _ _ (1059161 / 50000) (84733 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584156928 :
    ThetaLowerSegment 1584156928 1584288000 (79206007363939 / 50000) (19803153344011 / 12500) := by
  exact
    packedTile65536 1584156928 1584288000 14 6237 39801 31 _ _ (211833 / 10000) (2118333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584288000 :
    ThetaLowerSegment 1584288000 1584419072 (19803153344011 / 12500) (39609528681641 / 25000) := by
  exact
    packedTile65536 1584288000 1584419072 14 6084 39803 31 _ _ (2118339 / 100000) (1059171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584419072 :
    ThetaLowerSegment 1584419072 1584550144 (39609528681641 / 25000)
      (158451259069699 / 100000) := by
  exact
    packedTile65536 1584419072 1584550144 14 6205 39804 31 _ _ (2118347 / 100000) (42367 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584550144 :
    ThetaLowerSegment 1584550144 1584681216 (158451259069699 / 100000)
      (79232235624917 / 50000) := by
  exact
    packedTile65536 1584550144 1584681216 14 6237 39806 31 _ _ (423671 / 20000) (1059179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584681216 :
    ThetaLowerSegment 1584681216 1584812288 (79232235624917 / 50000) (31695468908357 / 20000) := by
  exact
    packedTile65536 1584681216 1584812288 14 6077 39808 31 _ _ (2118363 / 100000) (1059183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584812288 :
    ThetaLowerSegment 1584812288 1584943360 (31695468908357 / 20000) (6339616595881 / 4000) := by
  exact
    packedTile65536 1584812288 1584943360 14 6170 39809 31 _ _ (529593 / 25000) (16947 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1584943360 :
    ThetaLowerSegment 1584943360 1585074432 (6339616595881 / 4000) (31700683926369 / 20000) := by
  exact
    packedTile65536 1584943360 1585074432 14 6139 39811 31 _ _ (105919 / 5000) (2118383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585074432 :
    ThetaLowerSegment 1585074432 1585205504 (31700683926369 / 20000)
      (158516498559357 / 100000) := by
  exact
    packedTile65536 1585074432 1585205504 14 6174 39812 31 _ _ (529597 / 25000) (2118391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585205504 :
    ThetaLowerSegment 1585205504 1585336576 (158516498559357 / 100000)
      (158529516102777 / 100000) := by
  exact
    packedTile65536 1585205504 1585336576 14 6145 39814 31 _ _ (529599 / 25000) (2118399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585336576 :
    ThetaLowerSegment 1585336576 1585467648 (158529516102777 / 100000)
      (158542624792917 / 100000) := by
  exact
    packedTile65536 1585336576 1585467648 14 6188 39816 31 _ _ (423681 / 20000) (264801 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585467648 :
    ThetaLowerSegment 1585467648 1585598720 (158542624792917 / 100000)
      (39638932853537 / 25000) := by
  exact
    packedTile65536 1585467648 1585598720 14 6187 39817 31 _ _ (2118413 / 100000) (132401 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585598720 :
    ThetaLowerSegment 1585598720 1585729792 (39638932853537 / 25000) (79284388325333 / 50000) := by
  exact
    packedTile65536 1585598720 1585729792 14 6158 39819 31 _ _ (2118421 / 100000) (264803 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585729792 :
    ThetaLowerSegment 1585729792 1585860864 (79284388325333 / 50000) (79290889787003 / 50000) := by
  exact
    packedTile65536 1585729792 1585860864 14 6138 39821 31 _ _ (211843 / 10000) (2118433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585860864 :
    ThetaLowerSegment 1585860864 1585991936 (79290889787003 / 50000) (39648758660143 / 25000) := by
  exact
    packedTile65536 1585860864 1585991936 14 6257 39822 31 _ _ (1059219 / 50000) (2118441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585991936 :
    ThetaLowerSegment 1585991936 1586123008 (39648758660143 / 25000) (79304060140757 / 50000) := by
  exact
    packedTile65536 1585991936 1586123008 14 6177 39824 31 _ _ (1059223 / 50000) (2118449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586123008 :
    ThetaLowerSegment 1586123008 1586254080 (79304060140757 / 50000) (4956917982756 / 3125) := by
  exact
    packedTile65536 1586123008 1586254080 14 6257 39826 31 _ _ (1059227 / 50000) (2118457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586254080 :
    ThetaLowerSegment 1586254080 1586385152 (4956917982756 / 3125) (158634393403327 / 100000) := by
  exact
    packedTile65536 1586254080 1586385152 14 6145 39827 31 _ _ (2118463 / 100000) (1059233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586385152 :
    ThetaLowerSegment 1586385152 1586516224 (158634393403327 / 100000)
      (158647583003773 / 100000) := by
  exact
    packedTile65536 1586385152 1586516224 14 6226 39829 31 _ _ (2118471 / 100000) (1059237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586516224 :
    ThetaLowerSegment 1586516224 1586647296 (158647583003773 / 100000)
      (158660742995321 / 100000) := by
  exact
    packedTile65536 1586516224 1586647296 14 6212 39831 31 _ _ (2118479 / 100000) (1059241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586647296 :
    ThetaLowerSegment 1586647296 1586778368 (158660742995321 / 100000)
      (19834256151521 / 12500) := by
  exact
    packedTile65536 1586647296 1586778368 14 6281 39832 31 _ _ (2118487 / 100000) (211849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586778368 :
    ThetaLowerSegment 1586778368 1586909440 (19834256151521 / 12500) (19835883421261 / 12500) := by
  exact
    packedTile65536 1586778368 1586909440 14 6145 39834 31 _ _ (66203 / 3125) (2118499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1586909440 :
    ThetaLowerSegment 1586909440 1587040512 (19835883421261 / 12500) (19837505136073 / 12500) := by
  exact
    packedTile65536 1586909440 1587040512 14 6124 39836 31 _ _ (264813 / 12500) (2118507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587040512 :
    ThetaLowerSegment 1587040512 1587171584 (19837505136073 / 12500) (3967826642509 / 2500) := by
  exact
    packedTile65536 1587040512 1587171584 14 6148 39837 31 _ _ (132407 / 6250) (423703 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587171584 :
    ThetaLowerSegment 1587171584 1587302656 (3967826642509 / 2500) (1984075255627 / 1250) := by
  exact
    packedTile65536 1587171584 1587302656 14 6115 39839 31 _ _ (52963 / 2500) (2118523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587302656 :
    ThetaLowerSegment 1587302656 1587433728 (1984075255627 / 1250) (15873900703293 / 10000) := by
  exact
    packedTile65536 1587302656 1587433728 14 6130 39840 31 _ _ (2118529 / 100000) (529633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587433728 :
    ThetaLowerSegment 1587433728 1587564800 (15873900703293 / 10000)
      (158752309326753 / 100000) := by
  exact
    packedTile65536 1587433728 1587564800 14 6279 39842 31 _ _ (2118537 / 100000) (105927 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587564800 :
    ThetaLowerSegment 1587564800 1587695872 (158752309326753 / 100000)
      (158765384986493 / 100000) := by
  exact
    packedTile65536 1587564800 1587695872 14 6172 39844 31 _ _ (423709 / 20000) (529637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587695872 :
    ThetaLowerSegment 1587695872 1587826944 (158765384986493 / 100000)
      (158778511540881 / 100000) := by
  exact
    packedTile65536 1587695872 1587826944 14 6196 39845 31 _ _ (2118553 / 100000) (529639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587826944 :
    ThetaLowerSegment 1587826944 1587958016 (158778511540881 / 100000)
      (158791722893513 / 100000) := by
  exact
    packedTile65536 1587826944 1587958016 14 6236 39847 31 _ _ (1059281 / 50000) (423713 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1587958016 :
    ThetaLowerSegment 1587958016 1588089088 (158791722893513 / 100000)
      (158804849553233 / 100000) := by
  exact
    packedTile65536 1587958016 1588089088 14 6196 39849 31 _ _ (211857 / 10000) (2118573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588089088 :
    ThetaLowerSegment 1588089088 1588220160 (158804849553233 / 100000)
      (158818037701283 / 100000) := by
  exact
    packedTile65536 1588089088 1588220160 14 6225 39850 31 _ _ (1059289 / 50000) (2118581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588220160 :
    ThetaLowerSegment 1588220160 1588351232 (158818037701283 / 100000)
      (158831098783973 / 100000) := by
  exact
    packedTile65536 1588220160 1588351232 14 6165 39852 31 _ _ (1059293 / 50000) (2118589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588351232 :
    ThetaLowerSegment 1588351232 1588482304 (158831098783973 / 100000)
      (158844267970493 / 100000) := by
  exact
    packedTile65536 1588351232 1588482304 14 6216 39854 31 _ _ (423719 / 20000) (1059299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588482304 :
    ThetaLowerSegment 1588482304 1588613376 (158844267970493 / 100000)
      (39714353475527 / 25000) := by
  exact
    packedTile65536 1588482304 1588613376 14 6205 39855 31 _ _ (2118603 / 100000) (1059303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588613376 :
    ThetaLowerSegment 1588613376 1588744448 (39714353475527 / 25000)
      (158870390394483 / 100000) := by
  exact
    packedTile65536 1588613376 1588744448 14 6125 39857 31 _ _ (2118611 / 100000) (1059307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588744448 :
    ThetaLowerSegment 1588744448 1588875520 (158870390394483 / 100000)
      (79441759738213 / 50000) := by
  exact
    packedTile65536 1588744448 1588875520 14 6197 39859 31 _ _ (2118619 / 100000) (1059311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1588875520 :
    ThetaLowerSegment 1588875520 1589006592 (79441759738213 / 50000) (79448333840897 / 50000) := by
  exact
    packedTile65536 1588875520 1589006592 14 6206 39860 31 _ _ (529657 / 25000) (2118631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589006592 :
    ThetaLowerSegment 1589006592 1589137664 (79448333840897 / 50000) (79454852883869 / 50000) := by
  exact
    packedTile65536 1589006592 1589137664 14 6154 39862 31 _ _ (529659 / 25000) (2118639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589137664 :
    ThetaLowerSegment 1589137664 1589268736 (79454852883869 / 50000) (79461374070101 / 50000) := by
  exact
    packedTile65536 1589137664 1589268736 14 6156 39863 31 _ _ (529661 / 25000) (2118647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589268736 :
    ThetaLowerSegment 1589268736 1589399808 (79461374070101 / 50000) (79468021340751 / 50000) := by
  exact
    packedTile65536 1589268736 1589399808 14 6275 39865 31 _ _ (529663 / 25000) (423731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589399808 :
    ThetaLowerSegment 1589399808 1589530880 (79468021340751 / 50000)
      (158949066090669 / 100000) := by
  exact
    packedTile65536 1589399808 1589530880 14 6147 39867 31 _ _ (2118661 / 100000) (264833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589530880 :
    ThetaLowerSegment 1589530880 1589661952 (158949066090669 / 100000)
      (31792433587953 / 20000) := by
  exact
    packedTile65536 1589530880 1589661952 14 6184 39868 31 _ _ (2118669 / 100000) (132417 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589661952 :
    ThetaLowerSegment 1589661952 1589793024 (31792433587953 / 20000) (31795056510079 / 20000) := by
  exact
    packedTile65536 1589661952 1589793024 14 6190 39870 31 _ _ (2118677 / 100000) (52967 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589793024 :
    ThetaLowerSegment 1589793024 1589924096 (31795056510079 / 20000) (3974707546743 / 2500) := by
  exact
    packedTile65536 1589793024 1589924096 14 6145 39872 31 _ _ (423737 / 20000) (66209 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1589924096 :
    ThetaLowerSegment 1589924096 1590055168 (3974707546743 / 2500) (39750366858559 / 25000) := by
  exact
    packedTile65536 1589924096 1590055168 14 6214 39873 31 _ _ (1059347 / 50000) (2118697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590055168 :
    ThetaLowerSegment 1590055168 1590186240 (39750366858559 / 25000) (993840503137 / 625) := by
  exact
    packedTile65536 1590055168 1590186240 14 6142 39875 31 _ _ (1059351 / 50000) (423741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590186240 :
    ThetaLowerSegment 1590186240 1590317312 (993840503137 / 625) (15902760591037 / 10000) := by
  exact
    packedTile65536 1590186240 1590317312 14 6195 39877 31 _ _ (211871 / 10000) (2118713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590317312 :
    ThetaLowerSegment 1590317312 1590448384 (15902760591037 / 10000) (79520324369189 / 50000) := by
  exact
    packedTile65536 1590317312 1590448384 14 6156 39878 31 _ _ (1059359 / 50000) (2118721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590448384 :
    ThetaLowerSegment 1590448384 1590579456 (79520324369189 / 50000)
      (159053884425947 / 100000) := by
  exact
    packedTile65536 1590448384 1590579456 14 6247 39880 31 _ _ (2118727 / 100000) (211873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590579456 :
    ThetaLowerSegment 1590579456 1590710528 (159053884425947 / 100000)
      (159066901933787 / 100000) := by
  exact
    packedTile65536 1590579456 1590710528 14 6144 39882 31 _ _ (423747 / 20000) (1059369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590710528 :
    ThetaLowerSegment 1590710528 1590841600 (159066901933787 / 100000)
      (19885001324591 / 12500) := by
  exact
    packedTile65536 1590710528 1590841600 14 6187 39883 31 _ _ (2118743 / 100000) (1059373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590841600 :
    ThetaLowerSegment 1590841600 1590972672 (19885001324591 / 12500)
      (159093178634193 / 100000) := by
  exact
    packedTile65536 1590841600 1590972672 14 6215 39885 31 _ _ (2118751 / 100000) (1059377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1590972672 :
    ThetaLowerSegment 1590972672 1591103744 (159093178634193 / 100000)
      (159106202651913 / 100000) := by
  exact
    packedTile65536 1590972672 1591103744 14 6147 39886 31 _ _ (52969 / 2500) (2118763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591103744 :
    ThetaLowerSegment 1591103744 1591234816 (159106202651913 / 100000)
      (159119419526697 / 100000) := by
  exact
    packedTile65536 1591103744 1591234816 14 6238 39888 31 _ _ (132423 / 6250) (2118771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591234816 :
    ThetaLowerSegment 1591234816 1591365888 (159119419526697 / 100000) (1273060922109 / 800) := by
  exact
    packedTile65536 1591234816 1591365888 14 6228 39890 31 _ _ (264847 / 12500) (2118779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591365888 :
    ThetaLowerSegment 1591365888 1591496960 (1273060922109 / 800) (159145628834953 / 100000) := by
  exact
    packedTile65536 1591365888 1591496960 14 6142 39891 31 _ _ (66212 / 3125) (2118787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591496960 :
    ThetaLowerSegment 1591496960 1591628032 (159145628834953 / 100000)
      (159158714500521 / 100000) := by
  exact
    packedTile65536 1591496960 1591628032 14 6176 39893 31 _ _ (2118793 / 100000) (529699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591628032 :
    ThetaLowerSegment 1591628032 1591759104 (159158714500521 / 100000)
      (159171829878711 / 100000) := by
  exact
    packedTile65536 1591628032 1591759104 14 6190 39895 31 _ _ (2118801 / 100000) (529701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591759104 :
    ThetaLowerSegment 1591759104 1591890176 (159171829878711 / 100000)
      (159185102098287 / 100000) := by
  exact
    packedTile65536 1591759104 1591890176 14 6264 39896 31 _ _ (2118809 / 100000) (529703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1591890176 :
    ThetaLowerSegment 1591890176 1592021248 (159185102098287 / 100000) (7959915010469 / 5000) := by
  exact
    packedTile65536 1591890176 1592021248 14 6229 39898 31 _ _ (2118817 / 100000) (105941 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592021248 :
    ThetaLowerSegment 1592021248 1592152320 (7959915010469 / 5000) (39802897371513 / 25000) := by
  exact
    packedTile65536 1592021248 1592152320 14 6272 39900 31 _ _ (1059413 / 50000) (2118829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592152320 :
    ThetaLowerSegment 1592152320 1592283392 (39802897371513 / 25000) (79612342999503 / 50000) := by
  exact
    packedTile65536 1592152320 1592283392 14 6181 39901 31 _ _ (1059417 / 50000) (2118837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592283392 :
    ThetaLowerSegment 1592283392 1592414464 (79612342999503 / 50000) (79618841487917 / 50000) := by
  exact
    packedTile65536 1592283392 1592414464 14 6134 39903 31 _ _ (1059421 / 50000) (423769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592414464 :
    ThetaLowerSegment 1592414464 1592545536 (79618841487917 / 50000) (39812703372321 / 25000) := by
  exact
    packedTile65536 1592414464 1592545536 14 6197 39905 31 _ _ (42377 / 2000) (2118853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592545536 :
    ThetaLowerSegment 1592545536 1592676608 (39812703372321 / 25000) (39815955819351 / 25000) := by
  exact
    packedTile65536 1592545536 1592676608 14 6140 39906 31 _ _ (1059429 / 50000) (2118861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592676608 :
    ThetaLowerSegment 1592676608 1592807680 (39815955819351 / 25000)
      (159276936945267 / 100000) := by
  exact
    packedTile65536 1592676608 1592807680 14 6189 39908 31 _ _ (2118867 / 100000) (211887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592807680 :
    ThetaLowerSegment 1592807680 1592938752 (159276936945267 / 100000)
      (79644987191571 / 50000) := by
  exact
    packedTile65536 1592807680 1592938752 14 6153 39909 31 _ _ (16951 / 800) (1059439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1592938752 :
    ThetaLowerSegment 1592938752 1593069824 (79644987191571 / 50000)
      (159303151716519 / 100000) := by
  exact
    packedTile65536 1592938752 1593069824 14 6219 39911 31 _ _ (2118883 / 100000) (1059443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593069824 :
    ThetaLowerSegment 1593069824 1593200896 (159303151716519 / 100000)
      (31863234884121 / 20000) := by
  exact
    packedTile65536 1593069824 1593200896 14 6146 39913 31 _ _ (2118891 / 100000) (1059447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593200896 :
    ThetaLowerSegment 1593200896 1593331968 (31863234884121 / 20000) (31865866557921 / 20000) := by
  exact
    packedTile65536 1593200896 1593331968 14 6210 39914 31 _ _ (21189 / 1000) (2118903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593331968 :
    ThetaLowerSegment 1593331968 1593463040 (31865866557921 / 20000)
      (159342503921733 / 100000) := by
  exact
    packedTile65536 1593331968 1593463040 14 6216 39916 31 _ _ (529727 / 25000) (2118911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593463040 :
    ThetaLowerSegment 1593463040 1593594112 (159342503921733 / 100000)
      (159355520422721 / 100000) := by
  exact
    packedTile65536 1593463040 1593594112 14 6143 39918 31 _ _ (529729 / 25000) (2118919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593594112 :
    ThetaLowerSegment 1593594112 1593725184 (159355520422721 / 100000)
      (31873683238837 / 20000) := by
  exact
    packedTile65536 1593594112 1593725184 14 6086 39919 31 _ _ (529731 / 25000) (2118927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593725184 :
    ThetaLowerSegment 1593725184 1593856256 (31873683238837 / 20000)
      (159381417960937 / 100000) := by
  exact
    packedTile65536 1593725184 1593856256 14 6136 39921 31 _ _ (529733 / 25000) (423787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593856256 :
    ThetaLowerSegment 1593856256 1593987328 (159381417960937 / 100000)
      (79697316897977 / 50000) := by
  exact
    packedTile65536 1593856256 1593987328 14 6237 39923 31 _ _ (2118941 / 100000) (66217 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593987328 :
    ThetaLowerSegment 1593987328 1594118400 (79697316897977 / 50000) (39851863359351 / 25000) := by
  exact
    packedTile65536 1593987328 1594118400 14 6050 39924 31 _ _ (2118949 / 100000) (264869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594118400 :
    ThetaLowerSegment 1594118400 1594249472 (39851863359351 / 25000)
      (159420656658471 / 100000) := by
  exact
    packedTile65536 1594118400 1594249472 14 6231 39926 31 _ _ (2118957 / 100000) (26487 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594249472 :
    ThetaLowerSegment 1594249472 1594380544 (159420656658471 / 100000)
      (79716840968163 / 50000) := by
  exact
    packedTile65536 1594249472 1594380544 14 6147 39928 31 _ _ (423793 / 20000) (264871 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594380544 :
    ThetaLowerSegment 1594380544 1594511616 (79716840968163 / 50000) (79723284768097 / 50000) := by
  exact
    packedTile65536 1594380544 1594511616 14 6082 39929 31 _ _ (1059487 / 50000) (2118977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594511616 :
    ThetaLowerSegment 1594511616 1594642688 (79723284768097 / 50000) (79729762496071 / 50000) := by
  exact
    packedTile65536 1594511616 1594642688 14 6114 39931 31 _ _ (1059491 / 50000) (423797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594642688 :
    ThetaLowerSegment 1594642688 1594773760 (79729762496071 / 50000) (9967056121127 / 6250) := by
  exact
    packedTile65536 1594642688 1594773760 14 6311 39932 31 _ _ (211899 / 10000) (2118993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594773760 :
    ThetaLowerSegment 1594773760 1594904832 (9967056121127 / 6250) (9967878292351 / 6250) := by
  exact
    packedTile65536 1594773760 1594904832 14 6208 39934 31 _ _ (1059499 / 50000) (2119001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1594904832 :
    ThetaLowerSegment 1594904832 1595035904 (9967878292351 / 6250) (79749606911941 / 50000) := by
  exact
    packedTile65536 1594904832 1595035904 14 6211 39936 31 _ _ (1059503 / 50000) (2119009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595035904 :
    ThetaLowerSegment 1595035904 1595166976 (79749606911941 / 50000) (79756214000711 / 50000) := by
  exact
    packedTile65536 1595035904 1595166976 14 6236 39937 31 _ _ (423803 / 20000) (1059509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595166976 :
    ThetaLowerSegment 1595166976 1595298048 (79756214000711 / 50000) (31905109374563 / 20000) := by
  exact
    packedTile65536 1595166976 1595298048 14 6191 39939 31 _ _ (2119023 / 100000) (1059513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595298048 :
    ThetaLowerSegment 1595298048 1595429120 (31905109374563 / 20000) (19942345938403 / 12500) := by
  exact
    packedTile65536 1595298048 1595429120 14 6239 39941 31 _ _ (2119031 / 100000) (1059517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595429120 :
    ThetaLowerSegment 1595429120 1595560192 (19942345938403 / 12500) (1276415396963 / 800) := by
  exact
    packedTile65536 1595429120 1595560192 14 6209 39942 31 _ _ (2119039 / 100000) (1059521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595560192 :
    ThetaLowerSegment 1595560192 1595691264 (1276415396963 / 800) (159565119932271 / 100000) := by
  exact
    packedTile65536 1595560192 1595691264 14 6227 39944 31 _ _ (264881 / 12500) (2119051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595691264 :
    ThetaLowerSegment 1595691264 1595822336 (159565119932271 / 100000) (6383124728871 / 4000) := by
  exact
    packedTile65536 1595691264 1595822336 14 6134 39946 31 _ _ (132441 / 6250) (2119059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595822336 :
    ThetaLowerSegment 1595822336 1595953408 (6383124728871 / 4000) (159591451372463 / 100000) := by
  exact
    packedTile65536 1595822336 1595953408 14 6292 39947 31 _ _ (264883 / 12500) (2119067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595953408 :
    ThetaLowerSegment 1595953408 1596084480 (159591451372463 / 100000)
      (159604536642063 / 100000) := by
  exact
    packedTile65536 1595953408 1596084480 14 6175 39949 31 _ _ (66221 / 3125) (84763 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596084480 :
    ThetaLowerSegment 1596084480 1596215552 (159604536642063 / 100000)
      (159617395219503 / 100000) := by
  exact
    packedTile65536 1596084480 1596215552 14 6068 39951 31 _ _ (52977 / 2500) (2119083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596215552 :
    ThetaLowerSegment 1596215552 1596346624 (159617395219503 / 100000)
      (31926118581159 / 20000) := by
  exact
    packedTile65536 1596215552 1596346624 14 6228 39952 31 _ _ (2119089 / 100000) (529773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596346624 :
    ThetaLowerSegment 1596346624 1596477696 (31926118581159 / 20000) (39910890974633 / 25000) := by
  exact
    packedTile65536 1596346624 1596477696 14 6121 39954 31 _ _ (2119097 / 100000) (21191 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596477696 :
    ThetaLowerSegment 1596477696 1596608768 (39910890974633 / 25000)
      (159656560369497 / 100000) := by
  exact
    packedTile65536 1596477696 1596608768 14 6133 39955 31 _ _ (423821 / 20000) (529777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596608768 :
    ThetaLowerSegment 1596608768 1596739840 (159656560369497 / 100000)
      (79834854732831 / 50000) := by
  exact
    packedTile65536 1596608768 1596739840 14 6205 39957 31 _ _ (2119113 / 100000) (529779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596739840 :
    ThetaLowerSegment 1596739840 1596870912 (79834854732831 / 50000) (79841466390351 / 50000) := by
  exact
    packedTile65536 1596739840 1596870912 14 6240 39959 31 _ _ (2119121 / 100000) (529781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1596870912 :
    ThetaLowerSegment 1596870912 1597001984 (79841466390351 / 50000) (4990499913036 / 3125) := by
  exact
    packedTile65536 1596870912 1597001984 14 6165 39960 31 _ _ (211913 / 10000) (2119133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597001984 :
    ThetaLowerSegment 1597001984 1597133056 (4990499913036 / 3125) (79854477873011 / 50000) := by
  exact
    packedTile65536 1597001984 1597133056 14 6115 39962 31 _ _ (1059569 / 50000) (2119141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597133056 :
    ThetaLowerSegment 1597133056 1597264128 (79854477873011 / 50000) (79861032391589 / 50000) := by
  exact
    packedTile65536 1597133056 1597264128 14 6186 39964 31 _ _ (1059573 / 50000) (2119149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597264128 :
    ThetaLowerSegment 1597264128 1597395200 (79861032391589 / 50000) (19966915011431 / 12500) := by
  exact
    packedTile65536 1597264128 1597395200 14 6255 39965 31 _ _ (1059577 / 50000) (2119157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597395200 :
    ThetaLowerSegment 1597395200 1597526272 (19966915011431 / 12500) (9984280800541 / 6250) := by
  exact
    packedTile65536 1597395200 1597526272 14 6216 39967 31 _ _ (2119163 / 100000) (1059583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597526272 :
    ThetaLowerSegment 1597526272 1597657344 (9984280800541 / 6250) (31952308956569 / 20000) := by
  exact
    packedTile65536 1597526272 1597657344 14 6159 39969 31 _ _ (2119171 / 100000) (1059587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597657344 :
    ThetaLowerSegment 1597657344 1597788416 (31952308956569 / 20000) (31954949453603 / 20000) := by
  exact
    packedTile65536 1597657344 1597788416 14 6230 39970 31 _ _ (2119179 / 100000) (1059591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597788416 :
    ThetaLowerSegment 1597788416 1597919488 (31954949453603 / 20000) (79893922981431 / 50000) := by
  exact
    packedTile65536 1597788416 1597919488 14 6181 39972 31 _ _ (2119187 / 100000) (211919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597919488 :
    ThetaLowerSegment 1597919488 1598050560 (79893922981431 / 50000) (39950251540953 / 25000) := by
  exact
    packedTile65536 1597919488 1598050560 14 6210 39973 31 _ _ (423839 / 20000) (1059599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598050560 :
    ThetaLowerSegment 1598050560 1598181632 (39950251540953 / 25000) (39953514055511 / 25000) := by
  exact
    packedTile65536 1598050560 1598181632 14 6158 39975 31 _ _ (529801 / 25000) (2119207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598181632 :
    ThetaLowerSegment 1598181632 1598312704 (39953514055511 / 25000) (19978394383927 / 12500) := by
  exact
    packedTile65536 1598181632 1598312704 14 6181 39977 31 _ _ (529803 / 25000) (423843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598312704 :
    ThetaLowerSegment 1598312704 1598443776 (19978394383927 / 12500) (39960048658019 / 25000) := by
  exact
    packedTile65536 1598312704 1598443776 14 6153 39978 31 _ _ (105961 / 5000) (2119223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598443776 :
    ThetaLowerSegment 1598443776 1598574848 (39960048658019 / 25000) (3996330856049 / 2500) := by
  exact
    packedTile65536 1598443776 1598574848 14 6153 39980 31 _ _ (529807 / 25000) (2119231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598574848 :
    ThetaLowerSegment 1598574848 1598705920 (3996330856049 / 2500) (159866246351 / 100) := by
  exact
    packedTile65536 1598574848 1598705920 14 6140 39982 31 _ _ (529809 / 25000) (2119239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598705920 :
    ThetaLowerSegment 1598705920 1598836992 (159866246351 / 100) (1279035509209 / 800) := by
  exact
    packedTile65536 1598705920 1598836992 14 6225 39983 31 _ _ (423849 / 20000) (132453 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598836992 :
    ThetaLowerSegment 1598836992 1598968064 (1279035509209 / 800) (159892306755341 / 100000) := by
  exact
    packedTile65536 1598836992 1598968064 14 6072 39985 31 _ _ (2119253 / 100000) (264907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1598968064 :
    ThetaLowerSegment 1598968064 1599099136 (159892306755341 / 100000)
      (159905590283289 / 100000) := by
  exact
    packedTile65536 1598968064 1599099136 14 6268 39987 31 _ _ (2119261 / 100000) (66227 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599099136 :
    ThetaLowerSegment 1599099136 1599230208 (159905590283289 / 100000)
      (31983760361247 / 20000) := by
  exact
    packedTile65536 1599099136 1599230208 14 6234 39988 31 _ _ (2119269 / 100000) (264909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599230208 :
    ThetaLowerSegment 1599230208 1599361280 (31983760361247 / 20000)
      (159931805689907 / 100000) := by
  exact
    packedTile65536 1599230208 1599361280 14 6136 39990 31 _ _ (2119277 / 100000) (26491 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599361280 :
    ThetaLowerSegment 1599361280 1599492352 (159931805689907 / 100000)
      (31989017874911 / 20000) := by
  exact
    packedTile65536 1599361280 1599492352 14 6268 39992 31 _ _ (1059643 / 50000) (2119289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599492352 :
    ThetaLowerSegment 1599492352 1599623424 (31989017874911 / 20000) (31991639441589 / 20000) := by
  exact
    packedTile65536 1599492352 1599623424 14 6185 39993 31 _ _ (1059647 / 50000) (2119297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599623424 :
    ThetaLowerSegment 1599623424 1599754496 (31991639441589 / 20000)
      (159971224557339 / 100000) := by
  exact
    packedTile65536 1599623424 1599754496 14 6147 39995 31 _ _ (1059651 / 50000) (423861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599754496 :
    ThetaLowerSegment 1599754496 1599885568 (159971224557339 / 100000)
      (159984173541439 / 100000) := by
  exact
    packedTile65536 1599754496 1599885568 14 6110 39996 31 _ _ (211931 / 10000) (2119313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599885568 :
    ThetaLowerSegment 1599885568 1600016640 (159984173541439 / 100000)
      (159997457426663 / 100000) := by
  exact
    packedTile65536 1599885568 1600016640 14 6268 39998 31 _ _ (1059659 / 50000) (2119321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600016640 :
    ThetaLowerSegment 1600016640 1600147712 (159997457426663 / 100000)
      (160010631157079 / 100000) := by
  exact
    packedTile65536 1600016640 1600147712 14 6216 40000 31 _ _ (1059663 / 50000) (2119329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600147712 :
    ThetaLowerSegment 1600147712 1600278784 (160010631157079 / 100000)
      (80011928963407 / 50000) := by
  exact
    packedTile65536 1600147712 1600278784 14 6241 40001 31 _ _ (423867 / 20000) (1059669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600278784 :
    ThetaLowerSegment 1600278784 1600409856 (80011928963407 / 50000) (5001148102924 / 3125) := by
  exact
    packedTile65536 1600278784 1600409856 14 6078 40003 31 _ _ (2119343 / 100000) (1059673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600409856 :
    ThetaLowerSegment 1600409856 1600540928 (5001148102924 / 3125) (80024958709043 / 50000) := by
  exact
    packedTile65536 1600409856 1600540928 14 6218 40005 31 _ _ (2119351 / 100000) (1059677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600540928 :
    ThetaLowerSegment 1600540928 1600672000 (80024958709043 / 50000)
      (160062979027603 / 100000) := by
  exact
    packedTile65536 1600540928 1600672000 14 6163 40006 31 _ _ (2119359 / 100000) (1059681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600672000 :
    ThetaLowerSegment 1600672000 1600803072 (160062979027603 / 100000)
      (160076080954397 / 100000) := by
  exact
    packedTile65536 1600672000 1600803072 14 6182 40008 31 _ _ (2119367 / 100000) (211937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600803072 :
    ThetaLowerSegment 1600803072 1600934144 (160076080954397 / 100000)
      (160089221085597 / 100000) := by
  exact
    packedTile65536 1600803072 1600934144 14 6200 40010 31 _ _ (132461 / 6250) (2119379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1600934144 :
    ThetaLowerSegment 1600934144 1601065216 (160089221085597 / 100000)
      (160102454519293 / 100000) := by
  exact
    packedTile65536 1600934144 1601065216 14 6244 40011 31 _ _ (264923 / 12500) (2119387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601065216 :
    ThetaLowerSegment 1601065216 1601196288 (160102454519293 / 100000)
      (32023081224761 / 20000) := by
  exact
    packedTile65536 1601065216 1601196288 14 6111 40013 31 _ _ (66231 / 3125) (423879 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601196288 :
    ThetaLowerSegment 1601196288 1601327360 (32023081224761 / 20000) (32025725812081 / 20000) := by
  exact
    packedTile65536 1601196288 1601327360 14 6239 40014 31 _ _ (10597 / 500) (2119403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601327360 :
    ThetaLowerSegment 1601327360 1601458432 (32025725812081 / 20000) (32028288176353 / 20000) := by
  exact
    packedTile65536 1601327360 1601458432 14 6045 40016 31 _ _ (132463 / 6250) (2119411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601458432 :
    ThetaLowerSegment 1601458432 1601589504 (32028288176353 / 20000)
      (160154572789497 / 100000) := by
  exact
    packedTile65536 1601458432 1601589504 14 6196 40018 31 _ _ (2119417 / 100000) (105971 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601589504 :
    ThetaLowerSegment 1601589504 1601720576 (160154572789497 / 100000)
      (40041938373393 / 25000) := by
  exact
    packedTile65536 1601589504 1601720576 14 6219 40019 31 _ _ (84777 / 4000) (529857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601720576 :
    ThetaLowerSegment 1601720576 1601851648 (40041938373393 / 25000) (1601809278891 / 1000) := by
  exact
    packedTile65536 1601720576 1601851648 14 6216 40021 31 _ _ (2119433 / 100000) (529859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601851648 :
    ThetaLowerSegment 1601851648 1601982720 (1601809278891 / 1000) (160193981526219 / 100000) := by
  exact
    packedTile65536 1601851648 1601982720 14 6159 40023 31 _ _ (2119441 / 100000) (529861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601982720 :
    ThetaLowerSegment 1601982720 1602113792 (160193981526219 / 100000)
      (40051747146183 / 25000) := by
  exact
    packedTile65536 1601982720 1602113792 14 6137 40024 31 _ _ (2119449 / 100000) (529863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602113792 :
    ThetaLowerSegment 1602113792 1602244864 (40051747146183 / 25000) (20027508734167 / 12500) := by
  exact
    packedTile65536 1602113792 1602244864 14 6172 40026 31 _ _ (2119457 / 100000) (105973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602244864 :
    ThetaLowerSegment 1602244864 1602375936 (20027508734167 / 12500) (80116544876487 / 50000) := by
  exact
    packedTile65536 1602244864 1602375936 14 6143 40028 31 _ _ (1059733 / 50000) (2119469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602375936 :
    ThetaLowerSegment 1602375936 1602507008 (80116544876487 / 50000) (20030758941403 / 12500) := by
  exact
    packedTile65536 1602375936 1602507008 14 6125 40029 31 _ _ (1059737 / 50000) (2119477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602507008 :
    ThetaLowerSegment 1602507008 1602638080 (20030758941403 / 12500) (80129600861107 / 50000) := by
  exact
    packedTile65536 1602507008 1602638080 14 6195 40031 31 _ _ (1059741 / 50000) (423897 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602638080 :
    ThetaLowerSegment 1602638080 1602769152 (80129600861107 / 50000) (80136228506337 / 50000) := by
  exact
    packedTile65536 1602638080 1602769152 14 6254 40032 31 _ _ (211949 / 10000) (2119493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602769152 :
    ThetaLowerSegment 1602769152 1602900224 (80136228506337 / 50000) (16028560213927 / 10000) := by
  exact
    packedTile65536 1602769152 1602900224 14 6202 40034 31 _ _ (1059749 / 50000) (2119501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1602900224 :
    ThetaLowerSegment 1602900224 1603031296 (16028560213927 / 10000)
      (160298779114289 / 100000) := by
  exact
    packedTile65536 1602900224 1603031296 14 6217 40036 31 _ _ (2119507 / 100000) (211951 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603031296 :
    ThetaLowerSegment 1603031296 1603162368 (160298779114289 / 100000)
      (160311966736619 / 100000) := by
  exact
    packedTile65536 1603031296 1603162368 14 6222 40037 31 _ _ (423903 / 20000) (1059759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603162368 :
    ThetaLowerSegment 1603162368 1603293440 (160311966736619 / 100000)
      (160325116257311 / 100000) := by
  exact
    packedTile65536 1603162368 1603293440 14 6204 40039 31 _ _ (2119523 / 100000) (1059763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603293440 :
    ThetaLowerSegment 1603293440 1603424512 (160325116257311 / 100000)
      (32067699795209 / 20000) := by
  exact
    packedTile65536 1603293440 1603424512 14 6314 40041 31 _ _ (2119531 / 100000) (1059767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603424512 :
    ThetaLowerSegment 1603424512 1603555584 (32067699795209 / 20000) (1603517354971 / 1000) := by
  exact
    packedTile65536 1603424512 1603555584 14 6245 40042 31 _ _ (2119539 / 100000) (1059771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603555584 :
    ThetaLowerSegment 1603555584 1603686656 (1603517354971 / 1000) (10022803203371 / 6250) := by
  exact
    packedTile65536 1603555584 1603686656 14 6188 40044 31 _ _ (2119547 / 100000) (42391 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603686656 :
    ThetaLowerSegment 1603686656 1603817728 (10022803203371 / 6250) (40094491236727 / 25000) := by
  exact
    packedTile65536 1603686656 1603817728 14 6187 40046 31 _ _ (529889 / 25000) (2119559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603817728 :
    ThetaLowerSegment 1603817728 1603948800 (40094491236727 / 25000) (10024435529503 / 6250) := by
  exact
    packedTile65536 1603817728 1603948800 14 6135 40047 31 _ _ (529891 / 25000) (2119567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603948800 :
    ThetaLowerSegment 1603948800 1604079872 (10024435529503 / 6250) (1604038787851 / 1000) := by
  exact
    packedTile65536 1603948800 1604079872 14 6091 40049 31 _ _ (529893 / 25000) (84783 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604079872 :
    ThetaLowerSegment 1604079872 1604210944 (1604038787851 / 1000) (8020857579753 / 5000) := by
  exact
    packedTile65536 1604079872 1604210944 14 6262 40050 31 _ _ (105979 / 5000) (2119583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604210944 :
    ThetaLowerSegment 1604210944 1604342016 (8020857579753 / 5000) (40107563722019 / 25000) := by
  exact
    packedTile65536 1604210944 1604342016 14 6182 40052 31 _ _ (529897 / 25000) (2119591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604342016 :
    ThetaLowerSegment 1604342016 1604473088 (40107563722019 / 25000) (40110839557637 / 25000) := by
  exact
    packedTile65536 1604342016 1604473088 14 6182 40054 31 _ _ (529899 / 25000) (2119599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604473088 :
    ThetaLowerSegment 1604473088 1604604160 (40110839557637 / 25000)
      (160456319615123 / 100000) := by
  exact
    packedTile65536 1604473088 1604604160 14 6115 40055 31 _ _ (423921 / 20000) (264951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604604160 :
    ThetaLowerSegment 1604604160 1604735232 (160456319615123 / 100000)
      (80234759222637 / 50000) := by
  exact
    packedTile65536 1604604160 1604735232 14 6227 40057 31 _ _ (2119613 / 100000) (66238 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604735232 :
    ThetaLowerSegment 1604735232 1604866304 (80234759222637 / 50000) (80241342765463 / 50000) := by
  exact
    packedTile65536 1604735232 1604866304 14 6212 40059 31 _ _ (2119621 / 100000) (264953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604866304 :
    ThetaLowerSegment 1604866304 1604997376 (80241342765463 / 50000)
      (160495782718517 / 100000) := by
  exact
    packedTile65536 1604866304 1604997376 14 6179 40060 31 _ _ (2119629 / 100000) (132477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1604997376 :
    ThetaLowerSegment 1604997376 1605128448 (160495782718517 / 100000)
      (80254446336681 / 50000) := by
  exact
    packedTile65536 1604997376 1605128448 14 6185 40062 31 _ _ (2119637 / 100000) (52991 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605128448 :
    ThetaLowerSegment 1605128448 1605259520 (80254446336681 / 50000)
      (160521922131177 / 100000) := by
  exact
    packedTile65536 1605128448 1605259520 14 6147 40064 31 _ _ (423929 / 20000) (66239 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605259520 :
    ThetaLowerSegment 1605259520 1605390592 (160521922131177 / 100000)
      (160535159370407 / 100000) := by
  exact
    packedTile65536 1605259520 1605390592 14 6245 40065 31 _ _ (1059827 / 50000) (2119657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605390592 :
    ThetaLowerSegment 1605390592 1605521664 (160535159370407 / 100000)
      (160548305514131 / 100000) := by
  exact
    packedTile65536 1605390592 1605521664 14 6202 40067 31 _ _ (1059831 / 50000) (423933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605521664 :
    ThetaLowerSegment 1605521664 1605652736 (160548305514131 / 100000)
      (160561381758361 / 100000) := by
  exact
    packedTile65536 1605521664 1605652736 14 6169 40068 31 _ _ (211967 / 10000) (2119673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605652736 :
    ThetaLowerSegment 1605652736 1605783808 (160561381758361 / 100000)
      (160574438974841 / 100000) := by
  exact
    packedTile65536 1605652736 1605783808 14 6160 40070 31 _ _ (1059839 / 50000) (2119681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605783808 :
    ThetaLowerSegment 1605783808 1605914880 (160574438974841 / 100000)
      (160587517437461 / 100000) := by
  exact
    packedTile65536 1605783808 1605914880 14 6170 40072 31 _ _ (1059843 / 50000) (2119689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1605914880 :
    ThetaLowerSegment 1605914880 1606045952 (160587517437461 / 100000)
      (160600553555561 / 100000) := by
  exact
    packedTile65536 1605914880 1606045952 14 6150 40073 31 _ _ (1059847 / 50000) (2119697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606045952 :
    ThetaLowerSegment 1606045952 1606177024 (160600553555561 / 100000) (6424546811109 / 4000) := by
  exact
    packedTile65536 1606045952 1606177024 14 6188 40075 31 _ _ (2119703 / 100000) (1059853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606177024 :
    ThetaLowerSegment 1606177024 1606308096 (6424546811109 / 4000) (160626829443613 / 100000) := by
  exact
    packedTile65536 1606177024 1606308096 14 6208 40077 31 _ _ (2119711 / 100000) (1059857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606308096 :
    ThetaLowerSegment 1606308096 1606439168 (160626829443613 / 100000)
      (80319921199277 / 50000) := by
  exact
    packedTile65536 1606308096 1606439168 14 6139 40078 31 _ _ (2119719 / 100000) (1059861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606439168 :
    ThetaLowerSegment 1606439168 1606570240 (80319921199277 / 50000) (80326471155707 / 50000) := by
  exact
    packedTile65536 1606439168 1606570240 14 6180 40080 31 _ _ (2119727 / 100000) (211973 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606570240 :
    ThetaLowerSegment 1606570240 1606701312 (80326471155707 / 50000) (80333135602547 / 50000) := by
  exact
    packedTile65536 1606570240 1606701312 14 6288 40082 31 _ _ (423947 / 20000) (1059869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606701312 :
    ThetaLowerSegment 1606701312 1606832384 (80333135602547 / 50000) (20084919812297 / 12500) := by
  exact
    packedTile65536 1606701312 1606832384 14 6174 40083 31 _ _ (2119743 / 100000) (1059873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606832384 :
    ThetaLowerSegment 1606832384 1606963456 (20084919812297 / 12500) (20086555730903 / 12500) := by
  exact
    packedTile65536 1606832384 1606963456 14 6174 40085 31 _ _ (264969 / 12500) (423951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1606963456 :
    ThetaLowerSegment 1606963456 1607094528 (20086555730903 / 12500) (20088190860773 / 12500) := by
  exact
    packedTile65536 1606963456 1607094528 14 6171 40086 31 _ _ (26497 / 1250) (2119763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607094528 :
    ThetaLowerSegment 1607094528 1607225600 (20088190860773 / 12500) (20089845339697 / 12500) := by
  exact
    packedTile65536 1607094528 1607225600 14 6244 40088 31 _ _ (264971 / 12500) (2119771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607225600 :
    ThetaLowerSegment 1607225600 1607356672 (20089845339697 / 12500) (20091479686993 / 12500) := by
  exact
    packedTile65536 1607225600 1607356672 14 6168 40090 31 _ _ (66243 / 3125) (2119779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607356672 :
    ThetaLowerSegment 1607356672 1607487744 (20091479686993 / 12500) (1004656377704 / 625) := by
  exact
    packedTile65536 1607356672 1607487744 14 6219 40091 31 _ _ (264973 / 12500) (2119787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607487744 :
    ThetaLowerSegment 1607487744 1607618816 (1004656377704 / 625) (10047374464993 / 6250) := by
  exact
    packedTile65536 1607487744 1607618816 14 6119 40093 31 _ _ (132487 / 6250) (423959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607618816 :
    ThetaLowerSegment 1607618816 1607749888 (10047374464993 / 6250) (20096403698861 / 12500) := by
  exact
    packedTile65536 1607618816 1607749888 14 6245 40095 31 _ _ (10599 / 500) (2119803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607749888 :
    ThetaLowerSegment 1607749888 1607880960 (20096403698861 / 12500)
      (160784234619103 / 100000) := by
  exact
    packedTile65536 1607749888 1607880960 14 6135 40096 31 _ _ (2119809 / 100000) (529953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607880960 :
    ThetaLowerSegment 1607880960 1608012032 (160784234619103 / 100000)
      (32159435644341 / 20000) := by
  exact
    packedTile65536 1607880960 1608012032 14 6106 40098 31 _ _ (2119817 / 100000) (105991 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608012032 :
    ThetaLowerSegment 1608012032 1608143104 (32159435644341 / 20000) (32162070162851 / 20000) := by
  exact
    packedTile65536 1608012032 1608143104 14 6214 40100 31 _ _ (84793 / 4000) (529957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608143104 :
    ThetaLowerSegment 1608143104 1608274176 (32162070162851 / 20000) (5025732127001 / 3125) := by
  exact
    packedTile65536 1608143104 1608274176 14 6169 40101 31 _ _ (2119833 / 100000) (529959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608274176 :
    ThetaLowerSegment 1608274176 1608405248 (5025732127001 / 3125) (160836458726659 / 100000) := by
  exact
    packedTile65536 1608274176 1608405248 14 6147 40103 31 _ _ (2119841 / 100000) (529961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608405248 :
    ThetaLowerSegment 1608405248 1608536320 (160836458726659 / 100000)
      (160849622988949 / 100000) := by
  exact
    packedTile65536 1608405248 1608536320 14 6210 40104 31 _ _ (2119849 / 100000) (529963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608536320 :
    ThetaLowerSegment 1608536320 1608667392 (160849622988949 / 100000)
      (160862672834797 / 100000) := by
  exact
    packedTile65536 1608536320 1608667392 14 6156 40106 31 _ _ (1059929 / 50000) (2119861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608667392 :
    ThetaLowerSegment 1608667392 1608798464 (160862672834797 / 100000)
      (160875720610027 / 100000) := by
  exact
    packedTile65536 1608667392 1608798464 14 6155 40108 31 _ _ (1059933 / 50000) (2119869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608798464 :
    ThetaLowerSegment 1608798464 1608929536 (160875720610027 / 100000)
      (160888728156891 / 100000) := by
  exact
    packedTile65536 1608798464 1608929536 14 6136 40109 31 _ _ (1059937 / 50000) (2119877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1608929536 :
    ThetaLowerSegment 1608929536 1609060608 (160888728156891 / 100000)
      (160901807828831 / 100000) := by
  exact
    packedTile65536 1608929536 1609060608 14 6170 40111 31 _ _ (1059941 / 50000) (423977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609060608 :
    ThetaLowerSegment 1609060608 1609191680 (160901807828831 / 100000)
      (160915018983311 / 100000) := by
  exact
    packedTile65536 1609060608 1609191680 14 6232 40113 31 _ _ (211989 / 10000) (2119893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609191680 :
    ThetaLowerSegment 1609191680 1609322752 (160915018983311 / 100000)
      (160928007598357 / 100000) := by
  exact
    packedTile65536 1609191680 1609322752 14 6127 40114 31 _ _ (1059949 / 50000) (2119901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609322752 :
    ThetaLowerSegment 1609322752 1609339136 (160928007598357 / 100000) (6437184155503 / 4000) := by
  exact
    packedTile65536 1609322752 1609339136 11 753 40116 31 _ _ (1059953 / 50000) (2119909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609339136 :
    ThetaLowerSegment 1609339136 1609341184 (6437184155503 / 4000) (160929803158833 / 100000) := by
  exact
    packedTile65536 1609339136 1609341184 8 94 40116 31 _ _ (2119907 / 100000) (211991 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1577341184_1609341184 :
    ThetaLowerSegment 1577341184 1609341184 (157729148577773 / 100000)
      (160929803158833 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1577341184 cell1577472256)
                  (ThetaLowerSegment.join cell1577603328 cell1577734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1577865472 cell1577996544)
                  (ThetaLowerSegment.join cell1578127616 cell1578258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1578389760 cell1578520832)
                  (ThetaLowerSegment.join cell1578651904 cell1578782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1578914048 cell1579045120)
                  (ThetaLowerSegment.join cell1579176192 cell1579307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1579438336 cell1579569408)
                  (ThetaLowerSegment.join cell1579700480 cell1579831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1579962624 cell1580093696)
                  (ThetaLowerSegment.join cell1580224768 cell1580355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1580486912 cell1580617984)
                  (ThetaLowerSegment.join cell1580749056 cell1580880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1581011200 cell1581142272)
                  (ThetaLowerSegment.join cell1581273344 cell1581404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1581535488 cell1581666560)
                  (ThetaLowerSegment.join cell1581797632 cell1581928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1582059776 cell1582190848)
                  (ThetaLowerSegment.join cell1582321920 cell1582452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1582584064 cell1582715136)
                  (ThetaLowerSegment.join cell1582846208 cell1582977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1583108352 cell1583239424)
                  (ThetaLowerSegment.join cell1583370496 cell1583501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1583632640 cell1583763712)
                  (ThetaLowerSegment.join cell1583894784 cell1584025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1584156928 cell1584288000)
                  (ThetaLowerSegment.join cell1584419072 cell1584550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1584681216 cell1584812288)
                  (ThetaLowerSegment.join cell1584943360 cell1585074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1585205504 cell1585336576)
                  (ThetaLowerSegment.join cell1585467648 cell1585598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1585729792 cell1585860864)
                  (ThetaLowerSegment.join cell1585991936 cell1586123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1586254080 cell1586385152)
                  (ThetaLowerSegment.join cell1586516224 cell1586647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1586778368 cell1586909440)
                  (ThetaLowerSegment.join cell1587040512 cell1587171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1587302656 cell1587433728)
                  (ThetaLowerSegment.join cell1587564800 cell1587695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1587826944 cell1587958016)
                  (ThetaLowerSegment.join cell1588089088 cell1588220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1588351232 cell1588482304)
                  (ThetaLowerSegment.join cell1588613376 cell1588744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1588875520 cell1589006592)
                  (ThetaLowerSegment.join cell1589137664 cell1589268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1589399808 cell1589530880)
                  (ThetaLowerSegment.join cell1589661952 cell1589793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1589924096 cell1590055168)
                  (ThetaLowerSegment.join cell1590186240 cell1590317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1590448384 cell1590579456)
                  (ThetaLowerSegment.join cell1590710528 cell1590841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1590972672 cell1591103744)
                  (ThetaLowerSegment.join cell1591234816 cell1591365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1591496960 cell1591628032)
                  (ThetaLowerSegment.join cell1591759104 cell1591890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1592021248 cell1592152320)
                  (ThetaLowerSegment.join cell1592283392 cell1592414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1592545536 cell1592676608)
                  (ThetaLowerSegment.join cell1592807680 cell1592938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1593069824 cell1593200896)
                  (ThetaLowerSegment.join cell1593331968 cell1593463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1593594112 cell1593725184)
                  (ThetaLowerSegment.join cell1593856256 cell1593987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1594118400 cell1594249472)
                  (ThetaLowerSegment.join cell1594380544 cell1594511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1594642688 cell1594773760)
                  (ThetaLowerSegment.join cell1594904832 cell1595035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1595166976 cell1595298048)
                  (ThetaLowerSegment.join cell1595429120 cell1595560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1595691264 cell1595822336)
                  (ThetaLowerSegment.join cell1595953408 cell1596084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1596215552 cell1596346624)
                  (ThetaLowerSegment.join cell1596477696 cell1596608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1596739840 cell1596870912)
                  (ThetaLowerSegment.join cell1597001984 cell1597133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1597264128 cell1597395200)
                  (ThetaLowerSegment.join cell1597526272 cell1597657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1597788416 cell1597919488)
                  (ThetaLowerSegment.join cell1598050560 cell1598181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1598312704 cell1598443776)
                  (ThetaLowerSegment.join cell1598574848 cell1598705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1598836992 cell1598968064)
                  (ThetaLowerSegment.join cell1599099136 cell1599230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1599361280 cell1599492352)
                  (ThetaLowerSegment.join cell1599623424 cell1599754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1599885568 cell1600016640)
                  (ThetaLowerSegment.join cell1600147712 cell1600278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1600409856 cell1600540928)
                  (ThetaLowerSegment.join cell1600672000 cell1600803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1600934144 cell1601065216)
                  (ThetaLowerSegment.join cell1601196288 cell1601327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1601458432 cell1601589504)
                  (ThetaLowerSegment.join cell1601720576 cell1601851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1601982720 cell1602113792)
                  (ThetaLowerSegment.join cell1602244864 cell1602375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1602507008 cell1602638080)
                  (ThetaLowerSegment.join cell1602769152 cell1602900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1603031296 cell1603162368)
                  (ThetaLowerSegment.join cell1603293440 cell1603424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1603555584 cell1603686656)
                  (ThetaLowerSegment.join cell1603817728 cell1603948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1604079872 cell1604210944)
                  (ThetaLowerSegment.join cell1604342016 cell1604473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1604604160 cell1604735232)
                  (ThetaLowerSegment.join cell1604866304 cell1604997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1605128448 cell1605259520)
                  (ThetaLowerSegment.join cell1605390592 cell1605521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1605652736 cell1605783808)
                  (ThetaLowerSegment.join cell1605914880 cell1606045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1606177024 cell1606308096)
                  (ThetaLowerSegment.join cell1606439168 cell1606570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1606701312 cell1606832384)
                  (ThetaLowerSegment.join cell1606963456 cell1607094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1607225600 cell1607356672)
                  (ThetaLowerSegment.join cell1607487744 cell1607618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1607749888 cell1607880960)
                  (ThetaLowerSegment.join cell1608012032 cell1608143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1608274176 cell1608405248)
                  (ThetaLowerSegment.join cell1608536320 cell1608667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1608798464 cell1608929536)
                (ThetaLowerSegment.join cell1609060608 cell1609191680))
              (ThetaLowerSegment.join cell1609322752 cell1609339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
