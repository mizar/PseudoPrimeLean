/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1961341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1929341184 :
    ThetaLowerSegment 1929341184 1929472256 (96463508562947 / 50000)
      (192940189608817 / 100000) := by
  exact
    packedTile65536 1929341184 1929472256 14 6161 43924 31 _ _ (2138043 / 100000) (1069023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929472256 :
    ThetaLowerSegment 1929472256 1929603328 (192940189608817 / 100000)
      (192953394205617 / 100000) := by
  exact
    packedTile65536 1929472256 1929603328 14 6176 43925 31 _ _ (42761 / 2000) (2138053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929603328 :
    ThetaLowerSegment 1929603328 1929734400 (192953394205617 / 100000)
      (38593310361679 / 20000) := by
  exact
    packedTile65536 1929603328 1929734400 14 6154 43927 31 _ _ (2138057 / 100000) (106903 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929734400 :
    ThetaLowerSegment 1929734400 1929865472 (38593310361679 / 20000) (6030614918036 / 3125) := by
  exact
    packedTile65536 1929734400 1929865472 14 6139 43928 31 _ _ (2138063 / 100000) (1069033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929865472 :
    ThetaLowerSegment 1929865472 1929996544 (6030614918036 / 3125) (96496407908651 / 50000) := by
  exact
    packedTile65536 1929865472 1929996544 14 6145 43930 31 _ _ (213807 / 10000) (2138073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1929996544 :
    ThetaLowerSegment 1929996544 1930127616 (96496407908651 / 50000)
      (193005988509699 / 100000) := by
  exact
    packedTile65536 1929996544 1930127616 14 6161 43931 31 _ _ (2138077 / 100000) (13363 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930127616 :
    ThetaLowerSegment 1930127616 1930258688 (193005988509699 / 100000)
      (193019109931207 / 100000) := by
  exact
    packedTile65536 1930127616 1930258688 14 6137 43933 31 _ _ (534521 / 25000) (2138087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930258688 :
    ThetaLowerSegment 1930258688 1930389760 (193019109931207 / 100000)
      (193032143727847 / 100000) := by
  exact
    packedTile65536 1930258688 1930389760 14 6096 43934 31 _ _ (213809 / 10000) (2138093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930389760 :
    ThetaLowerSegment 1930389760 1930520832 (193032143727847 / 100000)
      (193045284472009 / 100000) := by
  exact
    packedTile65536 1930389760 1930520832 14 6146 43936 31 _ _ (2138097 / 100000) (21381 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930520832 :
    ThetaLowerSegment 1930520832 1930651904 (193045284472009 / 100000)
      (193058444502129 / 100000) := by
  exact
    packedTile65536 1930520832 1930651904 14 6155 43937 31 _ _ (267263 / 12500) (2138107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930651904 :
    ThetaLowerSegment 1930651904 1930782976 (193058444502129 / 100000)
      (193071645199443 / 100000) := by
  exact
    packedTile65536 1930651904 1930782976 14 6174 43939 31 _ _ (2138111 / 100000) (1069057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930782976 :
    ThetaLowerSegment 1930782976 1930914048 (193071645199443 / 100000)
      (193084794625143 / 100000) := by
  exact
    packedTile65536 1930782976 1930914048 14 6150 43940 31 _ _ (1069059 / 50000) (2138121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1930914048 :
    ThetaLowerSegment 1930914048 1931045120 (193084794625143 / 100000)
      (193097926982751 / 100000) := by
  exact
    packedTile65536 1930914048 1931045120 14 6142 43942 31 _ _ (534531 / 25000) (2138127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931045120 :
    ThetaLowerSegment 1931045120 1931176192 (193097926982751 / 100000)
      (48277735446537 / 25000) := by
  exact
    packedTile65536 1931045120 1931176192 14 6087 43943 31 _ _ (2138131 / 100000) (1069067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931176192 :
    ThetaLowerSegment 1931176192 1931307264 (48277735446537 / 25000) (96562014664423 / 50000) := by
  exact
    packedTile65536 1931176192 1931307264 14 6121 43945 31 _ _ (1069069 / 50000) (2138141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931307264 :
    ThetaLowerSegment 1931307264 1931438336 (96562014664423 / 50000)
      (193137189611321 / 100000) := by
  exact
    packedTile65536 1931307264 1931438336 14 6155 43946 31 _ _ (427629 / 20000) (534537 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931438336 :
    ThetaLowerSegment 1931438336 1931569408 (193137189611321 / 100000)
      (193150283654169 / 100000) := by
  exact
    packedTile65536 1931438336 1931569408 14 6124 43948 31 _ _ (267269 / 12500) (427631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931569408 :
    ThetaLowerSegment 1931569408 1931700480 (193150283654169 / 100000)
      (38632644757277 / 20000) := by
  exact
    packedTile65536 1931569408 1931700480 14 6052 43949 31 _ _ (1069079 / 50000) (2138161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931700480 :
    ThetaLowerSegment 1931700480 1931831552 (38632644757277 / 20000) (9658815360901 / 5000) := by
  exact
    packedTile65536 1931700480 1931831552 14 6119 43951 31 _ _ (427633 / 20000) (267271 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931831552 :
    ThetaLowerSegment 1931831552 1931962624 (9658815360901 / 5000) (482973722621 / 250) := by
  exact
    packedTile65536 1931831552 1931962624 14 6165 43952 31 _ _ (534543 / 25000) (85527 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931962624 :
    ThetaLowerSegment 1931962624 1932093696 (482973722621 / 250) (19320280990357 / 10000) := by
  exact
    packedTile65536 1931962624 1932093696 14 6230 43954 31 _ _ (2138179 / 100000) (1069091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932093696 :
    ThetaLowerSegment 1932093696 1932224768 (19320280990357 / 10000) (96607870826249 / 50000) := by
  exact
    packedTile65536 1932093696 1932224768 14 6048 43955 31 _ _ (1069093 / 50000) (2138189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932224768 :
    ThetaLowerSegment 1932224768 1932355840 (96607870826249 / 50000) (96614391242753 / 50000) := by
  exact
    packedTile65536 1932224768 1932355840 14 6099 43957 31 _ _ (133637 / 6250) (427639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932355840 :
    ThetaLowerSegment 1932355840 1932486912 (96614391242753 / 50000) (24155234067473 / 12500) := by
  exact
    packedTile65536 1932355840 1932486912 14 6122 43958 31 _ _ (2138199 / 100000) (1069101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932486912 :
    ThetaLowerSegment 1932486912 1932617984 (24155234067473 / 12500) (96627516598857 / 50000) := by
  exact
    packedTile65536 1932486912 1932617984 14 6155 43960 31 _ _ (1069103 / 50000) (2138209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932617984 :
    ThetaLowerSegment 1932617984 1932749056 (96627516598857 / 50000) (96634063807063 / 50000) := by
  exact
    packedTile65536 1932617984 1932749056 14 6124 43961 31 _ _ (2138213 / 100000) (267277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932749056 :
    ThetaLowerSegment 1932749056 1932880128 (96634063807063 / 50000) (48320330106339 / 25000) := by
  exact
    packedTile65536 1932749056 1932880128 14 6170 43963 31 _ _ (2138219 / 100000) (1069111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1932880128 :
    ThetaLowerSegment 1932880128 1933011200 (48320330106339 / 25000) (6040453539993 / 3125) := by
  exact
    packedTile65536 1932880128 1933011200 14 6170 43964 31 _ _ (1069113 / 50000) (2138229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933011200 :
    ThetaLowerSegment 1933011200 1933142272 (6040453539993 / 3125) (193307644168629 / 100000) := by
  exact
    packedTile65536 1933011200 1933142272 14 6141 43966 31 _ _ (2138233 / 100000) (534559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933142272 :
    ThetaLowerSegment 1933142272 1933273344 (193307644168629 / 100000)
      (193320841385909 / 100000) := by
  exact
    packedTile65536 1933142272 1933273344 14 6172 43967 31 _ _ (13364 / 625) (2138243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933273344 :
    ThetaLowerSegment 1933273344 1933404416 (193320841385909 / 100000) (1546672411807 / 800) := by
  exact
    packedTile65536 1933273344 1933404416 14 6178 43969 31 _ _ (2138247 / 100000) (8553 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933404416 :
    ThetaLowerSegment 1933404416 1933535488 (1546672411807 / 800) (193347013565561 / 100000) := by
  exact
    packedTile65536 1933404416 1933535488 14 6062 43970 31 _ _ (2138253 / 100000) (133641 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933535488 :
    ThetaLowerSegment 1933535488 1933666560 (193347013565561 / 100000)
      (193360198076721 / 100000) := by
  exact
    packedTile65536 1933535488 1933666560 14 6166 43971 31 _ _ (106913 / 5000) (2138263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933666560 :
    ThetaLowerSegment 1933666560 1933797632 (193360198076721 / 100000)
      (96686559812101 / 50000) := by
  exact
    packedTile65536 1933666560 1933797632 14 6043 43973 31 _ _ (2138267 / 100000) (213827 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933797632 :
    ThetaLowerSegment 1933797632 1933928704 (96686559812101 / 50000) (96693096515719 / 50000) := by
  exact
    packedTile65536 1933797632 1933928704 14 6114 43974 31 _ _ (1069137 / 50000) (2138277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1933928704 :
    ThetaLowerSegment 1933928704 1934059776 (96693096515719 / 50000) (96699683487259 / 50000) := by
  exact
    packedTile65536 1933928704 1934059776 14 6161 43976 31 _ _ (53457 / 2500) (2138283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934059776 :
    ThetaLowerSegment 1934059776 1934190848 (96699683487259 / 50000)
      (193412408386931 / 100000) := by
  exact
    packedTile65536 1934059776 1934190848 14 6099 43977 31 _ _ (2138287 / 100000) (213829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934190848 :
    ThetaLowerSegment 1934190848 1934321920 (193412408386931 / 100000)
      (193425665809731 / 100000) := by
  exact
    packedTile65536 1934190848 1934321920 14 6200 43979 31 _ _ (1069147 / 50000) (2138297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934321920 :
    ThetaLowerSegment 1934321920 1934452992 (193425665809731 / 100000)
      (193438641020199 / 100000) := by
  exact
    packedTile65536 1934321920 1934452992 14 6068 43980 31 _ _ (2138301 / 100000) (66822 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934452992 :
    ThetaLowerSegment 1934452992 1934584064 (193438641020199 / 100000)
      (38690359178203 / 20000) := by
  exact
    packedTile65536 1934452992 1934584064 14 6152 43982 31 _ _ (534577 / 25000) (2138311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934584064 :
    ThetaLowerSegment 1934584064 1934715136 (38690359178203 / 20000) (38692991442737 / 20000) := by
  exact
    packedTile65536 1934584064 1934715136 14 6155 43983 31 _ _ (1069157 / 50000) (2138317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934715136 :
    ThetaLowerSegment 1934715136 1934846208 (38692991442737 / 20000) (96738954511991 / 50000) := by
  exact
    packedTile65536 1934715136 1934846208 14 6057 43985 31 _ _ (2138321 / 100000) (534581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934846208 :
    ThetaLowerSegment 1934846208 1934977280 (96738954511991 / 50000) (96745554461363 / 50000) := by
  exact
    packedTile65536 1934846208 1934977280 14 6173 43986 31 _ _ (267291 / 12500) (2138331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1934977280 :
    ThetaLowerSegment 1934977280 1935108352 (96745554461363 / 50000) (96752226066563 / 50000) := by
  exact
    packedTile65536 1934977280 1935108352 14 6240 43988 31 _ _ (427667 / 20000) (1069169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935108352 :
    ThetaLowerSegment 1935108352 1935239424 (96752226066563 / 50000) (96758812156843 / 50000) := by
  exact
    packedTile65536 1935108352 1935239424 14 6160 43989 31 _ _ (2138341 / 100000) (267293 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935239424 :
    ThetaLowerSegment 1935239424 1935370496 (96758812156843 / 50000) (3870611996187 / 2000) := by
  exact
    packedTile65536 1935239424 1935370496 14 6068 43991 31 _ _ (534587 / 25000) (2138351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935370496 :
    ThetaLowerSegment 1935370496 1935501568 (3870611996187 / 2000) (38708747144823 / 20000) := by
  exact
    packedTile65536 1935370496 1935501568 14 6143 43992 31 _ _ (427671 / 20000) (1069179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935501568 :
    ThetaLowerSegment 1935501568 1935632640 (38708747144823 / 20000)
      (193556805392659 / 100000) := by
  exact
    packedTile65536 1935501568 1935632640 14 6112 43994 31 _ _ (1069181 / 50000) (427673 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935632640 :
    ThetaLowerSegment 1935632640 1935763712 (193556805392659 / 100000)
      (48392469310589 / 25000) := by
  exact
    packedTile65536 1935632640 1935763712 14 6113 43995 31 _ _ (2138369 / 100000) (534593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935763712 :
    ThetaLowerSegment 1935763712 1935894784 (48392469310589 / 25000) (96791492740553 / 50000) := by
  exact
    packedTile65536 1935763712 1935894784 14 6130 43997 31 _ _ (17107 / 800) (1069189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935894784 :
    ThetaLowerSegment 1935894784 1936025856 (96791492740553 / 50000) (96798055434911 / 50000) := by
  exact
    packedTile65536 1935894784 1936025856 14 6138 43998 31 _ _ (1069191 / 50000) (427677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936025856 :
    ThetaLowerSegment 1936025856 1936156928 (96798055434911 / 50000) (7744368511169 / 4000) := by
  exact
    packedTile65536 1936025856 1936156928 14 6127 44000 31 _ _ (2138389 / 100000) (267299 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936156928 :
    ThetaLowerSegment 1936156928 1936288000 (7744368511169 / 4000) (193622348945853 / 100000) := by
  exact
    packedTile65536 1936156928 1936288000 14 6143 44001 31 _ _ (534599 / 25000) (2138399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936288000 :
    ThetaLowerSegment 1936288000 1936419072 (193622348945853 / 100000)
      (193635487287741 / 100000) := by
  exact
    packedTile65536 1936288000 1936419072 14 6144 44003 31 _ _ (1069201 / 50000) (427681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936419072 :
    ThetaLowerSegment 1936419072 1936550144 (193635487287741 / 100000)
      (24206079010983 / 12500) := by
  exact
    packedTile65536 1936419072 1936550144 14 6147 44004 31 _ _ (2138409 / 100000) (534603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936550144 :
    ThetaLowerSegment 1936550144 1936681216 (24206079010983 / 12500) (24207722116377 / 12500) := by
  exact
    packedTile65536 1936550144 1936681216 14 6147 44006 31 _ _ (133651 / 6250) (2138419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936681216 :
    ThetaLowerSegment 1936681216 1936812288 (24207722116377 / 12500) (96837532545769 / 50000) := by
  exact
    packedTile65536 1936681216 1936812288 14 6214 44007 31 _ _ (2138423 / 100000) (1069213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936812288 :
    ThetaLowerSegment 1936812288 1936943360 (96837532545769 / 50000)
      (193688026109707 / 100000) := by
  exact
    packedTile65536 1936812288 1936943360 14 6061 44009 31 _ _ (2138429 / 100000) (66826 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1936943360 :
    ThetaLowerSegment 1936943360 1937074432 (193688026109707 / 100000)
      (193701181767979 / 100000) := by
  exact
    packedTile65536 1936943360 1937074432 14 6152 44010 31 _ _ (534609 / 25000) (2138439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937074432 :
    ThetaLowerSegment 1937074432 1937205504 (193701181767979 / 100000)
      (38742824725003 / 20000) := by
  exact
    packedTile65536 1937074432 1937205504 14 6052 44012 31 _ _ (2138443 / 100000) (1069223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937205504 :
    ThetaLowerSegment 1937205504 1937336576 (38742824725003 / 20000) (38745449886223 / 20000) := by
  exact
    packedTile65536 1937205504 1937336576 14 6138 44013 31 _ _ (42769 / 2000) (2138453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937336576 :
    ThetaLowerSegment 1937336576 1937467648 (38745449886223 / 20000)
      (193740343197203 / 100000) := by
  exact
    packedTile65536 1937336576 1937467648 14 6123 44015 31 _ _ (267307 / 12500) (2138459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937467648 :
    ThetaLowerSegment 1937467648 1937598720 (193740343197203 / 100000)
      (193753298006057 / 100000) := by
  exact
    packedTile65536 1937467648 1937598720 14 6058 44016 31 _ _ (2138463 / 100000) (1069233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937598720 :
    ThetaLowerSegment 1937598720 1937729792 (193753298006057 / 100000)
      (193766289211307 / 100000) := by
  exact
    packedTile65536 1937598720 1937729792 14 6075 44018 31 _ _ (213847 / 10000) (2138473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937729792 :
    ThetaLowerSegment 1937729792 1937860864 (193766289211307 / 100000)
      (193779389521409 / 100000) := by
  exact
    packedTile65536 1937729792 1937860864 14 6126 44019 31 _ _ (2138477 / 100000) (26731 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937860864 :
    ThetaLowerSegment 1937860864 1937991936 (193779389521409 / 100000)
      (193792509120749 / 100000) := by
  exact
    packedTile65536 1937860864 1937991936 14 6135 44021 31 _ _ (534621 / 25000) (2138487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1937991936 :
    ThetaLowerSegment 1937991936 1938123008 (193792509120749 / 100000)
      (193805585987099 / 100000) := by
  exact
    packedTile65536 1937991936 1938123008 14 6115 44022 31 _ _ (213849 / 10000) (2138493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938123008 :
    ThetaLowerSegment 1938123008 1938254080 (193805585987099 / 100000)
      (193818699250703 / 100000) := by
  exact
    packedTile65536 1938123008 1938254080 14 6132 44024 31 _ _ (2138497 / 100000) (4277 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938254080 :
    ThetaLowerSegment 1938254080 1938385152 (193818699250703 / 100000)
      (193831699216519 / 100000) := by
  exact
    packedTile65536 1938254080 1938385152 14 6079 44025 31 _ _ (267313 / 12500) (2138507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938385152 :
    ThetaLowerSegment 1938385152 1938516224 (193831699216519 / 100000)
      (193844846782147 / 100000) := by
  exact
    packedTile65536 1938385152 1938516224 14 6148 44027 31 _ _ (2138511 / 100000) (1069257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938516224 :
    ThetaLowerSegment 1938516224 1938647296 (193844846782147 / 100000)
      (193857925952119 / 100000) := by
  exact
    packedTile65536 1938516224 1938647296 14 6116 44028 31 _ _ (2138517 / 100000) (53463 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938647296 :
    ThetaLowerSegment 1938647296 1938778368 (193857925952119 / 100000)
      (38774195900523 / 20000) := by
  exact
    packedTile65536 1938647296 1938778368 14 6104 44030 31 _ _ (534631 / 25000) (2138527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938778368 :
    ThetaLowerSegment 1938778368 1938909440 (38774195900523 / 20000) (96942098881363 / 50000) := by
  exact
    packedTile65536 1938778368 1938909440 14 6181 44031 31 _ _ (2138531 / 100000) (1069267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1938909440 :
    ThetaLowerSegment 1938909440 1939040512 (96942098881363 / 50000) (12118575138269 / 6250) := by
  exact
    packedTile65536 1938909440 1939040512 14 6081 44033 31 _ _ (1069269 / 50000) (2138541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939040512 :
    ThetaLowerSegment 1939040512 1939171584 (12118575138269 / 6250) (1211939433428 / 625) := by
  exact
    packedTile65536 1939040512 1939171584 14 6129 44034 31 _ _ (133659 / 6250) (2138547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939171584 :
    ThetaLowerSegment 1939171584 1939302656 (1211939433428 / 625) (12120200568007 / 6250) := by
  exact
    packedTile65536 1939171584 1939302656 14 6032 44036 31 _ _ (2138551 / 100000) (1069277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939302656 :
    ThetaLowerSegment 1939302656 1939433728 (12120200568007 / 6250) (96968228727461 / 50000) := by
  exact
    packedTile65536 1939302656 1939433728 14 6195 44037 31 _ _ (1069279 / 50000) (2138561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939433728 :
    ThetaLowerSegment 1939433728 1939564800 (96968228727461 / 50000)
      (193949573274067 / 100000) := by
  exact
    packedTile65536 1939433728 1939564800 14 6133 44039 31 _ _ (427713 / 20000) (267321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939564800 :
    ThetaLowerSegment 1939564800 1939695872 (193949573274067 / 100000)
      (48490679767501 / 25000) := by
  exact
    packedTile65536 1939564800 1939695872 14 6147 44040 31 _ _ (2138571 / 100000) (1069287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939695872 :
    ThetaLowerSegment 1939695872 1939826944 (48490679767501 / 25000) (96987898237237 / 50000) := by
  exact
    packedTile65536 1939695872 1939826944 14 6115 44041 31 _ _ (1069289 / 50000) (2138581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939826944 :
    ThetaLowerSegment 1939826944 1939958016 (96987898237237 / 50000) (48497200837111 / 25000) := by
  exact
    packedTile65536 1939826944 1939958016 14 6082 44043 31 _ _ (427717 / 20000) (534647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939958016 :
    ThetaLowerSegment 1939958016 1940089088 (48497200837111 / 25000) (48500468605687 / 25000) := by
  exact
    packedTile65536 1939958016 1940089088 14 6112 44044 31 _ _ (66831 / 3125) (427719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940089088 :
    ThetaLowerSegment 1940089088 1940220160 (48500468605687 / 25000) (12125946660121 / 6250) := by
  exact
    packedTile65536 1940089088 1940220160 14 6206 44046 31 _ _ (1069299 / 50000) (2138601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940220160 :
    ThetaLowerSegment 1940220160 1940351232 (12125946660121 / 6250) (48507018072639 / 25000) := by
  exact
    packedTile65536 1940220160 1940351232 14 6044 44047 31 _ _ (427721 / 20000) (133663 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940351232 :
    ThetaLowerSegment 1940351232 1940482304 (48507018072639 / 25000) (24255139460643 / 12500) := by
  exact
    packedTile65536 1940351232 1940482304 14 6099 44049 31 _ _ (534653 / 25000) (427723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940482304 :
    ThetaLowerSegment 1940482304 1940613376 (24255139460643 / 12500)
      (194054381538801 / 100000) := by
  exact
    packedTile65536 1940482304 1940613376 14 6203 44050 31 _ _ (2138619 / 100000) (1069311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940613376 :
    ThetaLowerSegment 1940613376 1940744448 (194054381538801 / 100000)
      (97033868625963 / 50000) := by
  exact
    packedTile65536 1940613376 1940744448 14 6245 44052 31 _ _ (17109 / 800) (534657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940744448 :
    ThetaLowerSegment 1940744448 1940875520 (97033868625963 / 50000) (97040374344507 / 50000) := by
  exact
    packedTile65536 1940744448 1940875520 14 6084 44053 31 _ _ (267329 / 12500) (427727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1940875520 :
    ThetaLowerSegment 1940875520 1941006592 (97040374344507 / 50000) (6065431208256 / 3125) := by
  exact
    packedTile65536 1940875520 1941006592 14 6102 44055 31 _ _ (2138639 / 100000) (1069321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941006592 :
    ThetaLowerSegment 1941006592 1941137664 (6065431208256 / 3125) (48526737834273 / 25000) := by
  exact
    packedTile65536 1941006592 1941137664 14 6150 44056 31 _ _ (1069323 / 50000) (2138649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941137664 :
    ThetaLowerSegment 1941137664 1941268736 (48526737834273 / 25000) (38823995574503 / 20000) := by
  exact
    packedTile65536 1941137664 1941268736 14 6091 44058 31 _ _ (2138653 / 100000) (66833 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941268736 :
    ThetaLowerSegment 1941268736 1941399808 (38823995574503 / 20000) (48533272497711 / 25000) := by
  exact
    packedTile65536 1941268736 1941399808 14 6131 44059 31 _ _ (2138659 / 100000) (1069331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941399808 :
    ThetaLowerSegment 1941399808 1941530880 (48533272497711 / 25000) (24268248268353 / 12500) := by
  exact
    packedTile65536 1941399808 1941530880 14 6030 44061 31 _ _ (1069333 / 50000) (2138669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941530880 :
    ThetaLowerSegment 1941530880 1941661952 (24268248268353 / 12500) (6067472157636 / 3125) := by
  exact
    packedTile65536 1941530880 1941661952 14 6136 44062 31 _ _ (2138673 / 100000) (534669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941661952 :
    ThetaLowerSegment 1941661952 1941793024 (6067472157636 / 3125) (6067880912851 / 3125) := by
  exact
    packedTile65536 1941661952 1941793024 14 6116 44064 31 _ _ (53467 / 2500) (2138683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941793024 :
    ThetaLowerSegment 1941793024 1941924096 (6067880912851 / 3125) (48546352642021 / 25000) := by
  exact
    packedTile65536 1941793024 1941924096 14 6182 44065 31 _ _ (1069343 / 50000) (2138689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1941924096 :
    ThetaLowerSegment 1941924096 1942055168 (48546352642021 / 25000) (97099234713771 / 50000) := by
  exact
    packedTile65536 1941924096 1942055168 14 6106 44067 31 _ _ (2138693 / 100000) (267337 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942055168 :
    ThetaLowerSegment 1942055168 1942186240 (97099234713771 / 50000) (97105871099871 / 50000) := by
  exact
    packedTile65536 1942055168 1942186240 14 6206 44068 31 _ _ (21387 / 1000) (2138703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942186240 :
    ThetaLowerSegment 1942186240 1942317312 (97105871099871 / 50000)
      (194224897386499 / 100000) := by
  exact
    packedTile65536 1942186240 1942317312 14 6151 44070 31 _ _ (2138707 / 100000) (213871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942317312 :
    ThetaLowerSegment 1942317312 1942448384 (194224897386499 / 100000)
      (194237892206687 / 100000) := by
  exact
    packedTile65536 1942317312 1942448384 14 6076 44071 31 _ _ (2138713 / 100000) (534679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942448384 :
    ThetaLowerSegment 1942448384 1942579456 (194237892206687 / 100000)
      (194250865682207 / 100000) := by
  exact
    packedTile65536 1942448384 1942579456 14 6066 44073 31 _ _ (13367 / 625) (2138723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942579456 :
    ThetaLowerSegment 1942579456 1942710528 (194250865682207 / 100000)
      (48565943224913 / 25000) := by
  exact
    packedTile65536 1942579456 1942710528 14 6035 44074 31 _ _ (2138727 / 100000) (213873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942710528 :
    ThetaLowerSegment 1942710528 1942841600 (48565943224913 / 25000) (97138378576883 / 50000) := by
  exact
    packedTile65536 1942710528 1942841600 14 6071 44076 31 _ _ (1069367 / 50000) (2138737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942841600 :
    ThetaLowerSegment 1942841600 1942972672 (97138378576883 / 50000) (97144950924903 / 50000) := by
  exact
    packedTile65536 1942841600 1942972672 14 6146 44077 31 _ _ (106937 / 5000) (2138743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1942972672 :
    ThetaLowerSegment 1942972672 1943103744 (97144950924903 / 50000) (38860635410487 / 20000) := by
  exact
    packedTile65536 1942972672 1943103744 14 6207 44079 31 _ _ (2138747 / 100000) (1711 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943103744 :
    ThetaLowerSegment 1943103744 1943234816 (38860635410487 / 20000)
      (194316366748353 / 100000) := by
  exact
    packedTile65536 1943103744 1943234816 14 6167 44080 31 _ _ (1069377 / 50000) (2138757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943234816 :
    ThetaLowerSegment 1943234816 1943365888 (194316366748353 / 100000)
      (194329517983593 / 100000) := by
  exact
    packedTile65536 1943234816 1943365888 14 6149 44082 31 _ _ (53469 / 2500) (2138763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943365888 :
    ThetaLowerSegment 1943365888 1943496960 (194329517983593 / 100000)
      (194342675678177 / 100000) := by
  exact
    packedTile65536 1943365888 1943496960 14 6152 44083 31 _ _ (2138767 / 100000) (213877 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943496960 :
    ThetaLowerSegment 1943496960 1943628032 (194342675678177 / 100000)
      (194355948909621 / 100000) := by
  exact
    packedTile65536 1943496960 1943628032 14 6206 44085 31 _ _ (1069387 / 50000) (2138777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943628032 :
    ThetaLowerSegment 1943628032 1943759104 (194355948909621 / 100000)
      (194368995473721 / 100000) := by
  exact
    packedTile65536 1943628032 1943759104 14 6100 44086 31 _ _ (2138781 / 100000) (66837 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943759104 :
    ThetaLowerSegment 1943759104 1943890176 (194368995473721 / 100000)
      (194381943690219 / 100000) := by
  exact
    packedTile65536 1943759104 1943890176 14 6054 44088 31 _ _ (2138787 / 100000) (213879 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943890176 :
    ThetaLowerSegment 1943890176 1944021248 (194381943690219 / 100000)
      (194395022415529 / 100000) := by
  exact
    packedTile65536 1943890176 1944021248 14 6115 44089 31 _ _ (1069397 / 50000) (2138797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944021248 :
    ThetaLowerSegment 1944021248 1944152320 (194395022415529 / 100000)
      (38881659162907 / 20000) := by
  exact
    packedTile65536 1944021248 1944152320 14 6206 44091 31 _ _ (2138801 / 100000) (534701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944152320 :
    ThetaLowerSegment 1944152320 1944283392 (38881659162907 / 20000)
      (194421398152343 / 100000) := by
  exact
    packedTile65536 1944152320 1944283392 14 6126 44092 31 _ _ (267351 / 12500) (2138811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944283392 :
    ThetaLowerSegment 1944283392 1944414464 (194421398152343 / 100000)
      (194434645966259 / 100000) := by
  exact
    packedTile65536 1944283392 1944414464 14 6194 44094 31 _ _ (1069407 / 50000) (2138817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944414464 :
    ThetaLowerSegment 1944414464 1944545536 (194434645966259 / 100000)
      (48611915173011 / 25000) := by
  exact
    packedTile65536 1944414464 1944545536 14 6085 44095 31 _ _ (2138821 / 100000) (267353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944545536 :
    ThetaLowerSegment 1944545536 1944676608 (48611915173011 / 25000) (48615173677469 / 25000) := by
  exact
    packedTile65536 1944545536 1944676608 14 6094 44097 31 _ _ (534707 / 25000) (2138831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944676608 :
    ThetaLowerSegment 1944676608 1944807680 (48615173677469 / 25000) (97236860107513 / 50000) := by
  exact
    packedTile65536 1944676608 1944807680 14 6090 44098 31 _ _ (427767 / 20000) (1069419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944807680 :
    ThetaLowerSegment 1944807680 1944938752 (97236860107513 / 50000)
      (194487008834159 / 100000) := by
  exact
    packedTile65536 1944807680 1944938752 14 6213 44099 31 _ _ (2138841 / 100000) (534711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1944938752 :
    ThetaLowerSegment 1944938752 1945069824 (194487008834159 / 100000)
      (194500085750831 / 100000) := by
  exact
    packedTile65536 1944938752 1945069824 14 6114 44101 31 _ _ (66839 / 3125) (2138851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945069824 :
    ThetaLowerSegment 1945069824 1945200896 (194500085750831 / 100000)
      (97256503286943 / 50000) := by
  exact
    packedTile65536 1945069824 1945200896 14 6041 44102 31 _ _ (427771 / 20000) (1069429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945200896 :
    ThetaLowerSegment 1945200896 1945331968 (97256503286943 / 50000) (97263118787109 / 50000) := by
  exact
    packedTile65536 1945200896 1945331968 14 6186 44104 31 _ _ (1069431 / 50000) (427773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945331968 :
    ThetaLowerSegment 1945331968 1945463040 (97263118787109 / 50000) (97269704361681 / 50000) := by
  exact
    packedTile65536 1945331968 1945463040 14 6158 44105 31 _ _ (534717 / 25000) (2138871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945463040 :
    ThetaLowerSegment 1945463040 1945594112 (97269704361681 / 50000)
      (194552475110737 / 100000) := by
  exact
    packedTile65536 1945463040 1945594112 14 6109 44107 31 _ _ (17111 / 800) (1069439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945594112 :
    ThetaLowerSegment 1945594112 1945725184 (194552475110737 / 100000)
      (194565507318763 / 100000) := by
  exact
    packedTile65536 1945594112 1945725184 14 6093 44108 31 _ _ (1069441 / 50000) (427777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945725184 :
    ThetaLowerSegment 1945725184 1945856256 (194565507318763 / 100000)
      (97289318979167 / 50000) := by
  exact
    packedTile65536 1945725184 1945856256 14 6139 44110 31 _ _ (2138889 / 100000) (534723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945856256 :
    ThetaLowerSegment 1945856256 1945987328 (97289318979167 / 50000) (97295752775327 / 50000) := by
  exact
    packedTile65536 1945856256 1945987328 14 6016 44111 31 _ _ (427779 / 20000) (1069449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1945987328 :
    ThetaLowerSegment 1945987328 1946118400 (97295752775327 / 50000) (97302417593959 / 50000) := by
  exact
    packedTile65536 1945987328 1946118400 14 6232 44113 31 _ _ (1069451 / 50000) (427781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946118400 :
    ThetaLowerSegment 1946118400 1946249472 (97302417593959 / 50000) (97308915599501 / 50000) := by
  exact
    packedTile65536 1946118400 1946249472 14 6076 44114 31 _ _ (2138909 / 100000) (66841 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946249472 :
    ThetaLowerSegment 1946249472 1946380544 (97308915599501 / 50000) (3892620908441 / 2000) := by
  exact
    packedTile65536 1946249472 1946380544 14 6178 44116 31 _ _ (534729 / 25000) (2138919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946380544 :
    ThetaLowerSegment 1946380544 1946511616 (3892620908441 / 2000) (19464428534923 / 10000) := by
  exact
    packedTile65536 1946380544 1946511616 14 6190 44117 31 _ _ (1069461 / 50000) (85557 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946511616 :
    ThetaLowerSegment 1946511616 1946642688 (19464428534923 / 10000) (38931472980013 / 20000) := by
  exact
    packedTile65536 1946511616 1946642688 14 6115 44119 31 _ _ (2138929 / 100000) (534733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946642688 :
    ThetaLowerSegment 1946642688 1946773760 (38931472980013 / 20000)
      (194670453049449 / 100000) := by
  exact
    packedTile65536 1946642688 1946773760 14 6119 44120 31 _ _ (267367 / 12500) (2138939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946773760 :
    ThetaLowerSegment 1946773760 1946904832 (194670453049449 / 100000)
      (194683558347083 / 100000) := by
  exact
    packedTile65536 1946773760 1946904832 14 6127 44122 31 _ _ (1069471 / 50000) (427789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1946904832 :
    ThetaLowerSegment 1946904832 1947035904 (194683558347083 / 100000)
      (97348323288007 / 50000) := by
  exact
    packedTile65536 1946904832 1947035904 14 6119 44123 31 _ _ (2138949 / 100000) (267369 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947035904 :
    ThetaLowerSegment 1947035904 1947166976 (97348323288007 / 50000) (97354963676909 / 50000) := by
  exact
    packedTile65536 1947035904 1947166976 14 6209 44125 31 _ _ (534739 / 25000) (2138959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947166976 :
    ThetaLowerSegment 1947166976 1947298048 (97354963676909 / 50000) (38944641635017 / 20000) := by
  exact
    packedTile65536 1947166976 1947298048 14 6209 44126 31 _ _ (2138963 / 100000) (1069483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947298048 :
    ThetaLowerSegment 1947298048 1947429120 (38944641635017 / 20000) (19473630936021 / 10000) := by
  exact
    packedTile65536 1947298048 1947429120 14 6125 44128 31 _ _ (2138969 / 100000) (534743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947429120 :
    ThetaLowerSegment 1947429120 1947560192 (19473630936021 / 10000) (97374693529737 / 50000) := by
  exact
    packedTile65536 1947429120 1947560192 14 6114 44129 31 _ _ (66843 / 3125) (2138979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947560192 :
    ThetaLowerSegment 1947560192 1947691264 (97374693529737 / 50000) (973812409567 / 500) := by
  exact
    packedTile65536 1947560192 1947691264 14 6122 44131 31 _ _ (2138983 / 100000) (1069493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947691264 :
    ThetaLowerSegment 1947691264 1947822336 (973812409567 / 500) (19477568589867 / 10000) := by
  exact
    packedTile65536 1947691264 1947822336 14 6173 44132 31 _ _ (213899 / 10000) (2138993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947822336 :
    ThetaLowerSegment 1947822336 1947953408 (19477568589867 / 10000) (97394359400649 / 50000) := by
  exact
    packedTile65536 1947822336 1947953408 14 6093 44134 31 _ _ (534749 / 25000) (2138999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947953408 :
    ThetaLowerSegment 1947953408 1948084480 (97394359400649 / 50000) (24350233139217 / 12500) := by
  exact
    packedTile65536 1947953408 1948084480 14 6146 44135 31 _ _ (2139003 / 100000) (1069503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948084480 :
    ThetaLowerSegment 1948084480 1948215552 (24350233139217 / 12500) (97407427660733 / 50000) := by
  exact
    packedTile65536 1948084480 1948215552 14 6073 44137 31 _ _ (213901 / 10000) (2139013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948215552 :
    ThetaLowerSegment 1948215552 1948346624 (97407427660733 / 50000) (97413951659533 / 50000) := by
  exact
    packedTile65536 1948215552 1948346624 14 6100 44138 31 _ _ (267377 / 12500) (2139019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948346624 :
    ThetaLowerSegment 1948346624 1948477696 (97413951659533 / 50000) (24355156887579 / 12500) := by
  exact
    packedTile65536 1948346624 1948477696 14 6242 44140 31 _ _ (2139023 / 100000) (1069513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948477696 :
    ThetaLowerSegment 1948477696 1948608768 (24355156887579 / 12500) (97427126992971 / 50000) := by
  exact
    packedTile65536 1948477696 1948608768 14 6077 44141 31 _ _ (213903 / 10000) (2139033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948608768 :
    ThetaLowerSegment 1948608768 1948739840 (97427126992971 / 50000) (12179203975561 / 6250) := by
  exact
    packedTile65536 1948608768 1948739840 14 6082 44143 31 _ _ (2139037 / 100000) (13369 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948739840 :
    ThetaLowerSegment 1948739840 1948870912 (12179203975561 / 6250) (6090005197386 / 3125) := by
  exact
    packedTile65536 1948739840 1948870912 14 6032 44144 31 _ _ (2139043 / 100000) (1069523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1948870912 :
    ThetaLowerSegment 1948870912 1949001984 (6090005197386 / 3125) (48723287587463 / 25000) := by
  exact
    packedTile65536 1948870912 1949001984 14 6070 44146 31 _ _ (42781 / 2000) (2139053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949001984 :
    ThetaLowerSegment 1949001984 1949133056 (48723287587463 / 25000) (97453152775201 / 50000) := by
  exact
    packedTile65536 1949001984 1949133056 14 6150 44147 31 _ _ (2139057 / 100000) (106953 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949133056 :
    ThetaLowerSegment 1949133056 1949264128 (97453152775201 / 50000) (97459722910277 / 50000) := by
  exact
    packedTile65536 1949133056 1949264128 14 6143 44148 31 _ _ (267383 / 12500) (2139067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949264128 :
    ThetaLowerSegment 1949264128 1949395200 (97459722910277 / 50000) (97466336914717 / 50000) := by
  exact
    packedTile65536 1949264128 1949395200 14 6184 44150 31 _ _ (213907 / 10000) (2139073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949395200 :
    ThetaLowerSegment 1949395200 1949526272 (97466336914717 / 50000) (24368228644123 / 12500) := by
  exact
    packedTile65536 1949395200 1949526272 14 6150 44151 31 _ _ (2139077 / 100000) (53477 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949526272 :
    ThetaLowerSegment 1949526272 1949657344 (24368228644123 / 12500) (24369868252009 / 12500) := by
  exact
    packedTile65536 1949526272 1949657344 14 6132 44153 31 _ _ (534771 / 25000) (2139087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949657344 :
    ThetaLowerSegment 1949657344 1949788416 (24369868252009 / 12500) (97486111673851 / 50000) := by
  exact
    packedTile65536 1949657344 1949788416 14 6207 44154 31 _ _ (213909 / 10000) (2139093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949788416 :
    ThetaLowerSegment 1949788416 1949919488 (97486111673851 / 50000)
      (194985209805589 / 100000) := by
  exact
    packedTile65536 1949788416 1949919488 14 6071 44156 31 _ _ (2139097 / 100000) (21391 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1949919488 :
    ThetaLowerSegment 1949919488 1950050560 (194985209805589 / 100000)
      (194998239088053 / 100000) := by
  exact
    packedTile65536 1949919488 1950050560 14 6091 44157 31 _ _ (66847 / 3125) (2139107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950050560 :
    ThetaLowerSegment 1950050560 1950181632 (194998239088053 / 100000)
      (97505732605683 / 50000) := by
  exact
    packedTile65536 1950050560 1950181632 14 6183 44159 31 _ _ (2139111 / 100000) (1069557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950181632 :
    ThetaLowerSegment 1950181632 1950312704 (97505732605683 / 50000) (19502466784149 / 10000) := by
  exact
    packedTile65536 1950181632 1950312704 14 6172 44160 31 _ _ (2139117 / 100000) (26739 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950312704 :
    ThetaLowerSegment 1950312704 1950443776 (19502466784149 / 10000) (19503773788913 / 10000) := by
  exact
    packedTile65536 1950312704 1950443776 14 6110 44162 31 _ _ (534781 / 25000) (2139127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950443776 :
    ThetaLowerSegment 1950443776 1950574848 (19503773788913 / 10000) (19505095771871 / 10000) := by
  exact
    packedTile65536 1950443776 1950574848 14 6180 44163 31 _ _ (2139131 / 100000) (1069567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950574848 :
    ThetaLowerSegment 1950574848 1950705920 (19505095771871 / 10000)
      (195064192559329 / 100000) := by
  exact
    packedTile65536 1950574848 1950705920 14 6187 44165 31 _ _ (2139137 / 100000) (106957 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950705920 :
    ThetaLowerSegment 1950705920 1950836992 (195064192559329 / 100000)
      (195077391077809 / 100000) := by
  exact
    packedTile65536 1950705920 1950836992 14 6170 44166 31 _ _ (267393 / 12500) (2139147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950836992 :
    ThetaLowerSegment 1950836992 1950968064 (195077391077809 / 100000) (1950905276041 / 1000) := by
  exact
    packedTile65536 1950836992 1950968064 14 6141 44168 31 _ _ (2139151 / 100000) (1069577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1950968064 :
    ThetaLowerSegment 1950968064 1951099136 (1950905276041 / 1000) (97551887704797 / 50000) := by
  exact
    packedTile65536 1950968064 1951099136 14 6193 44169 31 _ _ (1069579 / 50000) (2139161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951099136 :
    ThetaLowerSegment 1951099136 1951230208 (97551887704797 / 50000) (97558390763357 / 50000) := by
  exact
    packedTile65536 1951099136 1951230208 14 6080 44171 31 _ _ (534791 / 25000) (2139167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951230208 :
    ThetaLowerSegment 1951230208 1951361280 (97558390763357 / 50000)
      (195129905340799 / 100000) := by
  exact
    packedTile65536 1951230208 1951361280 14 6135 44172 31 _ _ (2139171 / 100000) (1069587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951361280 :
    ThetaLowerSegment 1951361280 1951492352 (195129905340799 / 100000)
      (195142877316191 / 100000) := by
  exact
    packedTile65536 1951361280 1951492352 14 6064 44174 31 _ _ (1069589 / 50000) (2139181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951492352 :
    ThetaLowerSegment 1951492352 1951623424 (195142877316191 / 100000)
      (195155870725881 / 100000) := by
  exact
    packedTile65536 1951492352 1951623424 14 6074 44175 31 _ _ (427837 / 20000) (534797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951623424 :
    ThetaLowerSegment 1951623424 1951754496 (195155870725881 / 100000) (3903376641683 / 2000) := by
  exact
    packedTile65536 1951623424 1951754496 14 6059 44177 31 _ _ (2139191 / 100000) (1069597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951754496 :
    ThetaLowerSegment 1951754496 1951885568 (3903376641683 / 2000) (1219888562398 / 625) := by
  exact
    packedTile65536 1951754496 1951885568 14 6235 44178 31 _ _ (1069599 / 50000) (2139201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951885568 :
    ThetaLowerSegment 1951885568 1952016640 (1219888562398 / 625) (39039063935363 / 20000) := by
  exact
    packedTile65536 1951885568 1952016640 14 6147 44180 31 _ _ (427841 / 20000) (267401 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952016640 :
    ThetaLowerSegment 1952016640 1952147712 (39039063935363 / 20000) (97604224007361 / 50000) := by
  exact
    packedTile65536 1952016640 1952147712 14 6137 44181 31 _ _ (2139211 / 100000) (1069607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952147712 :
    ThetaLowerSegment 1952147712 1952278784 (97604224007361 / 50000) (3904431912971 / 2000) := by
  exact
    packedTile65536 1952147712 1952278784 14 6146 44183 31 _ _ (1069609 / 50000) (2139221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952278784 :
    ThetaLowerSegment 1952278784 1952409856 (3904431912971 / 2000) (488086644391 / 250) := by
  exact
    packedTile65536 1952278784 1952409856 14 6106 44184 31 _ _ (85569 / 4000) (534807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952409856 :
    ThetaLowerSegment 1952409856 1952540928 (488086644391 / 250) (12202989312989 / 6250) := by
  exact
    packedTile65536 1952409856 1952540928 14 6157 44186 31 _ _ (66851 / 3125) (427847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952540928 :
    ThetaLowerSegment 1952540928 1952672000 (12202989312989 / 6250) (24407644022761 / 12500) := by
  exact
    packedTile65536 1952540928 1952672000 14 6228 44187 31 _ _ (1069619 / 50000) (2139241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952672000 :
    ThetaLowerSegment 1952672000 1952803072 (24407644022761 / 12500)
      (195274229386773 / 100000) := by
  exact
    packedTile65536 1952672000 1952803072 14 6113 44189 31 _ _ (427849 / 20000) (133703 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952803072 :
    ThetaLowerSegment 1952803072 1952934144 (195274229386773 / 100000) (1562299531257 / 800) := by
  exact
    packedTile65536 1952803072 1952934144 14 6176 44190 31 _ _ (534813 / 25000) (427851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1952934144 :
    ThetaLowerSegment 1952934144 1953065216 (1562299531257 / 800) (195300488741667 / 100000) := by
  exact
    packedTile65536 1952934144 1953065216 14 6099 44192 31 _ _ (1069629 / 50000) (2139261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953065216 :
    ThetaLowerSegment 1953065216 1953196288 (195300488741667 / 100000)
      (195313632385827 / 100000) := by
  exact
    packedTile65536 1953065216 1953196288 14 6144 44193 31 _ _ (427853 / 20000) (534817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953196288 :
    ThetaLowerSegment 1953196288 1953327360 (195313632385827 / 100000) (7813068047939 / 4000) := by
  exact
    packedTile65536 1953196288 1953327360 14 6109 44194 31 _ _ (267409 / 12500) (85571 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953327360 :
    ThetaLowerSegment 1953327360 1953458432 (7813068047939 / 4000) (195339759357491 / 100000) := by
  exact
    packedTile65536 1953327360 1953458432 14 6104 44196 31 _ _ (2139279 / 100000) (1069641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953458432 :
    ThetaLowerSegment 1953458432 1953589504 (195339759357491 / 100000)
      (195352783324571 / 100000) := by
  exact
    packedTile65536 1953458432 1953589504 14 6088 44197 31 _ _ (427857 / 20000) (267411 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953589504 :
    ThetaLowerSegment 1953589504 1953720576 (195352783324571 / 100000)
      (195365877930903 / 100000) := by
  exact
    packedTile65536 1953589504 1953720576 14 6121 44199 31 _ _ (534823 / 25000) (427859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953720576 :
    ThetaLowerSegment 1953720576 1953851648 (195365877930903 / 100000) (6105594631308 / 3125) := by
  exact
    packedTile65536 1953720576 1953851648 14 6147 44200 31 _ _ (2139299 / 100000) (1069651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953851648 :
    ThetaLowerSegment 1953851648 1953982720 (6105594631308 / 3125) (48848015211979 / 25000) := by
  exact
    packedTile65536 1953851648 1953982720 14 6092 44202 31 _ _ (427861 / 20000) (534827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1953982720 :
    ThetaLowerSegment 1953982720 1954113792 (48848015211979 / 25000) (48851295312103 / 25000) := by
  exact
    packedTile65536 1953982720 1954113792 14 6133 44203 31 _ _ (133707 / 6250) (427863 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954113792 :
    ThetaLowerSegment 1954113792 1954244864 (48851295312103 / 25000) (12213642652373 / 6250) := by
  exact
    packedTile65536 1954113792 1954244864 14 6124 44205 31 _ _ (2139319 / 100000) (1069661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954244864 :
    ThetaLowerSegment 1954244864 1954375936 (12213642652373 / 6250) (48857880145267 / 25000) := by
  exact
    packedTile65536 1954244864 1954375936 14 6188 44206 31 _ _ (85573 / 4000) (66854 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954375936 :
    ThetaLowerSegment 1954375936 1954507008 (48857880145267 / 25000) (6107643964841 / 3125) := by
  exact
    packedTile65536 1954375936 1954507008 14 6117 44208 31 _ _ (534833 / 25000) (427867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954507008 :
    ThetaLowerSegment 1954507008 1954638080 (6107643964841 / 3125) (12216098739163 / 6250) := by
  exact
    packedTile65536 1954507008 1954638080 14 6064 44209 31 _ _ (2139339 / 100000) (1069671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954638080 :
    ThetaLowerSegment 1954638080 1954769152 (12216098739163 / 6250) (24433828729651 / 12500) := by
  exact
    packedTile65536 1954638080 1954769152 14 6100 44211 31 _ _ (1069673 / 50000) (2139349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954769152 :
    ThetaLowerSegment 1954769152 1954900224 (24433828729651 / 12500) (24435462124903 / 12500) := by
  exact
    packedTile65536 1954769152 1954900224 14 6108 44212 31 _ _ (267419 / 12500) (427871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1954900224 :
    ThetaLowerSegment 1954900224 1955031296 (24435462124903 / 12500)
      (195496933213357 / 100000) := by
  exact
    packedTile65536 1954900224 1955031296 14 6187 44214 31 _ _ (2139359 / 100000) (1069681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955031296 :
    ThetaLowerSegment 1955031296 1955162368 (195496933213357 / 100000)
      (39101976559151 / 20000) := by
  exact
    packedTile65536 1955031296 1955162368 14 6053 44215 31 _ _ (1069683 / 50000) (2139369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955162368 :
    ThetaLowerSegment 1955162368 1955293440 (39101976559151 / 20000)
      (195522960776791 / 100000) := by
  exact
    packedTile65536 1955162368 1955293440 14 6113 44217 31 _ _ (534843 / 25000) (3423 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955293440 :
    ThetaLowerSegment 1955293440 1955424512 (195522960776791 / 100000)
      (195536199254043 / 100000) := by
  exact
    packedTile65536 1955293440 1955424512 14 6188 44218 31 _ _ (2139379 / 100000) (1069691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955424512 :
    ThetaLowerSegment 1955424512 1955555584 (195536199254043 / 100000)
      (195549315829609 / 100000) := by
  exact
    packedTile65536 1955424512 1955555584 14 6131 44220 31 _ _ (1069693 / 50000) (2139389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955555584 :
    ThetaLowerSegment 1955555584 1955686656 (195549315829609 / 100000)
      (97781167018007 / 50000) := by
  exact
    packedTile65536 1955555584 1955686656 14 6085 44221 31 _ _ (2139393 / 100000) (534849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955686656 :
    ThetaLowerSegment 1955686656 1955817728 (97781167018007 / 50000) (9778774994873 / 5000) := by
  exact
    packedTile65536 1955686656 1955817728 14 6154 44223 31 _ _ (2139399 / 100000) (1069701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955817728 :
    ThetaLowerSegment 1955817728 1955948800 (9778774994873 / 5000) (97794250533861 / 50000) := by
  exact
    packedTile65536 1955817728 1955948800 14 6077 44224 31 _ _ (1069703 / 50000) (2139409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1955948800 :
    ThetaLowerSegment 1955948800 1956079872 (97794250533861 / 50000)
      (195601630645303 / 100000) := by
  exact
    packedTile65536 1955948800 1956079872 14 6137 44226 31 _ _ (2139413 / 100000) (267427 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956079872 :
    ThetaLowerSegment 1956079872 1956210944 (195601630645303 / 100000) (9780738654811 / 5000) := by
  exact
    packedTile65536 1956079872 1956210944 14 6143 44227 31 _ _ (2139419 / 100000) (1069711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956210944 :
    ThetaLowerSegment 1956210944 1956342016 (9780738654811 / 5000) (48907005105503 / 25000) := by
  exact
    packedTile65536 1956210944 1956342016 14 6192 44229 31 _ _ (1069713 / 50000) (2139429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956342016 :
    ThetaLowerSegment 1956342016 1956473088 (48907005105503 / 25000)
      (195641128728003 / 100000) := by
  exact
    packedTile65536 1956342016 1956473088 14 6127 44230 31 _ _ (2139433 / 100000) (534859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956473088 :
    ThetaLowerSegment 1956473088 1956604160 (195641128728003 / 100000)
      (39130847842039 / 20000) := by
  exact
    packedTile65536 1956473088 1956604160 14 6128 44232 31 _ _ (2139439 / 100000) (1069721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956604160 :
    ThetaLowerSegment 1956604160 1956735232 (39130847842039 / 20000)
      (195667441731461 / 100000) := by
  exact
    packedTile65536 1956604160 1956735232 14 6171 44233 31 _ _ (1069723 / 50000) (2139449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956735232 :
    ThetaLowerSegment 1956735232 1956866304 (195667441731461 / 100000)
      (195680428211171 / 100000) := by
  exact
    packedTile65536 1956735232 1956866304 14 6070 44235 31 _ _ (2139453 / 100000) (66858 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956866304 :
    ThetaLowerSegment 1956866304 1956997376 (195680428211171 / 100000)
      (195693508869611 / 100000) := by
  exact
    packedTile65536 1956866304 1956997376 14 6114 44236 31 _ _ (106973 / 5000) (2139463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956997376 :
    ThetaLowerSegment 1956997376 1957128448 (195693508869611 / 100000)
      (195706698677501 / 100000) := by
  exact
    packedTile65536 1956997376 1957128448 14 6165 44237 31 _ _ (1069733 / 50000) (2139469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957128448 :
    ThetaLowerSegment 1957128448 1957259520 (195706698677501 / 100000)
      (97859794501163 / 50000) := by
  exact
    packedTile65536 1957128448 1957259520 14 6025 44239 31 _ _ (2139473 / 100000) (534869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957259520 :
    ThetaLowerSegment 1957259520 1957390592 (97859794501163 / 50000) (97866294241403 / 50000) := by
  exact
    packedTile65536 1957259520 1957390592 14 6076 44240 31 _ _ (53487 / 2500) (2139483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957390592 :
    ThetaLowerSegment 1957390592 1957521664 (97866294241403 / 50000) (48936459579901 / 25000) := by
  exact
    packedTile65536 1957390592 1957521664 14 6193 44242 31 _ _ (1069743 / 50000) (2139489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957521664 :
    ThetaLowerSegment 1957521664 1957652736 (48936459579901 / 25000)
      (195758981225103 / 100000) := by
  exact
    packedTile65536 1957521664 1957652736 14 6143 44243 31 _ _ (2139493 / 100000) (267437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957652736 :
    ThetaLowerSegment 1957652736 1957783808 (195758981225103 / 100000)
      (195772034314603 / 100000) := by
  exact
    packedTile65536 1957652736 1957783808 14 6101 44245 31 _ _ (4279 / 200) (2139503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957783808 :
    ThetaLowerSegment 1957783808 1957914880 (195772034314603 / 100000)
      (195785198695021 / 100000) := by
  exact
    packedTile65536 1957783808 1957914880 14 6153 44246 31 _ _ (1069753 / 50000) (2139509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1957914880 :
    ThetaLowerSegment 1957914880 1958045952 (195785198695021 / 100000)
      (195798527861011 / 100000) := by
  exact
    packedTile65536 1957914880 1958045952 14 6230 44248 31 _ _ (2139513 / 100000) (534879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958045952 :
    ThetaLowerSegment 1958045952 1958177024 (195798527861011 / 100000)
      (195811405631891 / 100000) := by
  exact
    packedTile65536 1958045952 1958177024 14 6019 44249 31 _ _ (13372 / 625) (2139523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958177024 :
    ThetaLowerSegment 1958177024 1958308096 (195811405631891 / 100000)
      (195824662134987 / 100000) := by
  exact
    packedTile65536 1958177024 1958308096 14 6196 44251 31 _ _ (1069763 / 50000) (2139529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958308096 :
    ThetaLowerSegment 1958308096 1958439168 (195824662134987 / 100000) (6119925665199 / 3125) := by
  exact
    packedTile65536 1958308096 1958439168 14 6057 44252 31 _ _ (2139533 / 100000) (133721 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958439168 :
    ThetaLowerSegment 1958439168 1958570240 (6119925665199 / 3125) (24481337804241 / 12500) := by
  exact
    packedTile65536 1958439168 1958570240 14 6114 44254 31 _ _ (106977 / 5000) (2139543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958570240 :
    ThetaLowerSegment 1958570240 1958701312 (24481337804241 / 12500) (9793189395169 / 5000) := by
  exact
    packedTile65536 1958570240 1958701312 14 6116 44255 31 _ _ (2139547 / 100000) (42791 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958701312 :
    ThetaLowerSegment 1958701312 1958832384 (9793189395169 / 5000) (195876884107293 / 100000) := by
  exact
    packedTile65536 1958701312 1958832384 14 6121 44257 31 _ _ (2139553 / 100000) (534889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958832384 :
    ThetaLowerSegment 1958832384 1958963456 (195876884107293 / 100000)
      (195889911888133 / 100000) := by
  exact
    packedTile65536 1958832384 1958963456 14 6089 44258 31 _ _ (53489 / 2500) (2139563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1958963456 :
    ThetaLowerSegment 1958963456 1959094528 (195889911888133 / 100000)
      (195903219994873 / 100000) := by
  exact
    packedTile65536 1958963456 1959094528 14 6220 44260 31 _ _ (2139567 / 100000) (213957 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959094528 :
    ThetaLowerSegment 1959094528 1959225600 (195903219994873 / 100000)
      (195916356973093 / 100000) := by
  exact
    packedTile65536 1959094528 1959225600 14 6140 44261 31 _ _ (2139573 / 100000) (267447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959225600 :
    ThetaLowerSegment 1959225600 1959356672 (195916356973093 / 100000)
      (195929485435973 / 100000) := by
  exact
    packedTile65536 1959225600 1959356672 14 6136 44263 31 _ _ (106979 / 5000) (2139583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959356672 :
    ThetaLowerSegment 1959356672 1959487744 (195929485435973 / 100000)
      (195942943438203 / 100000) := by
  exact
    packedTile65536 1959356672 1959487744 14 6290 44264 31 _ _ (2139587 / 100000) (213959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959487744 :
    ThetaLowerSegment 1959487744 1959618816 (195942943438203 / 100000)
      (39191204981961 / 20000) := by
  exact
    packedTile65536 1959487744 1959618816 14 6114 44266 31 _ _ (2139593 / 100000) (534899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959618816 :
    ThetaLowerSegment 1959618816 1959749888 (39191204981961 / 20000) (39193805451801 / 20000) := by
  exact
    packedTile65536 1959618816 1959749888 14 6077 44267 31 _ _ (5349 / 250) (2139603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959749888 :
    ThetaLowerSegment 1959749888 1959880960 (39193805451801 / 20000) (489955116919 / 250) := by
  exact
    packedTile65536 1959749888 1959880960 14 6085 44269 31 _ _ (2139607 / 100000) (213961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1959880960 :
    ThetaLowerSegment 1959880960 1960012032 (489955116919 / 250) (195994860909857 / 100000) := by
  exact
    packedTile65536 1959880960 1960012032 14 5989 44270 31 _ _ (2139613 / 100000) (66863 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960012032 :
    ThetaLowerSegment 1960012032 1960143104 (195994860909857 / 100000)
      (196007927569197 / 100000) := by
  exact
    packedTile65536 1960012032 1960143104 14 6107 44272 31 _ _ (106981 / 5000) (2139623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960143104 :
    ThetaLowerSegment 1960143104 1960274176 (196007927569197 / 100000)
      (196020970735389 / 100000) := by
  exact
    packedTile65536 1960143104 1960274176 14 6096 44273 31 _ _ (2139627 / 100000) (213963 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960274176 :
    ThetaLowerSegment 1960274176 1960405248 (196020970735389 / 100000)
      (196034037480227 / 100000) := by
  exact
    packedTile65536 1960274176 1960405248 14 6107 44274 31 _ _ (1069817 / 50000) (2139637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960405248 :
    ThetaLowerSegment 1960405248 1960536320 (196034037480227 / 100000)
      (196047035793227 / 100000) := by
  exact
    packedTile65536 1960405248 1960536320 14 6075 44276 31 _ _ (53491 / 2500) (2139643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960536320 :
    ThetaLowerSegment 1960536320 1960667392 (196047035793227 / 100000) (6126879276619 / 3125) := by
  exact
    packedTile65536 1960536320 1960667392 14 6123 44277 31 _ _ (2139647 / 100000) (42793 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960667392 :
    ThetaLowerSegment 1960667392 1960798464 (6126879276619 / 3125) (12254574831239 / 6250) := by
  exact
    packedTile65536 1960667392 1960798464 14 6104 44279 31 _ _ (1069827 / 50000) (2139657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960798464 :
    ThetaLowerSegment 1960798464 1960929536 (12254574831239 / 6250) (49021608844061 / 25000) := by
  exact
    packedTile65536 1960798464 1960929536 14 6187 44280 31 _ _ (106983 / 5000) (2139663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960929536 :
    ThetaLowerSegment 1960929536 1961060608 (49021608844061 / 25000)
      (196099476646609 / 100000) := by
  exact
    packedTile65536 1960929536 1961060608 14 6095 44282 31 _ _ (2139667 / 100000) (213967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961060608 :
    ThetaLowerSegment 1961060608 1961191680 (196099476646609 / 100000)
      (196112436652027 / 100000) := by
  exact
    packedTile65536 1961060608 1961191680 14 6057 44283 31 _ _ (1069837 / 50000) (2139677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961191680 :
    ThetaLowerSegment 1961191680 1961322752 (196112436652027 / 100000)
      (196125768998107 / 100000) := by
  exact
    packedTile65536 1961191680 1961322752 14 6231 44285 31 _ _ (13373 / 625) (2139683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961322752 :
    ThetaLowerSegment 1961322752 1961339136 (196125768998107 / 100000)
      (196127420836471 / 100000) := by
  exact
    packedTile65536 1961322752 1961339136 11 772 44286 31 _ _ (2139687 / 100000) (213969 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961339136 :
    ThetaLowerSegment 1961339136 1961341184 (196127420836471 / 100000)
      (196127600570263 / 100000) := by
  exact
    packedTile65536 1961339136 1961341184 8 84 44287 31 _ _ (267461 / 12500) (2139691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1929341184_1961341184 :
    ThetaLowerSegment 1929341184 1961341184 (96463508562947 / 50000)
      (196127600570263 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1929341184 cell1929472256)
                  (ThetaLowerSegment.join cell1929603328 cell1929734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1929865472 cell1929996544)
                  (ThetaLowerSegment.join cell1930127616 cell1930258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1930389760 cell1930520832)
                  (ThetaLowerSegment.join cell1930651904 cell1930782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1930914048 cell1931045120)
                  (ThetaLowerSegment.join cell1931176192 cell1931307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1931438336 cell1931569408)
                  (ThetaLowerSegment.join cell1931700480 cell1931831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1931962624 cell1932093696)
                  (ThetaLowerSegment.join cell1932224768 cell1932355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1932486912 cell1932617984)
                  (ThetaLowerSegment.join cell1932749056 cell1932880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1933011200 cell1933142272)
                  (ThetaLowerSegment.join cell1933273344 cell1933404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1933535488 cell1933666560)
                  (ThetaLowerSegment.join cell1933797632 cell1933928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1934059776 cell1934190848)
                  (ThetaLowerSegment.join cell1934321920 cell1934452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1934584064 cell1934715136)
                  (ThetaLowerSegment.join cell1934846208 cell1934977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1935108352 cell1935239424)
                  (ThetaLowerSegment.join cell1935370496 cell1935501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1935632640 cell1935763712)
                  (ThetaLowerSegment.join cell1935894784 cell1936025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1936156928 cell1936288000)
                  (ThetaLowerSegment.join cell1936419072 cell1936550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1936681216 cell1936812288)
                  (ThetaLowerSegment.join cell1936943360 cell1937074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1937205504 cell1937336576)
                  (ThetaLowerSegment.join cell1937467648 cell1937598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1937729792 cell1937860864)
                  (ThetaLowerSegment.join cell1937991936 cell1938123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1938254080 cell1938385152)
                  (ThetaLowerSegment.join cell1938516224 cell1938647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1938778368 cell1938909440)
                  (ThetaLowerSegment.join cell1939040512 cell1939171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1939302656 cell1939433728)
                  (ThetaLowerSegment.join cell1939564800 cell1939695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1939826944 cell1939958016)
                  (ThetaLowerSegment.join cell1940089088 cell1940220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1940351232 cell1940482304)
                  (ThetaLowerSegment.join cell1940613376 cell1940744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1940875520 cell1941006592)
                  (ThetaLowerSegment.join cell1941137664 cell1941268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1941399808 cell1941530880)
                  (ThetaLowerSegment.join cell1941661952 cell1941793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1941924096 cell1942055168)
                  (ThetaLowerSegment.join cell1942186240 cell1942317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1942448384 cell1942579456)
                  (ThetaLowerSegment.join cell1942710528 cell1942841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1942972672 cell1943103744)
                  (ThetaLowerSegment.join cell1943234816 cell1943365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1943496960 cell1943628032)
                  (ThetaLowerSegment.join cell1943759104 cell1943890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1944021248 cell1944152320)
                  (ThetaLowerSegment.join cell1944283392 cell1944414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1944545536 cell1944676608)
                  (ThetaLowerSegment.join cell1944807680 cell1944938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1945069824 cell1945200896)
                  (ThetaLowerSegment.join cell1945331968 cell1945463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1945594112 cell1945725184)
                  (ThetaLowerSegment.join cell1945856256 cell1945987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1946118400 cell1946249472)
                  (ThetaLowerSegment.join cell1946380544 cell1946511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1946642688 cell1946773760)
                  (ThetaLowerSegment.join cell1946904832 cell1947035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1947166976 cell1947298048)
                  (ThetaLowerSegment.join cell1947429120 cell1947560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1947691264 cell1947822336)
                  (ThetaLowerSegment.join cell1947953408 cell1948084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1948215552 cell1948346624)
                  (ThetaLowerSegment.join cell1948477696 cell1948608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1948739840 cell1948870912)
                  (ThetaLowerSegment.join cell1949001984 cell1949133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1949264128 cell1949395200)
                  (ThetaLowerSegment.join cell1949526272 cell1949657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1949788416 cell1949919488)
                  (ThetaLowerSegment.join cell1950050560 cell1950181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1950312704 cell1950443776)
                  (ThetaLowerSegment.join cell1950574848 cell1950705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1950836992 cell1950968064)
                  (ThetaLowerSegment.join cell1951099136 cell1951230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1951361280 cell1951492352)
                  (ThetaLowerSegment.join cell1951623424 cell1951754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1951885568 cell1952016640)
                  (ThetaLowerSegment.join cell1952147712 cell1952278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1952409856 cell1952540928)
                  (ThetaLowerSegment.join cell1952672000 cell1952803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1952934144 cell1953065216)
                  (ThetaLowerSegment.join cell1953196288 cell1953327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1953458432 cell1953589504)
                  (ThetaLowerSegment.join cell1953720576 cell1953851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1953982720 cell1954113792)
                  (ThetaLowerSegment.join cell1954244864 cell1954375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1954507008 cell1954638080)
                  (ThetaLowerSegment.join cell1954769152 cell1954900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1955031296 cell1955162368)
                  (ThetaLowerSegment.join cell1955293440 cell1955424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1955555584 cell1955686656)
                  (ThetaLowerSegment.join cell1955817728 cell1955948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1956079872 cell1956210944)
                  (ThetaLowerSegment.join cell1956342016 cell1956473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1956604160 cell1956735232)
                  (ThetaLowerSegment.join cell1956866304 cell1956997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1957128448 cell1957259520)
                  (ThetaLowerSegment.join cell1957390592 cell1957521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1957652736 cell1957783808)
                  (ThetaLowerSegment.join cell1957914880 cell1958045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1958177024 cell1958308096)
                  (ThetaLowerSegment.join cell1958439168 cell1958570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1958701312 cell1958832384)
                  (ThetaLowerSegment.join cell1958963456 cell1959094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1959225600 cell1959356672)
                  (ThetaLowerSegment.join cell1959487744 cell1959618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1959749888 cell1959880960)
                  (ThetaLowerSegment.join cell1960012032 cell1960143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1960274176 cell1960405248)
                  (ThetaLowerSegment.join cell1960536320 cell1960667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1960798464 cell1960929536)
                (ThetaLowerSegment.join cell1961060608 cell1961191680))
              (ThetaLowerSegment.join cell1961322752 cell1961339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
