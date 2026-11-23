/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1737341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1705341184 :
    ThetaLowerSegment 1705341184 1705472256 (85264617382019 / 50000) (85271090144609 / 50000) := by
  exact
    packedTile65536 1705341184 1705472256 14 6090 41295 31 _ _ (1062851 / 50000) (425141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705472256 :
    ThetaLowerSegment 1705472256 1705603328 (85271090144609 / 50000) (17055529166233 / 10000) := by
  exact
    packedTile65536 1705472256 1705603328 14 6168 41297 31 _ _ (2125709 / 100000) (132857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705603328 :
    ThetaLowerSegment 1705603328 1705734400 (17055529166233 / 10000) (85284273816771 / 50000) := by
  exact
    packedTile65536 1705603328 1705734400 14 6236 41298 31 _ _ (2125717 / 100000) (53143 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705734400 :
    ThetaLowerSegment 1705734400 1705865472 (85284273816771 / 50000)
      (170581742008617 / 100000) := by
  exact
    packedTile65536 1705734400 1705865472 14 6207 41300 31 _ _ (85029 / 4000) (66429 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705865472 :
    ThetaLowerSegment 1705865472 1705996544 (170581742008617 / 100000)
      (170594851397861 / 100000) := by
  exact
    packedTile65536 1705865472 1705996544 14 6167 41302 31 _ _ (531433 / 25000) (425147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705996544 :
    ThetaLowerSegment 1705996544 1706127616 (170594851397861 / 100000)
      (170607831166301 / 100000) := by
  exact
    packedTile65536 1705996544 1706127616 14 6106 41303 31 _ _ (106287 / 5000) (2125743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706127616 :
    ThetaLowerSegment 1706127616 1706258688 (170607831166301 / 100000)
      (170621140474529 / 100000) := by
  exact
    packedTile65536 1706127616 1706258688 14 6261 41305 31 _ _ (531437 / 25000) (2125751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706258688 :
    ThetaLowerSegment 1706258688 1706389760 (170621140474529 / 100000)
      (170634213867779 / 100000) := by
  exact
    packedTile65536 1706258688 1706389760 14 6150 41306 31 _ _ (425151 / 20000) (1062879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706389760 :
    ThetaLowerSegment 1706389760 1706520832 (170634213867779 / 100000)
      (85323710616649 / 50000) := by
  exact
    packedTile65536 1706389760 1706520832 14 6213 41308 31 _ _ (2125763 / 100000) (1062883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706520832 :
    ThetaLowerSegment 1706520832 1706651904 (85323710616649 / 50000) (682642506091 / 400) := by
  exact
    packedTile65536 1706520832 1706651904 14 6212 41310 31 _ _ (2125771 / 100000) (1062887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706651904 :
    ThetaLowerSegment 1706651904 1706782976 (682642506091 / 400) (170673646913 / 100) := by
  exact
    packedTile65536 1706651904 1706782976 14 6125 41311 31 _ _ (1062889 / 50000) (2125781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706782976 :
    ThetaLowerSegment 1706782976 1706914048 (170673646913 / 100) (17068679489941 / 10000) := by
  exact
    packedTile65536 1706782976 1706914048 14 6185 41313 31 _ _ (1062893 / 50000) (2125789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1706914048 :
    ThetaLowerSegment 1706914048 1707045120 (17068679489941 / 10000) (21337478517803 / 12500) := by
  exact
    packedTile65536 1706914048 1707045120 14 6131 41314 31 _ _ (1062897 / 50000) (2125797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707045120 :
    ThetaLowerSegment 1707045120 1707176192 (21337478517803 / 12500) (42678266907763 / 25000) := by
  exact
    packedTile65536 1707045120 1707176192 14 6228 41316 31 _ _ (2125801 / 100000) (531451 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707176192 :
    ThetaLowerSegment 1707176192 1707307264 (42678266907763 / 25000) (42681532150387 / 25000) := by
  exact
    packedTile65536 1707176192 1707307264 14 6144 41317 31 _ _ (2125809 / 100000) (531453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707307264 :
    ThetaLowerSegment 1707307264 1707438336 (42681532150387 / 25000) (85369635201121 / 50000) := by
  exact
    packedTile65536 1707307264 1707438336 14 6182 41319 31 _ _ (2125817 / 100000) (106291 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707438336 :
    ThetaLowerSegment 1707438336 1707569408 (85369635201121 / 50000) (42688096685623 / 25000) := by
  exact
    packedTile65536 1707438336 1707569408 14 6170 41321 31 _ _ (85033 / 4000) (531457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707569408 :
    ThetaLowerSegment 1707569408 1707700480 (42688096685623 / 25000) (8538270798341 / 5000) := by
  exact
    packedTile65536 1707569408 1707700480 14 6129 41322 31 _ _ (265729 / 12500) (425167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707700480 :
    ThetaLowerSegment 1707700480 1707831552 (8538270798341 / 5000) (8538929383573 / 5000) := by
  exact
    packedTile65536 1707700480 1707831552 14 6196 41324 31 _ _ (26573 / 1250) (2125843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707831552 :
    ThetaLowerSegment 1707831552 1707962624 (8538929383573 / 5000) (42697931884487 / 25000) := by
  exact
    packedTile65536 1707831552 1707962624 14 6181 41325 31 _ _ (265731 / 12500) (2125851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1707962624 :
    ThetaLowerSegment 1707962624 1708093696 (42697931884487 / 25000) (85402405024809 / 50000) := by
  exact
    packedTile65536 1707962624 1708093696 14 6154 41327 31 _ _ (425171 / 20000) (1062929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708093696 :
    ThetaLowerSegment 1708093696 1708224768 (85402405024809 / 50000)
      (170817877729479 / 100000) := by
  exact
    packedTile65536 1708093696 1708224768 14 6147 41329 31 _ _ (2125863 / 100000) (1062933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708224768 :
    ThetaLowerSegment 1708224768 1708355840 (170817877729479 / 100000)
      (21353867119379 / 12500) := by
  exact
    packedTile65536 1708224768 1708355840 14 6143 41330 31 _ _ (2125871 / 100000) (1062937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708355840 :
    ThetaLowerSegment 1708355840 1708486912 (21353867119379 / 12500) (8542202255939 / 5000) := by
  exact
    packedTile65536 1708355840 1708486912 14 6166 41332 31 _ _ (1062939 / 50000) (2125881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708486912 :
    ThetaLowerSegment 1708486912 1708617984 (8542202255939 / 5000) (42714261759389 / 25000) := by
  exact
    packedTile65536 1708486912 1708617984 14 6116 41333 31 _ _ (1062943 / 50000) (2125889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708617984 :
    ThetaLowerSegment 1708617984 1708749056 (42714261759389 / 25000) (42717488866481 / 25000) := by
  exact
    packedTile65536 1708617984 1708749056 14 6072 41335 31 _ _ (1062947 / 50000) (2125897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708749056 :
    ThetaLowerSegment 1708749056 1708880128 (42717488866481 / 25000) (85441519130339 / 50000) := by
  exact
    packedTile65536 1708749056 1708880128 14 6154 41337 31 _ _ (2125901 / 100000) (132869 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708880128 :
    ThetaLowerSegment 1708880128 1709011200 (85441519130339 / 50000) (42724057912983 / 25000) := by
  exact
    packedTile65536 1708880128 1709011200 14 6206 41338 31 _ _ (2125909 / 100000) (265739 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709011200 :
    ThetaLowerSegment 1709011200 1709142272 (42724057912983 / 25000) (85454725301919 / 50000) := by
  exact
    packedTile65536 1709011200 1709142272 14 6218 41340 31 _ _ (2125917 / 100000) (13287 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709142272 :
    ThetaLowerSegment 1709142272 1709273344 (85454725301919 / 50000) (85461383695887 / 50000) := by
  exact
    packedTile65536 1709142272 1709273344 14 6264 41341 31 _ _ (531481 / 25000) (2125927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709273344 :
    ThetaLowerSegment 1709273344 1709404416 (85461383695887 / 50000) (85467960266529 / 50000) := by
  exact
    packedTile65536 1709273344 1709404416 14 6187 41343 31 _ _ (531483 / 25000) (425187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709404416 :
    ThetaLowerSegment 1709404416 1709535488 (85467960266529 / 50000) (85474542176769 / 50000) := by
  exact
    packedTile65536 1709404416 1709535488 14 6192 41344 31 _ _ (106297 / 5000) (2125943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709535488 :
    ThetaLowerSegment 1709535488 1709666560 (85474542176769 / 50000)
      (170962360892553 / 100000) := by
  exact
    packedTile65536 1709535488 1709666560 14 6245 41346 31 _ _ (2125947 / 100000) (42519 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709666560 :
    ThetaLowerSegment 1709666560 1709797632 (170962360892553 / 100000)
      (170975567325013 / 100000) := by
  exact
    packedTile65536 1709666560 1709797632 14 6212 41348 31 _ _ (425191 / 20000) (1062979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709797632 :
    ThetaLowerSegment 1709797632 1709928704 (170975567325013 / 100000) (3419774923393 / 2000) := by
  exact
    packedTile65536 1709797632 1709928704 14 6199 41349 31 _ _ (2125963 / 100000) (1062983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1709928704 :
    ThetaLowerSegment 1709928704 1710059776 (3419774923393 / 2000) (8550093489123 / 5000) := by
  exact
    packedTile65536 1709928704 1710059776 14 6173 41351 31 _ _ (212597 / 10000) (2125973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710059776 :
    ThetaLowerSegment 1710059776 1710190848 (8550093489123 / 5000) (42753724443911 / 25000) := by
  exact
    packedTile65536 1710059776 1710190848 14 6128 41352 31 _ _ (1062989 / 50000) (2125981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710190848 :
    ThetaLowerSegment 1710190848 1710321920 (42753724443911 / 25000) (85513968223891 / 50000) := by
  exact
    packedTile65536 1710190848 1710321920 14 6133 41354 31 _ _ (1062993 / 50000) (2125989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710321920 :
    ThetaLowerSegment 1710321920 1710452992 (85513968223891 / 50000) (42760248574197 / 25000) := by
  exact
    packedTile65536 1710321920 1710452992 14 6142 41356 31 _ _ (2125993 / 100000) (531499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710452992 :
    ThetaLowerSegment 1710452992 1710584064 (42760248574197 / 25000) (34210833824997 / 20000) := by
  exact
    packedTile65536 1710452992 1710584064 14 6197 41357 31 _ _ (2126001 / 100000) (531501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710584064 :
    ThetaLowerSegment 1710584064 1710715136 (34210833824997 / 20000)
      (171067337624731 / 100000) := by
  exact
    packedTile65536 1710584064 1710715136 14 6194 41359 31 _ _ (2126009 / 100000) (531503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710715136 :
    ThetaLowerSegment 1710715136 1710846208 (171067337624731 / 100000) (273728605771 / 160) := by
  exact
    packedTile65536 1710715136 1710846208 14 6134 41360 31 _ _ (66438 / 3125) (2126019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710846208 :
    ThetaLowerSegment 1710846208 1710977280 (273728605771 / 160) (171093323967011 / 100000) := by
  exact
    packedTile65536 1710846208 1710977280 14 6089 41362 31 _ _ (265753 / 12500) (2126027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1710977280 :
    ThetaLowerSegment 1710977280 1711108352 (171093323967011 / 100000)
      (34221295545399 / 20000) := by
  exact
    packedTile65536 1710977280 1711108352 14 6187 41363 31 _ _ (132877 / 6250) (425207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711108352 :
    ThetaLowerSegment 1711108352 1711239424 (34221295545399 / 20000)
      (171119799487369 / 100000) := by
  exact
    packedTile65536 1711108352 1711239424 14 6266 41365 31 _ _ (2126039 / 100000) (1063021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711239424 :
    ThetaLowerSegment 1711239424 1711370496 (171119799487369 / 100000)
      (42783222389687 / 25000) := by
  exact
    packedTile65536 1711239424 1711370496 14 6157 41367 31 _ _ (2126047 / 100000) (42521 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711370496 :
    ThetaLowerSegment 1711370496 1711501568 (42783222389687 / 25000) (42786475253837 / 25000) := by
  exact
    packedTile65536 1711370496 1711501568 14 6120 41368 31 _ _ (425211 / 20000) (1063029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711501568 :
    ThetaLowerSegment 1711501568 1711632640 (42786475253837 / 25000) (21394874163143 / 12500) := by
  exact
    packedTile65536 1711501568 1711632640 14 6158 41370 31 _ _ (1063031 / 50000) (425213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711632640 :
    ThetaLowerSegment 1711632640 1711763712 (21394874163143 / 12500) (85585999237667 / 50000) := by
  exact
    packedTile65536 1711632640 1711763712 14 6117 41371 31 _ _ (212607 / 10000) (2126073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711763712 :
    ThetaLowerSegment 1711763712 1711894784 (85585999237667 / 50000) (85592638979261 / 50000) := by
  exact
    packedTile65536 1711763712 1711894784 14 6246 41373 31 _ _ (1063039 / 50000) (2126081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1711894784 :
    ThetaLowerSegment 1711894784 1712025856 (85592638979261 / 50000)
      (171198364011697 / 100000) := by
  exact
    packedTile65536 1711894784 1712025856 14 6155 41375 31 _ _ (425217 / 20000) (265761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712025856 :
    ThetaLowerSegment 1712025856 1712156928 (171198364011697 / 100000)
      (21401416381613 / 12500) := by
  exact
    packedTile65536 1712025856 1712156928 14 6099 41376 31 _ _ (2126093 / 100000) (132881 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712156928 :
    ThetaLowerSegment 1712156928 1712288000 (21401416381613 / 12500) (42806084101651 / 25000) := by
  exact
    packedTile65536 1712156928 1712288000 14 6117 41378 31 _ _ (21261 / 1000) (2126103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712288000 :
    ThetaLowerSegment 1712288000 1712419072 (42806084101651 / 25000) (21404675167533 / 12500) := by
  exact
    packedTile65536 1712288000 1712419072 14 6145 41379 31 _ _ (531527 / 25000) (2126111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712419072 :
    ThetaLowerSegment 1712419072 1712550144 (21404675167533 / 12500) (42812648472511 / 25000) := by
  exact
    packedTile65536 1712419072 1712550144 14 6205 41381 31 _ _ (531529 / 25000) (2126119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712550144 :
    ThetaLowerSegment 1712550144 1712681216 (42812648472511 / 25000)
      (171263561114221 / 100000) := by
  exact
    packedTile65536 1712550144 1712681216 14 6099 41382 31 _ _ (2126123 / 100000) (1063063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712681216 :
    ThetaLowerSegment 1712681216 1712812288 (171263561114221 / 100000)
      (34255367335237 / 20000) := by
  exact
    packedTile65536 1712681216 1712812288 14 6244 41384 31 _ _ (2126131 / 100000) (1063067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712812288 :
    ThetaLowerSegment 1712812288 1712943360 (34255367335237 / 20000) (21411245166529 / 12500) := by
  exact
    packedTile65536 1712812288 1712943360 14 6173 41386 31 _ _ (2126139 / 100000) (1063071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712943360 :
    ThetaLowerSegment 1712943360 1713074432 (21411245166529 / 12500) (85651547268037 / 50000) := by
  exact
    packedTile65536 1712943360 1713074432 14 6177 41387 31 _ _ (1063073 / 50000) (2126149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713074432 :
    ThetaLowerSegment 1713074432 1713205504 (85651547268037 / 50000) (5353628796301 / 3125) := by
  exact
    packedTile65536 1713074432 1713205504 14 6127 41389 31 _ _ (1063077 / 50000) (2126157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713205504 :
    ThetaLowerSegment 1713205504 1713336576 (5353628796301 / 3125) (21416170402321 / 12500) := by
  exact
    packedTile65536 1713205504 1713336576 14 6228 41390 31 _ _ (1063081 / 50000) (425233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713336576 :
    ThetaLowerSegment 1713336576 1713467648 (21416170402321 / 12500)
      (171342351984989 / 100000) := by
  exact
    packedTile65536 1713336576 1713467648 14 6109 41392 31 _ _ (2126169 / 100000) (531543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713467648 :
    ThetaLowerSegment 1713467648 1713598720 (171342351984989 / 100000)
      (85677657643079 / 50000) := by
  exact
    packedTile65536 1713467648 1713598720 14 6097 41394 31 _ _ (2126177 / 100000) (106309 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713598720 :
    ThetaLowerSegment 1713598720 1713729792 (85677657643079 / 50000) (85684151012069 / 50000) := by
  exact
    packedTile65536 1713598720 1713729792 14 6108 41395 31 _ _ (425237 / 20000) (531547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713729792 :
    ThetaLowerSegment 1713729792 1713860864 (85684151012069 / 50000) (85690687989373 / 50000) := by
  exact
    packedTile65536 1713729792 1713860864 14 6149 41397 31 _ _ (132887 / 6250) (425239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713860864 :
    ThetaLowerSegment 1713860864 1713991936 (85690687989373 / 50000) (85697212234073 / 50000) := by
  exact
    packedTile65536 1713860864 1713991936 14 6137 41398 31 _ _ (10631 / 500) (2126203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1713991936 :
    ThetaLowerSegment 1713991936 1714123008 (85697212234073 / 50000) (85703831119577 / 50000) := by
  exact
    packedTile65536 1713991936 1714123008 14 6226 41400 31 _ _ (66444 / 3125) (2126211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714123008 :
    ThetaLowerSegment 1714123008 1714254080 (85703831119577 / 50000)
      (171420668296309 / 100000) := by
  exact
    packedTile65536 1714123008 1714254080 14 6117 41401 31 _ _ (425243 / 20000) (1063109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714254080 :
    ThetaLowerSegment 1714254080 1714385152 (171420668296309 / 100000)
      (171433787092219 / 100000) := by
  exact
    packedTile65536 1714254080 1714385152 14 6170 41403 31 _ _ (2126223 / 100000) (1063113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714385152 :
    ThetaLowerSegment 1714385152 1714516224 (171433787092219 / 100000)
      (21430850750579 / 12500) := by
  exact
    packedTile65536 1714385152 1714516224 14 6123 41405 31 _ _ (2126231 / 100000) (1063117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714516224 :
    ThetaLowerSegment 1714516224 1714647296 (21430850750579 / 12500) (8572993693169 / 5000) := by
  exact
    packedTile65536 1714516224 1714647296 14 6146 41406 31 _ _ (1063119 / 50000) (2126241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714647296 :
    ThetaLowerSegment 1714647296 1714778368 (8572993693169 / 5000) (85736484706247 / 50000) := by
  exact
    packedTile65536 1714647296 1714778368 14 6159 41408 31 _ _ (1063123 / 50000) (2126249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714778368 :
    ThetaLowerSegment 1714778368 1714909440 (85736484706247 / 50000) (42871553992171 / 25000) := by
  exact
    packedTile65536 1714778368 1714909440 14 6230 41409 31 _ _ (2126253 / 100000) (132891 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1714909440 :
    ThetaLowerSegment 1714909440 1715040512 (42871553992171 / 25000) (85749654741961 / 50000) := by
  exact
    packedTile65536 1714909440 1715040512 14 6158 41411 31 _ _ (2126261 / 100000) (265783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715040512 :
    ThetaLowerSegment 1715040512 1715171584 (85749654741961 / 50000) (34302505699659 / 20000) := by
  exact
    packedTile65536 1715040512 1715171584 14 6217 41413 31 _ _ (2126269 / 100000) (66446 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715171584 :
    ThetaLowerSegment 1715171584 1715302656 (34302505699659 / 20000)
      (171525592338039 / 100000) := by
  exact
    packedTile65536 1715171584 1715302656 14 6144 41414 31 _ _ (531569 / 25000) (2126279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715302656 :
    ThetaLowerSegment 1715302656 1715433728 (171525592338039 / 100000)
      (171538675363491 / 100000) := by
  exact
    packedTile65536 1715302656 1715433728 14 6153 41416 31 _ _ (531571 / 25000) (2126287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715433728 :
    ThetaLowerSegment 1715433728 1715564800 (171538675363491 / 100000)
      (171551790332547 / 100000) := by
  exact
    packedTile65536 1715433728 1715564800 14 6168 41417 31 _ _ (531573 / 25000) (425259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715564800 :
    ThetaLowerSegment 1715564800 1715695872 (171551790332547 / 100000)
      (17156483942951 / 10000) := by
  exact
    packedTile65536 1715564800 1715695872 14 6137 41419 31 _ _ (2126299 / 100000) (1063151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715695872 :
    ThetaLowerSegment 1715695872 1715826944 (17156483942951 / 10000) (1372624095211 / 800) := by
  exact
    packedTile65536 1715695872 1715826944 14 6195 41420 31 _ _ (2126307 / 100000) (212631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715826944 :
    ThetaLowerSegment 1715826944 1715958016 (1372624095211 / 800) (343182283793 / 200) := by
  exact
    packedTile65536 1715826944 1715958016 14 6175 41422 31 _ _ (425263 / 20000) (1063159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1715958016 :
    ThetaLowerSegment 1715958016 1716089088 (343182283793 / 200) (5362633963097 / 3125) := by
  exact
    packedTile65536 1715958016 1716089088 14 6182 41424 31 _ _ (1063161 / 50000) (85053 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716089088 :
    ThetaLowerSegment 1716089088 1716220160 (5362633963097 / 3125) (21452191200293 / 12500) := by
  exact
    packedTile65536 1716089088 1716220160 14 6228 41425 31 _ _ (212633 / 10000) (2126333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716220160 :
    ThetaLowerSegment 1716220160 1716351232 (21452191200293 / 12500) (3432613705111 / 2000) := by
  exact
    packedTile65536 1716220160 1716351232 14 6187 41427 31 _ _ (1063169 / 50000) (2126341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716351232 :
    ThetaLowerSegment 1716351232 1716482304 (3432613705111 / 2000) (1716440174387 / 1000) := by
  exact
    packedTile65536 1716351232 1716482304 14 6270 41428 31 _ _ (425269 / 20000) (531587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716482304 :
    ThetaLowerSegment 1716482304 1716613376 (1716440174387 / 1000) (34331433786401 / 20000) := by
  exact
    packedTile65536 1716482304 1716613376 14 6185 41430 31 _ _ (2126353 / 100000) (531589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716613376 :
    ThetaLowerSegment 1716613376 1716744448 (34331433786401 / 20000) (34334058990457 / 20000) := by
  exact
    packedTile65536 1716613376 1716744448 14 6173 41432 31 _ _ (53159 / 2500) (2126363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716744448 :
    ThetaLowerSegment 1716744448 1716875520 (34334058990457 / 20000)
      (171683355104541 / 100000) := by
  exact
    packedTile65536 1716744448 1716875520 14 6142 41433 31 _ _ (66449 / 3125) (2126371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716875520 :
    ThetaLowerSegment 1716875520 1717006592 (171683355104541 / 100000)
      (171696457833453 / 100000) := by
  exact
    packedTile65536 1716875520 1717006592 14 6162 41435 31 _ _ (265797 / 12500) (2126379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717006592 :
    ThetaLowerSegment 1717006592 1717137664 (171696457833453 / 100000)
      (171709462791881 / 100000) := by
  exact
    packedTile65536 1717006592 1717137664 14 6116 41436 31 _ _ (2126383 / 100000) (1063193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717137664 :
    ThetaLowerSegment 1717137664 1717268736 (171709462791881 / 100000) (4293064512449 / 2500) := by
  exact
    packedTile65536 1717137664 1717268736 14 6169 41438 31 _ _ (2126391 / 100000) (1063197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717268736 :
    ThetaLowerSegment 1717268736 1717399808 (4293064512449 / 2500) (42933947422137 / 25000) := by
  exact
    packedTile65536 1717268736 1717399808 14 6212 41439 31 _ _ (2126399 / 100000) (1063201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717399808 :
    ThetaLowerSegment 1717399808 1717530880 (42933947422137 / 25000) (42937232719407 / 25000) := by
  exact
    packedTile65536 1717399808 1717530880 14 6180 41441 31 _ _ (1063203 / 50000) (2126409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717530880 :
    ThetaLowerSegment 1717530880 1717661952 (42937232719407 / 25000) (42940503144139 / 25000) := by
  exact
    packedTile65536 1717530880 1717661952 14 6152 41443 31 _ _ (1063207 / 50000) (2126417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717661952 :
    ThetaLowerSegment 1717661952 1717793024 (42940503144139 / 25000) (85887532274327 / 50000) := by
  exact
    packedTile65536 1717661952 1717793024 14 6138 41444 31 _ _ (2126421 / 100000) (265803 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717793024 :
    ThetaLowerSegment 1717793024 1717924096 (85887532274327 / 50000)
      (171788067661989 / 100000) := by
  exact
    packedTile65536 1717793024 1717924096 14 6115 41446 31 _ _ (2126429 / 100000) (66451 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1717924096 :
    ThetaLowerSegment 1717924096 1718055168 (171788067661989 / 100000) (10737572774217 / 6250) := by
  exact
    packedTile65536 1717924096 1718055168 14 6159 41447 31 _ _ (2126437 / 100000) (53161 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718055168 :
    ThetaLowerSegment 1718055168 1718186240 (10737572774217 / 6250) (42953603565009 / 25000) := by
  exact
    packedTile65536 1718055168 1718186240 14 6231 41449 31 _ _ (531611 / 25000) (2126447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718186240 :
    ThetaLowerSegment 1718186240 1718317312 (42953603565009 / 25000) (21478428784091 / 12500) := by
  exact
    packedTile65536 1718186240 1718317312 14 6121 41451 31 _ _ (531613 / 25000) (425291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718317312 :
    ThetaLowerSegment 1718317312 1718448384 (21478428784091 / 12500) (21480065095061 / 12500) := by
  exact
    packedTile65536 1718317312 1718448384 14 6156 41452 31 _ _ (106323 / 5000) (2126463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718448384 :
    ThetaLowerSegment 1718448384 1718579456 (21480065095061 / 12500) (85926812025071 / 50000) := by
  exact
    packedTile65536 1718448384 1718579456 14 6162 41454 31 _ _ (2126467 / 100000) (212647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718579456 :
    ThetaLowerSegment 1718579456 1718710528 (85926812025071 / 50000) (85933374326921 / 50000) := by
  exact
    packedTile65536 1718579456 1718710528 14 6172 41455 31 _ _ (85059 / 4000) (1063239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718710528 :
    ThetaLowerSegment 1718710528 1718841600 (85933374326921 / 50000)
      (171879798880013 / 100000) := by
  exact
    packedTile65536 1718710528 1718841600 14 6137 41457 31 _ _ (2126483 / 100000) (1063243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718841600 :
    ThetaLowerSegment 1718841600 1718972672 (171879798880013 / 100000)
      (171892953347153 / 100000) := by
  exact
    packedTile65536 1718841600 1718972672 14 6186 41458 31 _ _ (212649 / 10000) (2126493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1718972672 :
    ThetaLowerSegment 1718972672 1719103744 (171892953347153 / 100000)
      (34381237734141 / 20000) := by
  exact
    packedTile65536 1718972672 1719103744 14 6224 41460 31 _ _ (1063249 / 50000) (2126501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719103744 :
    ThetaLowerSegment 1719103744 1719234816 (34381237734141 / 20000) (34383847381077 / 20000) := by
  exact
    packedTile65536 1719103744 1719234816 14 6136 41462 31 _ _ (425301 / 20000) (531627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719234816 :
    ThetaLowerSegment 1719234816 1719365888 (34383847381077 / 20000) (2149153538283 / 1250) := by
  exact
    packedTile65536 1719234816 1719365888 14 6135 41463 31 _ _ (2126513 / 100000) (531629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719365888 :
    ThetaLowerSegment 1719365888 1719496960 (2149153538283 / 1250) (171945486631529 / 100000) := by
  exact
    packedTile65536 1719365888 1719496960 14 6209 41465 31 _ _ (2126521 / 100000) (531631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719496960 :
    ThetaLowerSegment 1719496960 1719628032 (171945486631529 / 100000)
      (171958613688873 / 100000) := by
  exact
    packedTile65536 1719496960 1719628032 14 6173 41466 31 _ _ (66454 / 3125) (2126531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719628032 :
    ThetaLowerSegment 1719628032 1719759104 (171958613688873 / 100000)
      (171971736542529 / 100000) := by
  exact
    packedTile65536 1719628032 1719759104 14 6171 41468 31 _ _ (265817 / 12500) (2126539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719759104 :
    ThetaLowerSegment 1719759104 1719890176 (171971736542529 / 100000)
      (171984846686289 / 100000) := by
  exact
    packedTile65536 1719759104 1719890176 14 6165 41469 31 _ _ (132909 / 6250) (2126547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1719890176 :
    ThetaLowerSegment 1719890176 1720021248 (171984846686289 / 100000)
      (42999527496219 / 25000) := by
  exact
    packedTile65536 1719890176 1720021248 14 6237 41471 31 _ _ (2126551 / 100000) (1063277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720021248 :
    ThetaLowerSegment 1720021248 1720152320 (42999527496219 / 25000) (86005636692543 / 50000) := by
  exact
    packedTile65536 1720021248 1720152320 14 6190 41473 31 _ _ (2126559 / 100000) (1063281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720152320 :
    ThetaLowerSegment 1720152320 1720283392 (86005636692543 / 50000) (86012199275219 / 50000) := by
  exact
    packedTile65536 1720152320 1720283392 14 6172 41474 31 _ _ (1063283 / 50000) (2126569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720283392 :
    ThetaLowerSegment 1720283392 1720414464 (86012199275219 / 50000) (86018717224529 / 50000) := by
  exact
    packedTile65536 1720283392 1720414464 14 6130 41476 31 _ _ (1063287 / 50000) (2126577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720414464 :
    ThetaLowerSegment 1720414464 1720545536 (86018717224529 / 50000) (8602527879329 / 5000) := by
  exact
    packedTile65536 1720414464 1720545536 14 6171 41477 31 _ _ (1063291 / 50000) (425317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720545536 :
    ThetaLowerSegment 1720545536 1720676608 (8602527879329 / 5000) (172063676514121 / 100000) := by
  exact
    packedTile65536 1720545536 1720676608 14 6169 41479 31 _ _ (2126589 / 100000) (66456 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720676608 :
    ThetaLowerSegment 1720676608 1720807680 (172063676514121 / 100000)
      (172076623236657 / 100000) := by
  exact
    packedTile65536 1720676608 1720807680 14 6088 41481 31 _ _ (2126597 / 100000) (10633 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720807680 :
    ThetaLowerSegment 1720807680 1720938752 (172076623236657 / 100000)
      (172089895372221 / 100000) := by
  exact
    packedTile65536 1720807680 1720938752 14 6241 41482 31 _ _ (531651 / 25000) (2126607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1720938752 :
    ThetaLowerSegment 1720938752 1721069824 (172089895372221 / 100000)
      (172103108012577 / 100000) := by
  exact
    packedTile65536 1720938752 1721069824 14 6213 41484 31 _ _ (531653 / 25000) (425323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721069824 :
    ThetaLowerSegment 1721069824 1721200896 (172103108012577 / 100000)
      (172116256904037 / 100000) := by
  exact
    packedTile65536 1721069824 1721200896 14 6183 41485 31 _ _ (106331 / 5000) (2126623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721200896 :
    ThetaLowerSegment 1721200896 1721331968 (172116256904037 / 100000)
      (172129276114531 / 100000) := by
  exact
    packedTile65536 1721200896 1721331968 14 6122 41487 31 _ _ (2126627 / 100000) (212663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721331968 :
    ThetaLowerSegment 1721331968 1721463040 (172129276114531 / 100000)
      (43035574375159 / 25000) := by
  exact
    packedTile65536 1721331968 1721463040 14 6123 41488 31 _ _ (425327 / 20000) (1063319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721463040 :
    ThetaLowerSegment 1721463040 1721594112 (43035574375159 / 25000) (86077671164399 / 50000) := by
  exact
    packedTile65536 1721463040 1721594112 14 6134 41490 31 _ _ (2126643 / 100000) (1063323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721594112 :
    ThetaLowerSegment 1721594112 1721725184 (86077671164399 / 50000) (43042116471487 / 25000) := by
  exact
    packedTile65536 1721594112 1721725184 14 6171 41492 31 _ _ (42533 / 2000) (2126653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721725184 :
    ThetaLowerSegment 1721725184 1721856256 (43042116471487 / 25000) (10761349210363 / 6250) := by
  exact
    packedTile65536 1721725184 1721856256 14 6170 41493 31 _ _ (1063329 / 50000) (2126661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721856256 :
    ThetaLowerSegment 1721856256 1721987328 (10761349210363 / 6250) (172194949202003 / 100000) := by
  exact
    packedTile65536 1721856256 1721987328 14 6283 41495 31 _ _ (425333 / 20000) (531667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1721987328 :
    ThetaLowerSegment 1721987328 1722118400 (172194949202003 / 100000)
      (172208006974223 / 100000) := by
  exact
    packedTile65536 1721987328 1722118400 14 6140 41496 31 _ _ (2126673 / 100000) (531669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722118400 :
    ThetaLowerSegment 1722118400 1722249472 (172208006974223 / 100000) (10763831037737 / 6250) := by
  exact
    packedTile65536 1722118400 1722249472 14 6249 41498 31 _ _ (2126681 / 100000) (531671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722249472 :
    ThetaLowerSegment 1722249472 1722380544 (10763831037737 / 6250) (10764654331829 / 6250) := by
  exact
    packedTile65536 1722249472 1722380544 14 6194 41499 31 _ _ (66459 / 3125) (2126691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722380544 :
    ThetaLowerSegment 1722380544 1722511616 (10764654331829 / 6250) (5382734826954 / 3125) := by
  exact
    packedTile65536 1722380544 1722511616 14 6134 41501 31 _ _ (265837 / 12500) (2126699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722511616 :
    ThetaLowerSegment 1722511616 1722642688 (5382734826954 / 3125) (86130305349801 / 50000) := by
  exact
    packedTile65536 1722511616 1722642688 14 6158 41503 31 _ _ (2126703 / 100000) (1063353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722642688 :
    ThetaLowerSegment 1722642688 1722773760 (86130305349801 / 50000) (21534199549621 / 12500) := by
  exact
    packedTile65536 1722642688 1722773760 14 6106 41504 31 _ _ (2126711 / 100000) (1063357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722773760 :
    ThetaLowerSegment 1722773760 1722904832 (21534199549621 / 12500)
      (172286728886793 / 100000) := by
  exact
    packedTile65536 1722773760 1722904832 14 6175 41506 31 _ _ (2126719 / 100000) (1063361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1722904832 :
    ThetaLowerSegment 1722904832 1723035904 (172286728886793 / 100000)
      (172299672141229 / 100000) := by
  exact
    packedTile65536 1722904832 1723035904 14 6086 41507 31 _ _ (1063363 / 50000) (2126729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723035904 :
    ThetaLowerSegment 1723035904 1723166976 (172299672141229 / 100000) (6892507425063 / 4000) := by
  exact
    packedTile65536 1723035904 1723166976 14 6119 41509 31 _ _ (1063367 / 50000) (2126737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723166976 :
    ThetaLowerSegment 1723166976 1723298048 (6892507425063 / 4000) (86162904872643 / 50000) := by
  exact
    packedTile65536 1723166976 1723298048 14 6171 41511 31 _ _ (2126741 / 100000) (265843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723298048 :
    ThetaLowerSegment 1723298048 1723429120 (86162904872643 / 50000)
      (172338687210481 / 100000) := by
  exact
    packedTile65536 1723298048 1723429120 14 6055 41512 31 _ _ (2126749 / 100000) (66461 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723429120 :
    ThetaLowerSegment 1723429120 1723560192 (172338687210481 / 100000)
      (172351847582797 / 100000) := by
  exact
    packedTile65536 1723429120 1723560192 14 6188 41514 31 _ _ (2126757 / 100000) (53169 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723560192 :
    ThetaLowerSegment 1723560192 1723691264 (172351847582797 / 100000)
      (172364929308161 / 100000) := by
  exact
    packedTile65536 1723560192 1723691264 14 6151 41515 31 _ _ (531691 / 25000) (2126767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723691264 :
    ThetaLowerSegment 1723691264 1723822336 (172364929308161 / 100000)
      (172378238647337 / 100000) := by
  exact
    packedTile65536 1723691264 1723822336 14 6258 41517 31 _ _ (531693 / 25000) (85071 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723822336 :
    ThetaLowerSegment 1723822336 1723953408 (172378238647337 / 100000) (215489272871 / 125) := by
  exact
    packedTile65536 1723822336 1723953408 14 6197 41518 31 _ _ (2126779 / 100000) (1063391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1723953408 :
    ThetaLowerSegment 1723953408 1724084480 (215489272871 / 125) (86202244764851 / 50000) := by
  exact
    packedTile65536 1723953408 1724084480 14 6146 41520 31 _ _ (2126787 / 100000) (212679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724084480 :
    ThetaLowerSegment 1724084480 1724215552 (86202244764851 / 50000)
      (172417626742417 / 100000) := by
  exact
    packedTile65536 1724084480 1724215552 14 6177 41522 31 _ _ (425359 / 20000) (1063399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724215552 :
    ThetaLowerSegment 1724215552 1724346624 (172417626742417 / 100000)
      (172430564078983 / 100000) := by
  exact
    packedTile65536 1724215552 1724346624 14 6083 41523 31 _ _ (1063401 / 50000) (425361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724346624 :
    ThetaLowerSegment 1724346624 1724477696 (172430564078983 / 100000)
      (172443760935033 / 100000) := by
  exact
    packedTile65536 1724346624 1724477696 14 6205 41525 31 _ _ (212681 / 10000) (2126813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724477696 :
    ThetaLowerSegment 1724477696 1724608768 (172443760935033 / 100000)
      (172456770680739 / 100000) := by
  exact
    packedTile65536 1724477696 1724608768 14 6117 41526 31 _ _ (1063409 / 50000) (2126821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724608768 :
    ThetaLowerSegment 1724608768 1724739840 (172456770680739 / 100000)
      (43117502541591 / 25000) := by
  exact
    packedTile65536 1724608768 1724739840 14 6225 41528 31 _ _ (85073 / 4000) (531707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724739840 :
    ThetaLowerSegment 1724739840 1724870912 (43117502541591 / 25000) (10780199251477 / 6250) := by
  exact
    packedTile65536 1724739840 1724870912 14 6196 41529 31 _ _ (2126833 / 100000) (531709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724870912 :
    ThetaLowerSegment 1724870912 1725001984 (10780199251477 / 6250) (10781009577517 / 6250) := by
  exact
    packedTile65536 1724870912 1725001984 14 6096 41531 31 _ _ (53171 / 2500) (2126843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725001984 :
    ThetaLowerSegment 1725001984 1725133056 (10781009577517 / 6250) (2156363316681 / 1250) := by
  exact
    packedTile65536 1725001984 1725133056 14 6071 41533 31 _ _ (66464 / 3125) (2126851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725133056 :
    ThetaLowerSegment 1725133056 1725264128 (2156363316681 / 1250) (431305204233 / 250) := by
  exact
    packedTile65536 1725133056 1725264128 14 6120 41534 31 _ _ (265857 / 12500) (2126859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725264128 :
    ThetaLowerSegment 1725264128 1725395200 (431305204233 / 250) (172535283131841 / 100000) := by
  exact
    packedTile65536 1725264128 1725395200 14 6207 41536 31 _ _ (2126863 / 100000) (1063433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725395200 :
    ThetaLowerSegment 1725395200 1725526272 (172535283131841 / 100000)
      (43137077554179 / 25000) := by
  exact
    packedTile65536 1725395200 1725526272 14 6125 41537 31 _ _ (2126871 / 100000) (1063437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725526272 :
    ThetaLowerSegment 1725526272 1725657344 (43137077554179 / 25000) (21570168497357 / 12500) := by
  exact
    packedTile65536 1725526272 1725657344 14 6130 41539 31 _ _ (1063439 / 50000) (2126881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725657344 :
    ThetaLowerSegment 1725657344 1725788416 (21570168497357 / 12500) (43143604955053 / 25000) := by
  exact
    packedTile65536 1725657344 1725788416 14 6146 41541 31 _ _ (1063443 / 50000) (2126889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725788416 :
    ThetaLowerSegment 1725788416 1725919488 (43143604955053 / 25000)
      (172587532115557 / 100000) := by
  exact
    packedTile65536 1725788416 1725919488 14 6165 41542 31 _ _ (2126893 / 100000) (132931 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1725919488 :
    ThetaLowerSegment 1725919488 1726050560 (172587532115557 / 100000) (10787545861879 / 6250) := by
  exact
    packedTile65536 1725919488 1726050560 14 6207 41544 31 _ _ (2126901 / 100000) (265863 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726050560 :
    ThetaLowerSegment 1726050560 1726181632 (10787545861879 / 6250) (172613973798589 / 100000) := by
  exact
    packedTile65536 1726050560 1726181632 14 6225 41545 31 _ _ (2126909 / 100000) (66466 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726181632 :
    ThetaLowerSegment 1726181632 1726312704 (172613973798589 / 100000)
      (172626954366937 / 100000) := by
  exact
    packedTile65536 1726181632 1726312704 14 6103 41547 31 _ _ (531729 / 25000) (2126919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726312704 :
    ThetaLowerSegment 1726312704 1726443776 (172626954366937 / 100000)
      (172640085995713 / 100000) := by
  exact
    packedTile65536 1726312704 1726443776 14 6174 41548 31 _ _ (531731 / 25000) (2126927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726443776 :
    ThetaLowerSegment 1726443776 1726574848 (172640085995713 / 100000)
      (172653200652259 / 100000) := by
  exact
    packedTile65536 1726443776 1726574848 14 6166 41550 31 _ _ (2126931 / 100000) (1063467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726574848 :
    ThetaLowerSegment 1726574848 1726705920 (172653200652259 / 100000)
      (172666468497741 / 100000) := by
  exact
    packedTile65536 1726574848 1726705920 14 6238 41552 31 _ _ (2126939 / 100000) (1063471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726705920 :
    ThetaLowerSegment 1726705920 1726836992 (172666468497741 / 100000)
      (172679664076929 / 100000) := by
  exact
    packedTile65536 1726705920 1726836992 14 6204 41553 31 _ _ (2126947 / 100000) (42539 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726836992 :
    ThetaLowerSegment 1726836992 1726968064 (172679664076929 / 100000)
      (172692887349947 / 100000) := by
  exact
    packedTile65536 1726836992 1726968064 14 6217 41555 31 _ _ (1063477 / 50000) (2126957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1726968064 :
    ThetaLowerSegment 1726968064 1727099136 (172692887349947 / 100000)
      (172705919246121 / 100000) := by
  exact
    packedTile65536 1726968064 1727099136 14 6127 41556 31 _ _ (1063481 / 50000) (425393 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727099136 :
    ThetaLowerSegment 1727099136 1727230208 (172705919246121 / 100000)
      (21589879532993 / 12500) := by
  exact
    packedTile65536 1727099136 1727230208 14 6167 41558 31 _ _ (2126969 / 100000) (531743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727230208 :
    ThetaLowerSegment 1727230208 1727361280 (21589879532993 / 12500)
      (172732115045517 / 100000) := by
  exact
    packedTile65536 1727230208 1727361280 14 6149 41559 31 _ _ (2126977 / 100000) (106349 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727361280 :
    ThetaLowerSegment 1727361280 1727492352 (172732115045517 / 100000)
      (172745115177837 / 100000) := by
  exact
    packedTile65536 1727361280 1727492352 14 6112 41561 31 _ _ (425397 / 20000) (531747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727492352 :
    ThetaLowerSegment 1727492352 1727623424 (172745115177837 / 100000)
      (34551638810329 / 20000) := by
  exact
    packedTile65536 1727492352 1727623424 14 6149 41563 31 _ _ (132937 / 6250) (425399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727623424 :
    ThetaLowerSegment 1727623424 1727754496 (34551638810329 / 20000) (34554228220129 / 20000) := by
  exact
    packedTile65536 1727623424 1727754496 14 6087 41564 31 _ _ (2127 / 100) (2127003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727754496 :
    ThetaLowerSegment 1727754496 1727885568 (34554228220129 / 20000)
      (172784281749891 / 100000) := by
  exact
    packedTile65536 1727754496 1727885568 14 6178 41566 31 _ _ (2127007 / 100000) (212701 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1727885568 :
    ThetaLowerSegment 1727885568 1728016640 (172784281749891 / 100000)
      (172797307589751 / 100000) := by
  exact
    packedTile65536 1727885568 1728016640 14 6124 41567 31 _ _ (425403 / 20000) (1063509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728016640 :
    ThetaLowerSegment 1728016640 1728147712 (172797307589751 / 100000)
      (86405167802813 / 50000) := by
  exact
    packedTile65536 1728016640 1728147712 14 6125 41569 31 _ _ (2127023 / 100000) (1063513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728147712 :
    ThetaLowerSegment 1728147712 1728278784 (86405167802813 / 50000) (86411719055213 / 50000) := by
  exact
    packedTile65536 1728147712 1728278784 14 6160 41570 31 _ _ (212703 / 10000) (2127033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728278784 :
    ThetaLowerSegment 1728278784 1728409856 (86411719055213 / 50000) (3456734556877 / 2000) := by
  exact
    packedTile65536 1728278784 1728409856 14 6248 41572 31 _ _ (1063519 / 50000) (2127041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728409856 :
    ThetaLowerSegment 1728409856 1728540928 (3456734556877 / 2000) (17284975386743 / 10000) := by
  exact
    packedTile65536 1728409856 1728540928 14 6124 41574 31 _ _ (425409 / 20000) (265881 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728540928 :
    ThetaLowerSegment 1728540928 1728672000 (17284975386743 / 10000)
      (172862854386857 / 100000) := by
  exact
    packedTile65536 1728540928 1728672000 14 6159 41575 31 _ _ (2127053 / 100000) (132941 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728672000 :
    ThetaLowerSegment 1728672000 1728803072 (172862854386857 / 100000)
      (172875959203517 / 100000) := by
  exact
    packedTile65536 1728672000 1728803072 14 6161 41577 31 _ _ (106353 / 5000) (2127063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728803072 :
    ThetaLowerSegment 1728803072 1728934144 (172875959203517 / 100000)
      (172889055561193 / 100000) := by
  exact
    packedTile65536 1728803072 1728934144 14 6157 41578 31 _ _ (531767 / 25000) (2127071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728934144 :
    ThetaLowerSegment 1728934144 1729065216 (172889055561193 / 100000)
      (34580458045613 / 20000) := by
  exact
    packedTile65536 1728934144 1729065216 14 6222 41580 31 _ _ (531769 / 25000) (2127079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729065216 :
    ThetaLowerSegment 1729065216 1729196288 (34580458045613 / 20000) (4322885092369 / 2500) := by
  exact
    packedTile65536 1729065216 1729196288 14 6165 41582 31 _ _ (2127083 / 100000) (1063543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729196288 :
    ThetaLowerSegment 1729196288 1729327360 (4322885092369 / 2500) (86464276685661 / 50000) := by
  exact
    packedTile65536 1729196288 1729327360 14 6182 41583 31 _ _ (2127091 / 100000) (1063547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729327360 :
    ThetaLowerSegment 1729327360 1729458432 (86464276685661 / 50000) (86470847291383 / 50000) := by
  exact
    packedTile65536 1729327360 1729458432 14 6178 41585 31 _ _ (1063549 / 50000) (2127101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729458432 :
    ThetaLowerSegment 1729458432 1729589504 (86470847291383 / 50000) (17295484860627 / 10000) := by
  exact
    packedTile65536 1729458432 1729589504 14 6184 41586 31 _ _ (1063553 / 50000) (2127109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729589504 :
    ThetaLowerSegment 1729589504 1729720576 (17295484860627 / 10000)
      (172967779326197 / 100000) := by
  exact
    packedTile65536 1729589504 1729720576 14 6079 41588 31 _ _ (2127113 / 100000) (531779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729720576 :
    ThetaLowerSegment 1729720576 1729851648 (172967779326197 / 100000)
      (172980997256091 / 100000) := by
  exact
    packedTile65536 1729720576 1729851648 14 6214 41589 31 _ _ (2127121 / 100000) (531781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729851648 :
    ThetaLowerSegment 1729851648 1729982720 (172980997256091 / 100000)
      (172994066336667 / 100000) := by
  exact
    packedTile65536 1729851648 1729982720 14 6144 41591 31 _ _ (2127129 / 100000) (531783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1729982720 :
    ThetaLowerSegment 1729982720 1730113792 (172994066336667 / 100000)
      (173007007832091 / 100000) := by
  exact
    packedTile65536 1729982720 1730113792 14 6084 41593 31 _ _ (66473 / 3125) (2127139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730113792 :
    ThetaLowerSegment 1730113792 1730244864 (173007007832091 / 100000)
      (173019970647627 / 100000) := by
  exact
    packedTile65536 1730113792 1730244864 14 6094 41594 31 _ _ (265893 / 12500) (2127147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730244864 :
    ThetaLowerSegment 1730244864 1730375936 (173019970647627 / 100000)
      (86516478452241 / 50000) := by
  exact
    packedTile65536 1730244864 1730375936 14 6105 41596 31 _ _ (2127151 / 100000) (1063577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730375936 :
    ThetaLowerSegment 1730375936 1730507008 (86516478452241 / 50000)
      (173046015533583 / 100000) := by
  exact
    packedTile65536 1730375936 1730507008 14 6139 41597 31 _ _ (2127159 / 100000) (1063581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730507008 :
    ThetaLowerSegment 1730507008 1730638080 (173046015533583 / 100000)
      (86529607302409 / 50000) := by
  exact
    packedTile65536 1730507008 1730638080 14 6205 41599 31 _ _ (2127167 / 100000) (212717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730638080 :
    ThetaLowerSegment 1730638080 1730769152 (86529607302409 / 50000) (4326811832009 / 2500) := by
  exact
    packedTile65536 1730638080 1730769152 14 6233 41600 31 _ _ (1063587 / 50000) (2127177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730769152 :
    ThetaLowerSegment 1730769152 1730900224 (4326811832009 / 2500) (43271373972141 / 25000) := by
  exact
    packedTile65536 1730769152 1730900224 14 6122 41602 31 _ _ (1063591 / 50000) (425437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1730900224 :
    ThetaLowerSegment 1730900224 1731031296 (43271373972141 / 25000)
      (173098771675113 / 100000) := by
  exact
    packedTile65536 1730900224 1731031296 14 6241 41604 31 _ _ (2127189 / 100000) (265899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731031296 :
    ThetaLowerSegment 1731031296 1731162368 (173098771675113 / 100000)
      (43277968270359 / 25000) := by
  exact
    packedTile65536 1731031296 1731162368 14 6159 41605 31 _ _ (2127197 / 100000) (2659 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731162368 :
    ThetaLowerSegment 1731162368 1731293440 (43277968270359 / 25000) (43281234592101 / 25000) := by
  exact
    packedTile65536 1731162368 1731293440 14 6142 41607 31 _ _ (531801 / 25000) (2127207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731293440 :
    ThetaLowerSegment 1731293440 1731424512 (43281234592101 / 25000) (43284439236979 / 25000) := by
  exact
    packedTile65536 1731293440 1731424512 14 6026 41608 31 _ _ (531803 / 25000) (425443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731424512 :
    ThetaLowerSegment 1731424512 1731555584 (43284439236979 / 25000) (43287693883579 / 25000) := by
  exact
    packedTile65536 1731424512 1731555584 14 6120 41610 31 _ _ (106361 / 5000) (2127223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731555584 :
    ThetaLowerSegment 1731555584 1731686656 (43287693883579 / 25000) (5411374151582 / 3125) := by
  exact
    packedTile65536 1731555584 1731686656 14 6204 41611 31 _ _ (2127227 / 100000) (212723 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731686656 :
    ThetaLowerSegment 1731686656 1731817728 (5411374151582 / 3125) (21647128195573 / 12500) := by
  exact
    packedTile65536 1731686656 1731817728 14 6136 41613 31 _ _ (425447 / 20000) (1063619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731817728 :
    ThetaLowerSegment 1731817728 1731948800 (21647128195573 / 12500) (86595044478853 / 50000) := by
  exact
    packedTile65536 1731817728 1731948800 14 6141 41615 31 _ _ (1063621 / 50000) (425449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1731948800 :
    ThetaLowerSegment 1731948800 1732079872 (86595044478853 / 50000) (21650411599807 / 12500) := by
  exact
    packedTile65536 1731948800 1732079872 14 6207 41616 31 _ _ (8509 / 400) (2127253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732079872 :
    ThetaLowerSegment 1732079872 1732210944 (21650411599807 / 12500) (21652045333183 / 12500) := by
  exact
    packedTile65536 1732079872 1732210944 14 6144 41618 31 _ _ (2127257 / 100000) (106363 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732210944 :
    ThetaLowerSegment 1732210944 1732342016 (21652045333183 / 12500) (43307390054381 / 25000) := by
  exact
    packedTile65536 1732210944 1732342016 14 6204 41619 31 _ _ (425453 / 20000) (531817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732342016 :
    ThetaLowerSegment 1732342016 1732473088 (43307390054381 / 25000) (43310649036617 / 25000) := by
  exact
    packedTile65536 1732342016 1732473088 14 6128 41621 31 _ _ (2127273 / 100000) (531819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732473088 :
    ThetaLowerSegment 1732473088 1732604160 (43310649036617 / 25000) (43313886756777 / 25000) := by
  exact
    packedTile65536 1732473088 1732604160 14 6088 41622 31 _ _ (26591 / 1250) (2127283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732604160 :
    ThetaLowerSegment 1732604160 1732735232 (43313886756777 / 25000) (43317188307753 / 25000) := by
  exact
    packedTile65536 1732604160 1732735232 14 6208 41624 31 _ _ (265911 / 12500) (2127291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732735232 :
    ThetaLowerSegment 1732735232 1732866304 (43317188307753 / 25000)
      (173281804185837 / 100000) := by
  exact
    packedTile65536 1732735232 1732866304 14 6135 41626 31 _ _ (425459 / 20000) (1063649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732866304 :
    ThetaLowerSegment 1732866304 1732997376 (173281804185837 / 100000) (69317930163 / 40) := by
  exact
    packedTile65536 1732866304 1732997376 14 6121 41627 31 _ _ (2127303 / 100000) (1063653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732997376 :
    ThetaLowerSegment 1732997376 1733128448 (69317930163 / 40) (17330809343997 / 10000) := by
  exact
    packedTile65536 1732997376 1733128448 14 6237 41629 31 _ _ (212731 / 10000) (2127313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733128448 :
    ThetaLowerSegment 1733128448 1733259520 (17330809343997 / 10000) (86660688206781 / 50000) := by
  exact
    packedTile65536 1733128448 1733259520 14 6244 41630 31 _ _ (1063659 / 50000) (2127321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733259520 :
    ThetaLowerSegment 1733259520 1733390592 (86660688206781 / 50000) (86667189311981 / 50000) := by
  exact
    packedTile65536 1733259520 1733390592 14 6112 41632 31 _ _ (85093 / 4000) (66479 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733390592 :
    ThetaLowerSegment 1733390592 1733521664 (86667189311981 / 50000)
      (173347425557251 / 100000) := by
  exact
    packedTile65536 1733390592 1733521664 14 6133 41634 31 _ _ (2127333 / 100000) (265917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733521664 :
    ThetaLowerSegment 1733521664 1733652736 (173347425557251 / 100000)
      (173360504449719 / 100000) := by
  exact
    packedTile65536 1733521664 1733652736 14 6148 41635 31 _ _ (2127341 / 100000) (132959 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733652736 :
    ThetaLowerSegment 1733652736 1733783808 (173360504449719 / 100000)
      (173373562111743 / 100000) := by
  exact
    packedTile65536 1733652736 1733783808 14 6138 41637 31 _ _ (531837 / 25000) (2127351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733783808 :
    ThetaLowerSegment 1733783808 1733914880 (173373562111743 / 100000)
      (34677310774967 / 20000) := by
  exact
    packedTile65536 1733783808 1733914880 14 6107 41638 31 _ _ (531839 / 25000) (2127359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1733914880 :
    ThetaLowerSegment 1733914880 1734045952 (34677310774967 / 20000) (86699826024413 / 50000) := by
  exact
    packedTile65536 1733914880 1734045952 14 6157 41640 31 _ _ (2127363 / 100000) (1063683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734045952 :
    ThetaLowerSegment 1734045952 1734177024 (86699826024413 / 50000) (86706450657707 / 50000) := by
  exact
    packedTile65536 1734045952 1734177024 14 6228 41641 31 _ _ (2127371 / 100000) (1063687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734177024 :
    ThetaLowerSegment 1734177024 1734308096 (86706450657707 / 50000) (4335646798477 / 2500) := by
  exact
    packedTile65536 1734177024 1734308096 14 6097 41643 31 _ _ (1063689 / 50000) (2127381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734308096 :
    ThetaLowerSegment 1734308096 1734439168 (4335646798477 / 2500) (86719570222781 / 50000) := by
  exact
    packedTile65536 1734308096 1734439168 14 6237 41645 31 _ _ (1063693 / 50000) (2127389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734439168 :
    ThetaLowerSegment 1734439168 1734570240 (86719570222781 / 50000)
      (173452102651111 / 100000) := by
  exact
    packedTile65536 1734439168 1734570240 14 6093 41646 31 _ _ (2127393 / 100000) (531849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734570240 :
    ThetaLowerSegment 1734570240 1734701312 (173452102651111 / 100000)
      (21683149068683 / 12500) := by
  exact
    packedTile65536 1734570240 1734701312 14 6153 41648 31 _ _ (2127401 / 100000) (531851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734701312 :
    ThetaLowerSegment 1734701312 1734832384 (21683149068683 / 12500) (21684774409159 / 12500) := by
  exact
    packedTile65536 1734701312 1734832384 14 6112 41649 31 _ _ (2127409 / 100000) (531853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734832384 :
    ThetaLowerSegment 1734832384 1734963456 (21684774409159 / 12500) (21686424220267 / 12500) := by
  exact
    packedTile65536 1734832384 1734963456 14 6204 41651 31 _ _ (265927 / 12500) (2127419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1734963456 :
    ThetaLowerSegment 1734963456 1735094528 (21686424220267 / 12500) (21688047710707 / 12500) := by
  exact
    packedTile65536 1734963456 1735094528 14 6105 41652 31 _ _ (66482 / 3125) (2127427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735094528 :
    ThetaLowerSegment 1735094528 1735225600 (21688047710707 / 12500) (86758617811879 / 50000) := by
  exact
    packedTile65536 1735094528 1735225600 14 6042 41654 31 _ _ (2127431 / 100000) (1063717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735225600 :
    ThetaLowerSegment 1735225600 1735356672 (86758617811879 / 50000)
      (173530398088851 / 100000) := by
  exact
    packedTile65536 1735225600 1735356672 14 6187 41656 31 _ _ (2127439 / 100000) (1063721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735356672 :
    ThetaLowerSegment 1735356672 1735487744 (173530398088851 / 100000)
      (173543488264089 / 100000) := by
  exact
    packedTile65536 1735356672 1735487744 14 6153 41657 31 _ _ (1063723 / 50000) (2127449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735487744 :
    ThetaLowerSegment 1735487744 1735618816 (173543488264089 / 100000)
      (173556650821987 / 100000) := by
  exact
    packedTile65536 1735487744 1735618816 14 6187 41659 31 _ _ (1063727 / 50000) (2127457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735618816 :
    ThetaLowerSegment 1735618816 1735749888 (173556650821987 / 100000) (4339245654699 / 2500) := by
  exact
    packedTile65536 1735618816 1735749888 14 6193 41660 31 _ _ (2127461 / 100000) (265933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735749888 :
    ThetaLowerSegment 1735749888 1735880960 (4339245654699 / 2500) (173582895230027 / 100000) := by
  exact
    packedTile65536 1735749888 1735880960 14 6143 41662 31 _ _ (2127469 / 100000) (132967 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1735880960 :
    ThetaLowerSegment 1735880960 1736012032 (173582895230027 / 100000)
      (173595834545141 / 100000) := by
  exact
    packedTile65536 1735880960 1736012032 14 6082 41663 31 _ _ (2127477 / 100000) (53187 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736012032 :
    ThetaLowerSegment 1736012032 1736143104 (173595834545141 / 100000)
      (173609139830077 / 100000) := by
  exact
    packedTile65536 1736012032 1736143104 14 6254 41665 31 _ _ (531871 / 25000) (2127487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736143104 :
    ThetaLowerSegment 1736143104 1736274176 (173609139830077 / 100000)
      (173622215395909 / 100000) := by
  exact
    packedTile65536 1736143104 1736274176 14 6146 41667 31 _ _ (531873 / 25000) (425499 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736274176 :
    ThetaLowerSegment 1736274176 1736405248 (173622215395909 / 100000)
      (34727044584959 / 20000) := by
  exact
    packedTile65536 1736274176 1736405248 14 6114 41668 31 _ _ (2127499 / 100000) (1063751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736405248 :
    ThetaLowerSegment 1736405248 1736536320 (34727044584959 / 20000) (86824139717627 / 50000) := by
  exact
    packedTile65536 1736405248 1736536320 14 6137 41670 31 _ _ (2127507 / 100000) (212751 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736536320 :
    ThetaLowerSegment 1736536320 1736667392 (86824139717627 / 50000) (21707687209967 / 12500) := by
  exact
    packedTile65536 1736536320 1736667392 14 6213 41671 31 _ _ (1063757 / 50000) (2127517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736667392 :
    ThetaLowerSegment 1736667392 1736798464 (21707687209967 / 12500) (86837281396169 / 50000) := by
  exact
    packedTile65536 1736667392 1736798464 14 6141 41673 31 _ _ (1063761 / 50000) (85101 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736798464 :
    ThetaLowerSegment 1736798464 1736929536 (86837281396169 / 50000) (6947501884073 / 4000) := by
  exact
    packedTile65536 1736798464 1736929536 14 6103 41674 31 _ _ (2127529 / 100000) (531883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1736929536 :
    ThetaLowerSegment 1736929536 1737060608 (6947501884073 / 4000) (34740160331467 / 20000) := by
  exact
    packedTile65536 1736929536 1737060608 14 6230 41676 31 _ _ (2127537 / 100000) (106377 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737060608 :
    ThetaLowerSegment 1737060608 1737191680 (34740160331467 / 20000) (34742727852773 / 20000) := by
  exact
    packedTile65536 1737060608 1737191680 14 6034 41678 31 _ _ (425509 / 20000) (531887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737191680 :
    ThetaLowerSegment 1737191680 1737322752 (34742727852773 / 20000)
      (173726906678137 / 100000) := by
  exact
    packedTile65536 1737191680 1737322752 14 6236 41679 31 _ _ (66486 / 3125) (425511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737322752 :
    ThetaLowerSegment 1737322752 1737339136 (173726906678137 / 100000)
      (173728491710337 / 100000) := by
  exact
    packedTile65536 1737322752 1737339136 11 745 41681 31 _ _ (53189 / 2500) (2127563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1737339136 :
    ThetaLowerSegment 1737339136 1737341184 (173728491710337 / 100000)
      (43432179839841 / 25000) := by
  exact
    packedTile65536 1737339136 1737341184 8 107 41681 31 _ _ (2127561 / 100000) (531891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1705341184_1737341184 :
    ThetaLowerSegment 1705341184 1737341184 (85264617382019 / 50000) (43432179839841 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1705341184 cell1705472256)
                  (ThetaLowerSegment.join cell1705603328 cell1705734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1705865472 cell1705996544)
                  (ThetaLowerSegment.join cell1706127616 cell1706258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1706389760 cell1706520832)
                  (ThetaLowerSegment.join cell1706651904 cell1706782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1706914048 cell1707045120)
                  (ThetaLowerSegment.join cell1707176192 cell1707307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1707438336 cell1707569408)
                  (ThetaLowerSegment.join cell1707700480 cell1707831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1707962624 cell1708093696)
                  (ThetaLowerSegment.join cell1708224768 cell1708355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1708486912 cell1708617984)
                  (ThetaLowerSegment.join cell1708749056 cell1708880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1709011200 cell1709142272)
                  (ThetaLowerSegment.join cell1709273344 cell1709404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1709535488 cell1709666560)
                  (ThetaLowerSegment.join cell1709797632 cell1709928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1710059776 cell1710190848)
                  (ThetaLowerSegment.join cell1710321920 cell1710452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1710584064 cell1710715136)
                  (ThetaLowerSegment.join cell1710846208 cell1710977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1711108352 cell1711239424)
                  (ThetaLowerSegment.join cell1711370496 cell1711501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1711632640 cell1711763712)
                  (ThetaLowerSegment.join cell1711894784 cell1712025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1712156928 cell1712288000)
                  (ThetaLowerSegment.join cell1712419072 cell1712550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1712681216 cell1712812288)
                  (ThetaLowerSegment.join cell1712943360 cell1713074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1713205504 cell1713336576)
                  (ThetaLowerSegment.join cell1713467648 cell1713598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1713729792 cell1713860864)
                  (ThetaLowerSegment.join cell1713991936 cell1714123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1714254080 cell1714385152)
                  (ThetaLowerSegment.join cell1714516224 cell1714647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1714778368 cell1714909440)
                  (ThetaLowerSegment.join cell1715040512 cell1715171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1715302656 cell1715433728)
                  (ThetaLowerSegment.join cell1715564800 cell1715695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1715826944 cell1715958016)
                  (ThetaLowerSegment.join cell1716089088 cell1716220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1716351232 cell1716482304)
                  (ThetaLowerSegment.join cell1716613376 cell1716744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1716875520 cell1717006592)
                  (ThetaLowerSegment.join cell1717137664 cell1717268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1717399808 cell1717530880)
                  (ThetaLowerSegment.join cell1717661952 cell1717793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1717924096 cell1718055168)
                  (ThetaLowerSegment.join cell1718186240 cell1718317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1718448384 cell1718579456)
                  (ThetaLowerSegment.join cell1718710528 cell1718841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1718972672 cell1719103744)
                  (ThetaLowerSegment.join cell1719234816 cell1719365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1719496960 cell1719628032)
                  (ThetaLowerSegment.join cell1719759104 cell1719890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1720021248 cell1720152320)
                  (ThetaLowerSegment.join cell1720283392 cell1720414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1720545536 cell1720676608)
                  (ThetaLowerSegment.join cell1720807680 cell1720938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1721069824 cell1721200896)
                  (ThetaLowerSegment.join cell1721331968 cell1721463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1721594112 cell1721725184)
                  (ThetaLowerSegment.join cell1721856256 cell1721987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1722118400 cell1722249472)
                  (ThetaLowerSegment.join cell1722380544 cell1722511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1722642688 cell1722773760)
                  (ThetaLowerSegment.join cell1722904832 cell1723035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1723166976 cell1723298048)
                  (ThetaLowerSegment.join cell1723429120 cell1723560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1723691264 cell1723822336)
                  (ThetaLowerSegment.join cell1723953408 cell1724084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1724215552 cell1724346624)
                  (ThetaLowerSegment.join cell1724477696 cell1724608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1724739840 cell1724870912)
                  (ThetaLowerSegment.join cell1725001984 cell1725133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1725264128 cell1725395200)
                  (ThetaLowerSegment.join cell1725526272 cell1725657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1725788416 cell1725919488)
                  (ThetaLowerSegment.join cell1726050560 cell1726181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1726312704 cell1726443776)
                  (ThetaLowerSegment.join cell1726574848 cell1726705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1726836992 cell1726968064)
                  (ThetaLowerSegment.join cell1727099136 cell1727230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1727361280 cell1727492352)
                  (ThetaLowerSegment.join cell1727623424 cell1727754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1727885568 cell1728016640)
                  (ThetaLowerSegment.join cell1728147712 cell1728278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1728409856 cell1728540928)
                  (ThetaLowerSegment.join cell1728672000 cell1728803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1728934144 cell1729065216)
                  (ThetaLowerSegment.join cell1729196288 cell1729327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1729458432 cell1729589504)
                  (ThetaLowerSegment.join cell1729720576 cell1729851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1729982720 cell1730113792)
                  (ThetaLowerSegment.join cell1730244864 cell1730375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1730507008 cell1730638080)
                  (ThetaLowerSegment.join cell1730769152 cell1730900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1731031296 cell1731162368)
                  (ThetaLowerSegment.join cell1731293440 cell1731424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1731555584 cell1731686656)
                  (ThetaLowerSegment.join cell1731817728 cell1731948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1732079872 cell1732210944)
                  (ThetaLowerSegment.join cell1732342016 cell1732473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1732604160 cell1732735232)
                  (ThetaLowerSegment.join cell1732866304 cell1732997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1733128448 cell1733259520)
                  (ThetaLowerSegment.join cell1733390592 cell1733521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1733652736 cell1733783808)
                  (ThetaLowerSegment.join cell1733914880 cell1734045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1734177024 cell1734308096)
                  (ThetaLowerSegment.join cell1734439168 cell1734570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1734701312 cell1734832384)
                  (ThetaLowerSegment.join cell1734963456 cell1735094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1735225600 cell1735356672)
                  (ThetaLowerSegment.join cell1735487744 cell1735618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1735749888 cell1735880960)
                  (ThetaLowerSegment.join cell1736012032 cell1736143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1736274176 cell1736405248)
                  (ThetaLowerSegment.join cell1736536320 cell1736667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1736798464 cell1736929536)
                (ThetaLowerSegment.join cell1737060608 cell1737191680))
              (ThetaLowerSegment.join cell1737322752 cell1737339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
