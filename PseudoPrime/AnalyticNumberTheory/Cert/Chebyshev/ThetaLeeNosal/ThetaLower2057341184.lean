/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2057341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2025341184 :
    ThetaLowerSegment 2025341184 2025472256 (50632294223973 / 25000)
      (202542319295459 / 100000) := by
  exact
    packedTile65536 2025341184 2025472256 14 6133 45003 31 _ _ (2142899 / 100000) (1071451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025472256 :
    ThetaLowerSegment 2025472256 2025603328 (202542319295459 / 100000)
      (101277655864237 / 50000) := by
  exact
    packedTile65536 2025472256 2025603328 14 6063 45005 31 _ _ (428581 / 20000) (535727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025603328 :
    ThetaLowerSegment 2025603328 2025734400 (101277655864237 / 50000)
      (101284239961357 / 50000) := by
  exact
    packedTile65536 2025603328 2025734400 14 6145 45006 31 _ _ (66966 / 3125) (428583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025734400 :
    ThetaLowerSegment 2025734400 2025865472 (101284239961357 / 50000) (25322689947343 / 12500) := by
  exact
    packedTile65536 2025734400 2025865472 14 6085 45008 31 _ _ (1071459 / 50000) (2142921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025865472 :
    ThetaLowerSegment 2025865472 2025996544 (25322689947343 / 12500) (50648647855311 / 25000) := by
  exact
    packedTile65536 2025865472 2025996544 14 6100 45009 31 _ _ (85717 / 4000) (133933 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2025996544 :
    ThetaLowerSegment 2025996544 2026127616 (50648647855311 / 25000) (101303919510343 / 50000) := by
  exact
    packedTile65536 2025996544 2026127616 14 6182 45011 31 _ _ (2142931 / 100000) (1071467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026127616 :
    ThetaLowerSegment 2026127616 2026258688 (101303919510343 / 50000) (20262103523289 / 10000) := by
  exact
    packedTile65536 2026127616 2026258688 14 6158 45012 31 _ _ (1071469 / 50000) (2142941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026258688 :
    ThetaLowerSegment 2026258688 2026389760 (20262103523289 / 10000) (4052683858181 / 2000) := by
  exact
    packedTile65536 2026258688 2026389760 14 6140 45013 31 _ _ (66967 / 3125) (2142947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026389760 :
    ThetaLowerSegment 2026389760 2026520832 (4052683858181 / 2000) (202647241337689 / 100000) := by
  exact
    packedTile65536 2026389760 2026520832 14 6089 45015 31 _ _ (2142951 / 100000) (1071477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026520832 :
    ThetaLowerSegment 2026520832 2026651904 (202647241337689 / 100000) (1266626730907 / 625) := by
  exact
    packedTile65536 2026520832 2026651904 14 6083 45016 31 _ _ (2142957 / 100000) (26787 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026651904 :
    ThetaLowerSegment 2026651904 2026782976 (1266626730907 / 625) (5066834261379 / 2500) := by
  exact
    packedTile65536 2026651904 2026782976 14 6110 45018 31 _ _ (535741 / 25000) (2142967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026782976 :
    ThetaLowerSegment 2026782976 2026914048 (5066834261379 / 2500) (2533582032231 / 1250) := by
  exact
    packedTile65536 2026782976 2026914048 14 6156 45019 31 _ _ (214297 / 10000) (2142973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2026914048 :
    ThetaLowerSegment 2026914048 2027045120 (2533582032231 / 1250) (50674938686223 / 25000) := by
  exact
    packedTile65536 2026914048 2027045120 14 6156 45021 31 _ _ (2142977 / 100000) (107149 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027045120 :
    ThetaLowerSegment 2027045120 2027176192 (50674938686223 / 25000) (20271275407977 / 10000) := by
  exact
    packedTile65536 2027045120 2027176192 14 6066 45022 31 _ _ (2142983 / 100000) (1071493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027176192 :
    ThetaLowerSegment 2027176192 2027307264 (20271275407977 / 10000)
      (202725798453813 / 100000) := by
  exact
    packedTile65536 2027176192 2027307264 14 6087 45024 31 _ _ (2142989 / 100000) (133937 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027307264 :
    ThetaLowerSegment 2027307264 2027438336 (202725798453813 / 100000)
      (202738947877269 / 100000) := by
  exact
    packedTile65536 2027307264 2027438336 14 6136 45025 31 _ _ (535749 / 25000) (2142999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027438336 :
    ThetaLowerSegment 2027438336 2027569408 (202738947877269 / 100000)
      (202752170199609 / 100000) := by
  exact
    packedTile65536 2027438336 2027569408 14 6170 45027 31 _ _ (1071501 / 50000) (428601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027569408 :
    ThetaLowerSegment 2027569408 2027700480 (202752170199609 / 100000)
      (202765045397681 / 100000) := by
  exact
    packedTile65536 2027569408 2027700480 14 6008 45028 31 _ _ (2143009 / 100000) (535753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027700480 :
    ThetaLowerSegment 2027700480 2027831552 (202765045397681 / 100000)
      (101389139257653 / 50000) := by
  exact
    packedTile65536 2027700480 2027831552 14 6175 45029 31 _ _ (428603 / 20000) (1071509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027831552 :
    ThetaLowerSegment 2027831552 2027962624 (101389139257653 / 50000) (4055822818667 / 2000) := by
  exact
    packedTile65536 2027831552 2027962624 14 6002 45031 31 _ _ (1071511 / 50000) (85721 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2027962624 :
    ThetaLowerSegment 2027962624 2028093696 (4055822818667 / 2000) (20280408482247 / 10000) := by
  exact
    packedTile65536 2027962624 2028093696 14 6040 45032 31 _ _ (535757 / 25000) (2143031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028093696 :
    ThetaLowerSegment 2028093696 2028224768 (20280408482247 / 10000) (40563461041077 / 20000) := by
  exact
    packedTile65536 2028093696 2028224768 14 6169 45034 31 _ _ (428607 / 20000) (1071519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028224768 :
    ThetaLowerSegment 2028224768 2028355840 (40563461041077 / 20000) (50707628191767 / 25000) := by
  exact
    packedTile65536 2028224768 2028355840 14 6163 45035 31 _ _ (2143041 / 100000) (535761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028355840 :
    ThetaLowerSegment 2028355840 2028486912 (50707628191767 / 25000) (50710874909487 / 25000) := by
  exact
    packedTile65536 2028355840 2028486912 14 6060 45037 31 _ _ (267881 / 12500) (2143051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028486912 :
    ThetaLowerSegment 2028486912 2028617984 (50710874909487 / 25000) (101428270060769 / 50000) := by
  exact
    packedTile65536 2028486912 2028617984 14 6085 45038 31 _ _ (1071527 / 50000) (2143057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028617984 :
    ThetaLowerSegment 2028617984 2028749056 (101428270060769 / 50000) (50717376410147 / 25000) := by
  exact
    packedTile65536 2028617984 2028749056 14 6050 45040 31 _ _ (2143061 / 100000) (267883 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028749056 :
    ThetaLowerSegment 2028749056 2028880128 (50717376410147 / 25000) (50720672447193 / 25000) := by
  exact
    packedTile65536 2028749056 2028880128 14 6152 45041 31 _ _ (2143067 / 100000) (214307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2028880128 :
    ThetaLowerSegment 2028880128 2029011200 (50720672447193 / 25000) (50723925632007 / 25000) := by
  exact
    packedTile65536 2028880128 2029011200 14 6072 45043 31 _ _ (2143073 / 100000) (535769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029011200 :
    ThetaLowerSegment 2029011200 2029142272 (50723925632007 / 25000) (50727201329787 / 25000) := by
  exact
    packedTile65536 2029011200 2029142272 14 6114 45044 31 _ _ (53577 / 2500) (2143083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029142272 :
    ThetaLowerSegment 2029142272 2029273344 (50727201329787 / 25000) (101460993720567 / 50000) := by
  exact
    packedTile65536 2029142272 2029273344 14 6151 45046 31 _ _ (1071543 / 50000) (2143089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029273344 :
    ThetaLowerSegment 2029273344 2029404416 (101460993720567 / 50000) (2029349788709 / 1000) := by
  exact
    packedTile65536 2029273344 2029404416 14 6062 45047 31 _ _ (2143093 / 100000) (267887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029404416 :
    ThetaLowerSegment 2029404416 2029535488 (2029349788709 / 1000) (202948143928057 / 100000) := by
  exact
    packedTile65536 2029404416 2029535488 14 6143 45048 31 _ _ (2143099 / 100000) (1071551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029535488 :
    ThetaLowerSegment 2029535488 2029666560 (202948143928057 / 100000)
      (202961369035183 / 100000) := by
  exact
    packedTile65536 2029535488 2029666560 14 6171 45050 31 _ _ (1071553 / 50000) (2143109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029666560 :
    ThetaLowerSegment 2029666560 2029797632 (202961369035183 / 100000)
      (202974435589047 / 100000) := by
  exact
    packedTile65536 2029666560 2029797632 14 6097 45051 31 _ _ (267889 / 12500) (428623 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029797632 :
    ThetaLowerSegment 2029797632 2029928704 (202974435589047 / 100000) (5074689161979 / 2500) := by
  exact
    packedTile65536 2029797632 2029928704 14 6127 45053 31 _ _ (2143119 / 100000) (1071561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2029928704 :
    ThetaLowerSegment 2029928704 2030059776 (5074689161979 / 2500) (10150026833583 / 5000) := by
  exact
    packedTile65536 2029928704 2030059776 14 6052 45054 31 _ _ (3429 / 160) (267891 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030059776 :
    ThetaLowerSegment 2030059776 2030190848 (10150026833583 / 5000) (25376699346867 / 12500) := by
  exact
    packedTile65536 2030059776 2030190848 14 6093 45056 31 _ _ (535783 / 25000) (428627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030190848 :
    ThetaLowerSegment 2030190848 2030321920 (25376699346867 / 12500) (50756668050753 / 25000) := by
  exact
    packedTile65536 2030190848 2030321920 14 6102 45057 31 _ _ (1071569 / 50000) (2143141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030321920 :
    ThetaLowerSegment 2030321920 2030452992 (50756668050753 / 25000)
      (203039773248397 / 100000) := by
  exact
    packedTile65536 2030321920 2030452992 14 6113 45059 31 _ _ (428629 / 20000) (535787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030452992 :
    ThetaLowerSegment 2030452992 2030584064 (203039773248397 / 100000)
      (203052902191423 / 100000) := by
  exact
    packedTile65536 2030452992 2030584064 14 6126 45060 31 _ _ (2143151 / 100000) (1071577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030584064 :
    ThetaLowerSegment 2030584064 2030715136 (203052902191423 / 100000) (6345810192391 / 3125) := by
  exact
    packedTile65536 2030584064 2030715136 14 6077 45062 31 _ _ (2143157 / 100000) (53579 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030715136 :
    ThetaLowerSegment 2030715136 2030846208 (6345810192391 / 3125) (6346221679879 / 3125) := by
  exact
    packedTile65536 2030715136 2030846208 14 6144 45063 31 _ _ (535791 / 25000) (2143167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030846208 :
    ThetaLowerSegment 2030846208 2030977280 (6346221679879 / 3125) (101546266787599 / 50000) := by
  exact
    packedTile65536 2030846208 2030977280 14 6271 45064 31 _ _ (214317 / 10000) (2143173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2030977280 :
    ThetaLowerSegment 2030977280 2031108352 (101546266787599 / 50000) (50776368519481 / 25000) := by
  exact
    packedTile65536 2030977280 2031108352 14 6038 45066 31 _ _ (2143177 / 100000) (107159 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031108352 :
    ThetaLowerSegment 2031108352 2031239424 (50776368519481 / 25000) (50779651875837 / 25000) := by
  exact
    packedTile65536 2031108352 2031239424 14 6128 45067 31 _ _ (2143183 / 100000) (1071593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031239424 :
    ThetaLowerSegment 2031239424 2031370496 (50779651875837 / 25000) (50782843085747 / 25000) := by
  exact
    packedTile65536 2031239424 2031370496 14 5956 45069 31 _ _ (214319 / 10000) (2143193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031370496 :
    ThetaLowerSegment 2031370496 2031501568 (50782843085747 / 25000) (50786143607587 / 25000) := by
  exact
    packedTile65536 2031370496 2031501568 14 6160 45070 31 _ _ (535799 / 25000) (2143199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031501568 :
    ThetaLowerSegment 2031501568 2031632640 (50786143607587 / 25000) (101578847559557 / 50000) := by
  exact
    packedTile65536 2031501568 2031632640 14 6122 45072 31 _ _ (2143203 / 100000) (1071603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031632640 :
    ThetaLowerSegment 2031632640 2031763712 (101578847559557 / 50000) (20317082013103 / 10000) := by
  exact
    packedTile65536 2031632640 2031763712 14 6124 45073 31 _ _ (2143209 / 100000) (535803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031763712 :
    ThetaLowerSegment 2031763712 2031894784 (20317082013103 / 10000) (101591998311499 / 50000) := by
  exact
    packedTile65536 2031763712 2031894784 14 6148 45075 31 _ _ (133951 / 6250) (2143219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2031894784 :
    ThetaLowerSegment 2031894784 2032025856 (101591998311499 / 50000) (50799308826323 / 25000) := by
  exact
    packedTile65536 2031894784 2032025856 14 6177 45076 31 _ _ (1071611 / 50000) (85729 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032025856 :
    ThetaLowerSegment 2032025856 2032156928 (50799308826323 / 25000) (50802550458673 / 25000) := by
  exact
    packedTile65536 2032025856 2032156928 14 6050 45077 31 _ _ (535807 / 25000) (2143231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032156928 :
    ThetaLowerSegment 2032156928 2032288000 (50802550458673 / 25000) (50805838181163 / 25000) := by
  exact
    packedTile65536 2032156928 2032288000 14 6136 45079 31 _ _ (428647 / 20000) (1071619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032288000 :
    ThetaLowerSegment 2032288000 2032419072 (50805838181163 / 25000) (101618258255437 / 50000) := by
  exact
    packedTile65536 2032288000 2032419072 14 6142 45080 31 _ _ (2143241 / 100000) (535811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032419072 :
    ThetaLowerSegment 2032419072 2032550144 (101618258255437 / 50000) (20324976607001 / 10000) := by
  exact
    packedTile65536 2032419072 2032550144 14 6182 45082 31 _ _ (133953 / 6250) (2143251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032550144 :
    ThetaLowerSegment 2032550144 2032681216 (20324976607001 / 10000) (101631394240657 / 50000) := by
  exact
    packedTile65536 2032550144 2032681216 14 6076 45083 31 _ _ (1071627 / 50000) (2143257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032681216 :
    ThetaLowerSegment 2032681216 2032812288 (101631394240657 / 50000) (50818985954333 / 25000) := by
  exact
    packedTile65536 2032681216 2032812288 14 6138 45085 31 _ _ (2143261 / 100000) (66977 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032812288 :
    ThetaLowerSegment 2032812288 2032943360 (50818985954333 / 25000) (2032890263191 / 1000) := by
  exact
    packedTile65536 2032812288 2032943360 14 6104 45086 31 _ _ (2143267 / 100000) (214327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2032943360 :
    ThetaLowerSegment 2032943360 2033074432 (2032890263191 / 1000) (406604200581 / 200) := by
  exact
    packedTile65536 2032943360 2033074432 14 6100 45088 31 _ _ (1071637 / 50000) (2143277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033074432 :
    ThetaLowerSegment 2033074432 2033205504 (406604200581 / 200) (10165758393433 / 5000) := by
  exact
    packedTile65536 2033074432 2033205504 14 6097 45089 31 _ _ (26791 / 1250) (2143283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033205504 :
    ThetaLowerSegment 2033205504 2033336576 (10165758393433 / 5000) (25416024345121 / 12500) := by
  exact
    packedTile65536 2033205504 2033336576 14 6078 45091 31 _ _ (1071643 / 50000) (2143289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033336576 :
    ThetaLowerSegment 2033336576 2033467648 (25416024345121 / 12500)
      (203341343863523 / 100000) := by
  exact
    packedTile65536 2033336576 2033467648 14 6135 45092 31 _ _ (2143293 / 100000) (66978 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033467648 :
    ThetaLowerSegment 2033467648 2033598720 (203341343863523 / 100000) (6354830585464 / 3125) := by
  exact
    packedTile65536 2033467648 2033598720 14 6175 45093 31 _ _ (2143299 / 100000) (1071651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033598720 :
    ThetaLowerSegment 2033598720 2033729792 (6354830585464 / 3125) (20336773220377 / 10000) := by
  exact
    packedTile65536 2033598720 2033729792 14 6137 45095 31 _ _ (1071653 / 50000) (2143309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033729792 :
    ThetaLowerSegment 2033729792 2033860864 (20336773220377 / 10000) (20338077425729 / 10000) := by
  exact
    packedTile65536 2033729792 2033860864 14 6085 45096 31 _ _ (133957 / 6250) (428663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033860864 :
    ThetaLowerSegment 2033860864 2033991936 (20338077425729 / 10000)
      (203393974959011 / 100000) := by
  exact
    packedTile65536 2033860864 2033991936 14 6159 45098 31 _ _ (2143319 / 100000) (1071661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2033991936 :
    ThetaLowerSegment 2033991936 2034123008 (203393974959011 / 100000)
      (203407237854111 / 100000) := by
  exact
    packedTile65536 2033991936 2034123008 14 6188 45099 31 _ _ (85733 / 4000) (66979 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034123008 :
    ThetaLowerSegment 2034123008 2034254080 (203407237854111 / 100000)
      (40684067579859 / 20000) := by
  exact
    packedTile65536 2034123008 2034254080 14 6112 45101 31 _ _ (535833 / 25000) (428667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034254080 :
    ThetaLowerSegment 2034254080 2034385152 (40684067579859 / 20000)
      (203433618021543 / 100000) := by
  exact
    packedTile65536 2034254080 2034385152 14 6196 45102 31 _ _ (1071669 / 50000) (2143341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034385152 :
    ThetaLowerSegment 2034385152 2034516224 (203433618021543 / 100000)
      (203446844597367 / 100000) := by
  exact
    packedTile65536 2034385152 2034516224 14 6171 45104 31 _ _ (133959 / 6250) (2143347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034516224 :
    ThetaLowerSegment 2034516224 2034647296 (203446844597367 / 100000)
      (101730020604737 / 50000) := by
  exact
    packedTile65536 2034516224 2034647296 14 6157 45105 31 _ _ (2143351 / 100000) (1071677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034647296 :
    ThetaLowerSegment 2034647296 2034778368 (101730020604737 / 50000)
      (203473066389963 / 100000) := by
  exact
    packedTile65536 2034647296 2034778368 14 6077 45107 31 _ _ (2143357 / 100000) (13396 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034778368 :
    ThetaLowerSegment 2034778368 2034909440 (203473066389963 / 100000)
      (40697235898183 / 20000) := by
  exact
    packedTile65536 2034778368 2034909440 14 6118 45108 31 _ _ (535841 / 25000) (2143367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2034909440 :
    ThetaLowerSegment 2034909440 2035040512 (40697235898183 / 20000) (8139972133817 / 4000) := by
  exact
    packedTile65536 2034909440 2035040512 14 6123 45109 31 _ _ (214337 / 10000) (2143373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035040512 :
    ThetaLowerSegment 2035040512 2035171584 (8139972133817 / 4000) (203512300783553 / 100000) := by
  exact
    packedTile65536 2035040512 2035171584 14 6064 45111 31 _ _ (2143377 / 100000) (107169 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035171584 :
    ThetaLowerSegment 2035171584 2035302656 (203512300783553 / 100000)
      (203525371133087 / 100000) := by
  exact
    packedTile65536 2035171584 2035302656 14 6098 45112 31 _ _ (2143383 / 100000) (1071693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035302656 :
    ThetaLowerSegment 2035302656 2035433728 (203525371133087 / 100000)
      (203538381510387 / 100000) := by
  exact
    packedTile65536 2035302656 2035433728 14 6070 45114 31 _ _ (214339 / 10000) (2143393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035433728 :
    ThetaLowerSegment 2035433728 2035564800 (203538381510387 / 100000)
      (203551447652403 / 100000) := by
  exact
    packedTile65536 2035433728 2035564800 14 6096 45115 31 _ _ (535849 / 25000) (2143399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035564800 :
    ThetaLowerSegment 2035564800 2035695872 (203551447652403 / 100000)
      (203564601710477 / 100000) := by
  exact
    packedTile65536 2035564800 2035695872 14 6137 45117 31 _ _ (1071701 / 50000) (428681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035695872 :
    ThetaLowerSegment 2035695872 2035826944 (203564601710477 / 100000)
      (203577753668101 / 100000) := by
  exact
    packedTile65536 2035695872 2035826944 14 6136 45118 31 _ _ (2143409 / 100000) (535853 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035826944 :
    ThetaLowerSegment 2035826944 2035958016 (203577753668101 / 100000)
      (203590669886891 / 100000) := by
  exact
    packedTile65536 2035826944 2035958016 14 6026 45120 31 _ _ (428683 / 20000) (1071709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2035958016 :
    ThetaLowerSegment 2035958016 2036089088 (203590669886891 / 100000)
      (203603860505879 / 100000) := by
  exact
    packedTile65536 2035958016 2036089088 14 6154 45121 31 _ _ (1071711 / 50000) (85737 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036089088 :
    ThetaLowerSegment 2036089088 2036220160 (203603860505879 / 100000)
      (203616892548119 / 100000) := by
  exact
    packedTile65536 2036089088 2036220160 14 6080 45123 31 _ _ (535857 / 25000) (2143431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036220160 :
    ThetaLowerSegment 2036220160 2036351232 (203616892548119 / 100000)
      (203629984649099 / 100000) := by
  exact
    packedTile65536 2036220160 2036351232 14 6108 45124 31 _ _ (428687 / 20000) (1071719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036351232 :
    ThetaLowerSegment 2036351232 2036482304 (203629984649099 / 100000)
      (40728614499969 / 20000) := by
  exact
    packedTile65536 2036351232 2036482304 14 6106 45125 31 _ _ (2143441 / 100000) (535861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036482304 :
    ThetaLowerSegment 2036482304 2036613376 (40728614499969 / 20000) (40731238079097 / 20000) := by
  exact
    packedTile65536 2036482304 2036613376 14 6120 45127 31 _ _ (2143447 / 100000) (42869 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036613376 :
    ThetaLowerSegment 2036613376 2036744448 (40731238079097 / 20000)
      (203669295473241 / 100000) := by
  exact
    packedTile65536 2036613376 2036744448 14 6114 45128 31 _ _ (1071727 / 50000) (2143457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036744448 :
    ThetaLowerSegment 2036744448 2036875520 (203669295473241 / 100000)
      (203682366292321 / 100000) := by
  exact
    packedTile65536 2036744448 2036875520 14 6098 45130 31 _ _ (107173 / 5000) (2143463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2036875520 :
    ThetaLowerSegment 2036875520 2037006592 (203682366292321 / 100000)
      (40739102006393 / 20000) := by
  exact
    packedTile65536 2036875520 2037006592 14 6132 45131 31 _ _ (2143467 / 100000) (214347 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037006592 :
    ThetaLowerSegment 2037006592 2037137664 (40739102006393 / 20000)
      (203708589504211 / 100000) := by
  exact
    packedTile65536 2037006592 2037137664 14 6102 45133 31 _ _ (2143473 / 100000) (535869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037137664 :
    ThetaLowerSegment 2037137664 2037268736 (203708589504211 / 100000)
      (203721570419091 / 100000) := by
  exact
    packedTile65536 2037137664 2037268736 14 6056 45134 31 _ _ (53587 / 2500) (2143483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037268736 :
    ThetaLowerSegment 2037268736 2037399808 (203721570419091 / 100000)
      (203734609244429 / 100000) := by
  exact
    packedTile65536 2037268736 2037399808 14 6083 45136 31 _ _ (1071743 / 50000) (2143489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037399808 :
    ThetaLowerSegment 2037399808 2037530880 (203734609244429 / 100000)
      (203747714560631 / 100000) := by
  exact
    packedTile65536 2037399808 2037530880 14 6114 45137 31 _ _ (2143493 / 100000) (267937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037530880 :
    ThetaLowerSegment 2037530880 2037661952 (203747714560631 / 100000)
      (203760828487513 / 100000) := by
  exact
    packedTile65536 2037530880 2037661952 14 6118 45139 31 _ _ (2143499 / 100000) (1071751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037661952 :
    ThetaLowerSegment 2037661952 2037793024 (203760828487513 / 100000)
      (50943492579167 / 25000) := by
  exact
    packedTile65536 2037661952 2037793024 14 6131 45140 31 _ _ (428701 / 20000) (535877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037793024 :
    ThetaLowerSegment 2037793024 2037924096 (50943492579167 / 25000) (50946756076187 / 25000) := by
  exact
    packedTile65536 2037793024 2037924096 14 6090 45141 31 _ _ (267939 / 12500) (428703 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2037924096 :
    ThetaLowerSegment 2037924096 2038055168 (50946756076187 / 25000) (12737507574983 / 6250) := by
  exact
    packedTile65536 2037924096 2038055168 14 6110 45143 31 _ _ (1071759 / 50000) (2143521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038055168 :
    ThetaLowerSegment 2038055168 2038186240 (12737507574983 / 6250) (101906647652189 / 50000) := by
  exact
    packedTile65536 2038055168 2038186240 14 6146 45144 31 _ _ (85741 / 4000) (267941 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038186240 :
    ThetaLowerSegment 2038186240 2038317312 (101906647652189 / 50000)
      (101913189708801 / 50000) := by
  exact
    packedTile65536 2038186240 2038317312 14 6104 45146 31 _ _ (2143531 / 100000) (1071767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038317312 :
    ThetaLowerSegment 2038317312 2038448384 (101913189708801 / 50000) (25479927319907 / 12500) := by
  exact
    packedTile65536 2038317312 2038448384 14 6083 45147 31 _ _ (1071769 / 50000) (2143541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038448384 :
    ThetaLowerSegment 2038448384 2038579456 (25479927319907 / 12500) (25481561236321 / 12500) := by
  exact
    packedTile65536 2038448384 2038579456 14 6098 45149 31 _ _ (267943 / 12500) (2143547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038579456 :
    ThetaLowerSegment 2038579456 2038710528 (25481561236321 / 12500) (101932807423609 / 50000) := by
  exact
    packedTile65536 2038579456 2038710528 14 6123 45150 31 _ _ (42871 / 2000) (2143553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038710528 :
    ThetaLowerSegment 2038710528 2038841600 (101932807423609 / 50000)
      (203878804153439 / 100000) := by
  exact
    packedTile65536 2038710528 2038841600 14 6153 45152 31 _ _ (2143557 / 100000) (53589 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038841600 :
    ThetaLowerSegment 2038841600 2038972672 (203878804153439 / 100000)
      (101945992461163 / 50000) := by
  exact
    packedTile65536 2038841600 2038972672 14 6149 45153 31 _ _ (2143563 / 100000) (1071783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2038972672 :
    ThetaLowerSegment 2038972672 2039103744 (101945992461163 / 50000)
      (101952532493233 / 50000) := by
  exact
    packedTile65536 2038972672 2039103744 14 6102 45154 31 _ _ (214357 / 10000) (2143573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039103744 :
    ThetaLowerSegment 2039103744 2039234816 (101952532493233 / 50000)
      (101959142209829 / 50000) := by
  exact
    packedTile65536 2039103744 2039234816 14 6167 45156 31 _ _ (267947 / 12500) (2143579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039234816 :
    ThetaLowerSegment 2039234816 2039365888 (101959142209829 / 50000) (4078628234439 / 2000) := by
  exact
    packedTile65536 2039234816 2039365888 14 6124 45157 31 _ _ (2143583 / 100000) (1071793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039365888 :
    ThetaLowerSegment 2039365888 2039496960 (4078628234439 / 2000) (203944609799423 / 100000) := by
  exact
    packedTile65536 2039365888 2039496960 14 6157 45159 31 _ _ (2143589 / 100000) (267949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039496960 :
    ThetaLowerSegment 2039496960 2039628032 (203944609799423 / 100000)
      (203957578549173 / 100000) := by
  exact
    packedTile65536 2039496960 2039628032 14 6050 45160 31 _ _ (428719 / 20000) (1071799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039628032 :
    ThetaLowerSegment 2039628032 2039759104 (203957578549173 / 100000)
      (203970671670189 / 100000) := by
  exact
    packedTile65536 2039628032 2039759104 14 6108 45162 31 _ _ (1071801 / 50000) (428721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039759104 :
    ThetaLowerSegment 2039759104 2039890176 (203970671670189 / 100000)
      (203983953465357 / 100000) := by
  exact
    packedTile65536 2039759104 2039890176 14 6196 45163 31 _ _ (267951 / 12500) (2143611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2039890176 :
    ThetaLowerSegment 2039890176 2040021248 (203983953465357 / 100000)
      (203996952346717 / 100000) := by
  exact
    packedTile65536 2039890176 2040021248 14 6064 45165 31 _ _ (428723 / 20000) (1071809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040021248 :
    ThetaLowerSegment 2040021248 2040152320 (203996952346717 / 100000) (6375312517742 / 3125) := by
  exact
    packedTile65536 2040021248 2040152320 14 6087 45166 31 _ _ (2143621 / 100000) (267953 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040152320 :
    ThetaLowerSegment 2040152320 2040283392 (6375312517742 / 3125) (51005752561519 / 25000) := by
  exact
    packedTile65536 2040152320 2040283392 14 6069 45168 31 _ _ (535907 / 25000) (2143631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040283392 :
    ThetaLowerSegment 2040283392 2040414464 (51005752561519 / 25000) (51009017316101 / 25000) := by
  exact
    packedTile65536 2040283392 2040414464 14 6092 45169 31 _ _ (1071817 / 50000) (2143637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040414464 :
    ThetaLowerSegment 2040414464 2040545536 (51009017316101 / 25000) (51012324416711 / 25000) := by
  exact
    packedTile65536 2040414464 2040545536 14 6171 45170 31 _ _ (53591 / 2500) (2143643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040545536 :
    ThetaLowerSegment 2040545536 2040676608 (51012324416711 / 25000)
      (204062354620721 / 100000) := by
  exact
    packedTile65536 2040545536 2040676608 14 6091 45172 31 _ _ (2143647 / 100000) (42873 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040676608 :
    ThetaLowerSegment 2040676608 2040807680 (204062354620721 / 100000)
      (204075456627857 / 100000) := by
  exact
    packedTile65536 2040676608 2040807680 14 6112 45173 31 _ _ (2143653 / 100000) (267957 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040807680 :
    ThetaLowerSegment 2040807680 2040938752 (204075456627857 / 100000)
      (204088412908897 / 100000) := by
  exact
    packedTile65536 2040807680 2040938752 14 6044 45175 31 _ _ (107183 / 5000) (2143663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2040938752 :
    ThetaLowerSegment 2040938752 2041069824 (204088412908897 / 100000)
      (204101575018137 / 100000) := by
  exact
    packedTile65536 2040938752 2041069824 14 6140 45176 31 _ _ (1071833 / 50000) (2143669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041069824 :
    ThetaLowerSegment 2041069824 2041200896 (204101575018137 / 100000)
      (204114604256553 / 100000) := by
  exact
    packedTile65536 2041069824 2041200896 14 6078 45178 31 _ _ (267959 / 12500) (85747 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041200896 :
    ThetaLowerSegment 2041200896 2041331968 (204114604256553 / 100000)
      (102063860714177 / 50000) := by
  exact
    packedTile65536 2041200896 2041331968 14 6119 45179 31 _ _ (2143679 / 100000) (1071841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041331968 :
    ThetaLowerSegment 2041331968 2041463040 (102063860714177 / 50000)
      (102070390378687 / 50000) := by
  exact
    packedTile65536 2041331968 2041463040 14 6092 45181 31 _ _ (428737 / 20000) (267961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041463040 :
    ThetaLowerSegment 2041463040 2041594112 (102070390378687 / 50000)
      (102076858969297 / 50000) := by
  exact
    packedTile65536 2041463040 2041594112 14 6035 45182 31 _ _ (535923 / 25000) (428739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041594112 :
    ThetaLowerSegment 2041594112 2041725184 (102076858969297 / 50000) (20416692740567 / 10000) := by
  exact
    packedTile65536 2041594112 2041725184 14 6162 45184 31 _ _ (1071849 / 50000) (2143701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041725184 :
    ThetaLowerSegment 2041725184 2041856256 (20416692740567 / 10000) (40836008089831 / 20000) := by
  exact
    packedTile65536 2041725184 2041856256 14 6117 45185 31 _ _ (428741 / 20000) (535927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041856256 :
    ThetaLowerSegment 2041856256 2041987328 (40836008089831 / 20000)
      (204192949876797 / 100000) := by
  exact
    packedTile65536 2041856256 2041987328 14 6022 45186 31 _ _ (2143711 / 100000) (1071857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2041987328 :
    ThetaLowerSegment 2041987328 2042118400 (204192949876797 / 100000) (2042059386581 / 1000) := by
  exact
    packedTile65536 2041987328 2042118400 14 6059 45188 31 _ _ (2143717 / 100000) (53593 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042118400 :
    ThetaLowerSegment 2042118400 2042249472 (2042059386581 / 1000) (12763688594889 / 6250) := by
  exact
    packedTile65536 2042118400 2042249472 14 6101 45189 31 _ _ (535931 / 25000) (2143727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042249472 :
    ThetaLowerSegment 2042249472 2042380544 (12763688594889 / 6250) (51058028927131 / 25000) := by
  exact
    packedTile65536 2042249472 2042380544 14 6110 45191 31 _ _ (214373 / 10000) (2143733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042380544 :
    ThetaLowerSegment 2042380544 2042511616 (51058028927131 / 25000) (8169813959881 / 4000) := by
  exact
    packedTile65536 2042380544 2042511616 14 6173 45192 31 _ _ (2143737 / 100000) (107187 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042511616 :
    ThetaLowerSegment 2042511616 2042642688 (8169813959881 / 4000) (204258400104409 / 100000) := by
  exact
    packedTile65536 2042511616 2042642688 14 6088 45194 31 _ _ (2143743 / 100000) (1071873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042642688 :
    ThetaLowerSegment 2042642688 2042773760 (204258400104409 / 100000)
      (204271436248159 / 100000) := by
  exact
    packedTile65536 2042642688 2042773760 14 6081 45195 31 _ _ (343 / 16) (2143753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042773760 :
    ThetaLowerSegment 2042773760 2042904832 (204271436248159 / 100000)
      (40856978092163 / 20000) := by
  exact
    packedTile65536 2042773760 2042904832 14 6276 45197 31 _ _ (535939 / 25000) (2143759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2042904832 :
    ThetaLowerSegment 2042904832 2043035904 (40856978092163 / 20000)
      (204298036009399 / 100000) := by
  exact
    packedTile65536 2042904832 2043035904 14 6132 45198 31 _ _ (1071881 / 50000) (428753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043035904 :
    ThetaLowerSegment 2043035904 2043166976 (204298036009399 / 100000)
      (51077787361093 / 25000) := by
  exact
    packedTile65536 2043035904 2043166976 14 6117 45199 31 _ _ (2143769 / 100000) (535943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043166976 :
    ThetaLowerSegment 2043166976 2043298048 (51077787361093 / 25000) (102162162542761 / 50000) := by
  exact
    packedTile65536 2043166976 2043298048 14 6146 45201 31 _ _ (85751 / 4000) (1071889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043298048 :
    ThetaLowerSegment 2043298048 2043429120 (102162162542761 / 50000) (51084369297023 / 25000) := by
  exact
    packedTile65536 2043298048 2043429120 14 6135 45202 31 _ _ (1071891 / 50000) (428757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043429120 :
    ThetaLowerSegment 2043429120 2043560192 (51084369297023 / 25000) (25543843136503 / 12500) := by
  exact
    packedTile65536 2043429120 2043560192 14 6189 45204 31 _ _ (535947 / 25000) (2143791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043560192 :
    ThetaLowerSegment 2043560192 2043691264 (25543843136503 / 12500) (2043637236209 / 1000) := by
  exact
    packedTile65536 2043560192 2043691264 14 6054 45205 31 _ _ (1071897 / 50000) (2143797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043691264 :
    ThetaLowerSegment 2043691264 2043822336 (2043637236209 / 1000) (204376691473149 / 100000) := by
  exact
    packedTile65536 2043691264 2043822336 14 6049 45207 31 _ _ (2143801 / 100000) (535951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043822336 :
    ThetaLowerSegment 2043822336 2043953408 (204376691473149 / 100000)
      (204389772983463 / 100000) := by
  exact
    packedTile65536 2043822336 2043953408 14 6102 45208 31 _ _ (2143807 / 100000) (214381 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2043953408 :
    ThetaLowerSegment 2043953408 2044084480 (204389772983463 / 100000)
      (204402972446261 / 100000) := by
  exact
    packedTile65536 2043953408 2044084480 14 6157 45210 31 _ _ (1071907 / 50000) (2143817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044084480 :
    ThetaLowerSegment 2044084480 2044215552 (204402972446261 / 100000)
      (204416186952741 / 100000) := by
  exact
    packedTile65536 2044084480 2044215552 14 6164 45211 31 _ _ (107191 / 5000) (2143823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044215552 :
    ThetaLowerSegment 2044215552 2044346624 (204416186952741 / 100000)
      (204429287873427 / 100000) := by
  exact
    packedTile65536 2044215552 2044346624 14 6111 45213 31 _ _ (1071913 / 50000) (2143829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044346624 :
    ThetaLowerSegment 2044346624 2044477696 (204429287873427 / 100000) (4088848634271 / 2000) := by
  exact
    packedTile65536 2044346624 2044477696 14 6131 45214 31 _ _ (2143833 / 100000) (535959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044477696 :
    ThetaLowerSegment 2044477696 2044608768 (4088848634271 / 2000) (102227793154827 / 50000) := by
  exact
    packedTile65536 2044477696 2044608768 14 6136 45215 31 _ _ (2143839 / 100000) (1071921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044608768 :
    ThetaLowerSegment 2044608768 2044739840 (102227793154827 / 50000) (12779290815689 / 6250) := by
  exact
    packedTile65536 2044608768 2044739840 14 6095 45217 31 _ _ (1071923 / 50000) (2143849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044739840 :
    ThetaLowerSegment 2044739840 2044870912 (12779290815689 / 6250) (6390053543669 / 3125) := by
  exact
    packedTile65536 2044739840 2044870912 14 6092 45218 31 _ _ (535963 / 25000) (428771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2044870912 :
    ThetaLowerSegment 2044870912 2045001984 (6390053543669 / 3125) (102247380461641 / 50000) := by
  exact
    packedTile65536 2044870912 2045001984 14 6086 45220 31 _ _ (2143859 / 100000) (1071931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045001984 :
    ThetaLowerSegment 2045001984 2045133056 (102247380461641 / 50000) (25563497499359 / 12500) := by
  exact
    packedTile65536 2045001984 2045133056 14 6166 45221 31 _ _ (428773 / 20000) (535967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045133056 :
    ThetaLowerSegment 2045133056 2045264128 (25563497499359 / 12500)
      (204521081190553 / 100000) := by
  exact
    packedTile65536 2045133056 2045264128 14 6111 45223 31 _ _ (2143871 / 100000) (1071937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045264128 :
    ThetaLowerSegment 2045264128 2045395200 (204521081190553 / 100000)
      (204534152414719 / 100000) := by
  exact
    packedTile65536 2045264128 2045395200 14 6097 45224 31 _ _ (1071939 / 50000) (2143881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045395200 :
    ThetaLowerSegment 2045395200 2045526272 (204534152414719 / 100000)
      (40909479894791 / 20000) := by
  exact
    packedTile65536 2045395200 2045526272 14 6179 45226 31 _ _ (535971 / 25000) (2143887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045526272 :
    ThetaLowerSegment 2045526272 2045657344 (40909479894791 / 20000)
      (204560610130297 / 100000) := by
  exact
    packedTile65536 2045526272 2045657344 14 6162 45227 31 _ _ (2143891 / 100000) (1071947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045657344 :
    ThetaLowerSegment 2045657344 2045788416 (204560610130297 / 100000)
      (102286862174123 / 50000) := by
  exact
    packedTile65536 2045657344 2045788416 14 6117 45228 31 _ _ (2143897 / 100000) (21439 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045788416 :
    ThetaLowerSegment 2045788416 2045919488 (102286862174123 / 50000)
      (102293413941691 / 50000) := by
  exact
    packedTile65536 2045788416 2045919488 14 6112 45230 31 _ _ (2143903 / 100000) (1071953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2045919488 :
    ThetaLowerSegment 2045919488 2046050560 (102293413941691 / 50000) (25574975085349 / 12500) := by
  exact
    packedTile65536 2045919488 2046050560 14 6051 45231 31 _ _ (214391 / 10000) (2143913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046050560 :
    ThetaLowerSegment 2046050560 2046181632 (25574975085349 / 12500) (51153234114031 / 25000) := by
  exact
    packedTile65536 2046050560 2046181632 14 6127 45233 31 _ _ (535979 / 25000) (2143919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046181632 :
    ThetaLowerSegment 2046181632 2046312704 (51153234114031 / 25000) (102313017912827 / 50000) := by
  exact
    packedTile65536 2046181632 2046312704 14 6110 45234 31 _ _ (2143923 / 100000) (1071963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046312704 :
    ThetaLowerSegment 2046312704 2046443776 (102313017912827 / 50000) (51159758080813 / 25000) := by
  exact
    packedTile65536 2046312704 2046443776 14 6062 45236 31 _ _ (2143929 / 100000) (535983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046443776 :
    ThetaLowerSegment 2046443776 2046574848 (51159758080813 / 25000)
      (204652181076607 / 100000) := by
  exact
    packedTile65536 2046443776 2046574848 14 6133 45237 31 _ _ (428787 / 20000) (1071969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046574848 :
    ThetaLowerSegment 2046574848 2046705920 (204652181076607 / 100000)
      (40933077123077 / 20000) := by
  exact
    packedTile65536 2046574848 2046705920 14 6159 45239 31 _ _ (1071971 / 50000) (428789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046705920 :
    ThetaLowerSegment 2046705920 2046836992 (40933077123077 / 20000)
      (204678523728729 / 100000) := by
  exact
    packedTile65536 2046705920 2046836992 14 6128 45240 31 _ _ (535987 / 25000) (2143951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046836992 :
    ThetaLowerSegment 2046836992 2046968064 (204678523728729 / 100000)
      (204691507520209 / 100000) := by
  exact
    packedTile65536 2046836992 2046968064 14 6056 45241 31 _ _ (428791 / 20000) (1071979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2046968064 :
    ThetaLowerSegment 2046968064 2047099136 (204691507520209 / 100000)
      (204704594258153 / 100000) := by
  exact
    packedTile65536 2046968064 2047099136 14 6104 45243 31 _ _ (2143961 / 100000) (535991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047099136 :
    ThetaLowerSegment 2047099136 2047230208 (204704594258153 / 100000) (8188712558347 / 4000) := by
  exact
    packedTile65536 2047099136 2047230208 14 6166 45244 31 _ _ (2143967 / 100000) (214397 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047230208 :
    ThetaLowerSegment 2047230208 2047361280 (8188712558347 / 4000) (204730926503659 / 100000) := by
  exact
    packedTile65536 2047230208 2047361280 14 6116 45246 31 _ _ (1071987 / 50000) (2143977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047361280 :
    ThetaLowerSegment 2047361280 2047492352 (204730926503659 / 100000)
      (204743970477979 / 100000) := by
  exact
    packedTile65536 2047361280 2047492352 14 6084 45247 31 _ _ (107199 / 5000) (2143983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047492352 :
    ThetaLowerSegment 2047492352 2047623424 (204743970477979 / 100000)
      (204757010206913 / 100000) := by
  exact
    packedTile65536 2047492352 2047623424 14 6082 45249 31 _ _ (2143987 / 100000) (214399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047623424 :
    ThetaLowerSegment 2047623424 2047754496 (204757010206913 / 100000)
      (51192551620957 / 25000) := by
  exact
    packedTile65536 2047623424 2047754496 14 6155 45250 31 _ _ (2143993 / 100000) (535999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047754496 :
    ThetaLowerSegment 2047754496 2047885568 (51192551620957 / 25000)
      (204783209837763 / 100000) := by
  exact
    packedTile65536 2047754496 2047885568 14 6065 45252 31 _ _ (2143999 / 100000) (1072001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2047885568 :
    ThetaLowerSegment 2047885568 2048016640 (204783209837763 / 100000)
      (204796155345991 / 100000) := by
  exact
    packedTile65536 2047885568 2048016640 14 6038 45253 31 _ _ (1072003 / 50000) (2144009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048016640 :
    ThetaLowerSegment 2048016640 2048147712 (204796155345991 / 100000)
      (204809240251227 / 100000) := by
  exact
    packedTile65536 2048016640 2048147712 14 6103 45255 31 _ _ (536003 / 25000) (428803 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048147712 :
    ThetaLowerSegment 2048147712 2048278784 (204809240251227 / 100000)
      (51205600595967 / 25000) := by
  exact
    packedTile65536 2048147712 2048278784 14 6139 45256 31 _ _ (2144019 / 100000) (1072011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048278784 :
    ThetaLowerSegment 2048278784 2048409856 (51205600595967 / 25000) (6401109851274 / 3125) := by
  exact
    packedTile65536 2048278784 2048409856 14 6116 45257 31 _ _ (85761 / 4000) (536007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048409856 :
    ThetaLowerSegment 2048409856 2048540928 (6401109851274 / 3125) (204848656006767 / 100000) := by
  exact
    packedTile65536 2048409856 2048540928 14 6129 45259 31 _ _ (2144031 / 100000) (1072017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048540928 :
    ThetaLowerSegment 2048540928 2048672000 (204848656006767 / 100000)
      (40972366652863 / 20000) := by
  exact
    packedTile65536 2048540928 2048672000 14 6146 45260 31 _ _ (1072019 / 50000) (2144041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048672000 :
    ThetaLowerSegment 2048672000 2048803072 (40972366652863 / 20000) (40974965234191 / 20000) := by
  exact
    packedTile65536 2048672000 2048803072 14 6060 45262 31 _ _ (536011 / 25000) (2144047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048803072 :
    ThetaLowerSegment 2048803072 2048934144 (40974965234191 / 20000) (102444073579909 / 50000) := by
  exact
    packedTile65536 2048803072 2048934144 14 6213 45263 31 _ _ (2144051 / 100000) (1072027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2048934144 :
    ThetaLowerSegment 2048934144 2049065216 (102444073579909 / 50000)
      (204901133713067 / 100000) := by
  exact
    packedTile65536 2048934144 2049065216 14 6057 45265 31 _ _ (2144057 / 100000) (107203 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049065216 :
    ThetaLowerSegment 2049065216 2049196288 (204901133713067 / 100000)
      (51228529003633 / 25000) := by
  exact
    packedTile65536 2049065216 2049196288 14 6055 45266 31 _ _ (2144063 / 100000) (1072033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049196288 :
    ThetaLowerSegment 2049196288 2049327360 (51228529003633 / 25000) (102463645662341 / 50000) := by
  exact
    packedTile65536 2049196288 2049327360 14 6145 45268 31 _ _ (214407 / 10000) (2144073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049327360 :
    ThetaLowerSegment 2049327360 2049458432 (102463645662341 / 50000)
      (102470281577561 / 50000) := by
  exact
    packedTile65536 2049327360 2049458432 14 6190 45269 31 _ _ (536019 / 25000) (2144079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049458432 :
    ThetaLowerSegment 2049458432 2049589504 (102470281577561 / 50000)
      (102476868200537 / 50000) := by
  exact
    packedTile65536 2049458432 2049589504 14 6144 45270 31 _ _ (2144083 / 100000) (1072043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049589504 :
    ThetaLowerSegment 2049589504 2049720576 (102476868200537 / 50000) (12810438019499 / 6250) := by
  exact
    packedTile65536 2049589504 2049720576 14 6190 45272 31 _ _ (2144089 / 100000) (536023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049720576 :
    ThetaLowerSegment 2049720576 2049851648 (12810438019499 / 6250) (204980132317479 / 100000) := by
  exact
    packedTile65536 2049720576 2049851648 14 6121 45273 31 _ _ (428819 / 20000) (1072049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049851648 :
    ThetaLowerSegment 2049851648 2049982720 (204980132317479 / 100000) (8199728282059 / 4000) := by
  exact
    packedTile65536 2049851648 2049982720 14 6098 45275 31 _ _ (1072051 / 50000) (428821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2049982720 :
    ThetaLowerSegment 2049982720 2050113792 (8199728282059 / 4000) (205006313983679 / 100000) := by
  exact
    packedTile65536 2049982720 2050113792 14 6113 45276 31 _ _ (536027 / 25000) (2144111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050113792 :
    ThetaLowerSegment 2050113792 2050244864 (205006313983679 / 100000)
      (51254875608761 / 25000) := by
  exact
    packedTile65536 2050113792 2050244864 14 6151 45278 31 _ _ (428823 / 20000) (1072059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050244864 :
    ThetaLowerSegment 2050244864 2050375936 (51254875608761 / 25000) (10251637226317 / 5000) := by
  exact
    packedTile65536 2050244864 2050375936 14 6176 45279 31 _ _ (2144121 / 100000) (536031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050375936 :
    ThetaLowerSegment 2050375936 2050507008 (10251637226317 / 5000) (102522875400361 / 50000) := by
  exact
    packedTile65536 2050375936 2050507008 14 6066 45281 31 _ _ (2144127 / 100000) (214413 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050507008 :
    ThetaLowerSegment 2050507008 2050638080 (102522875400361 / 50000) (51264779869053 / 25000) := by
  exact
    packedTile65536 2050507008 2050638080 14 6235 45282 31 _ _ (1072067 / 50000) (2144137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050638080 :
    ThetaLowerSegment 2050638080 2050769152 (51264779869053 / 25000) (51268068979813 / 25000) := by
  exact
    packedTile65536 2050638080 2050769152 14 6136 45283 31 _ _ (107207 / 5000) (2144143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050769152 :
    ThetaLowerSegment 2050769152 2050900224 (51268068979813 / 25000)
      (205085434549391 / 100000) := by
  exact
    packedTile65536 2050769152 2050900224 14 6137 45285 31 _ _ (2144147 / 100000) (42883 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2050900224 :
    ThetaLowerSegment 2050900224 2051031296 (205085434549391 / 100000)
      (51274654736547 / 25000) := by
  exact
    packedTile65536 2050900224 2051031296 14 6149 45286 31 _ _ (2144153 / 100000) (536039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051031296 :
    ThetaLowerSegment 2051031296 2051162368 (51274654736547 / 25000) (8204463043961 / 4000) := by
  exact
    packedTile65536 2051031296 2051162368 14 6043 45288 31 _ _ (2144159 / 100000) (1072081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051162368 :
    ThetaLowerSegment 2051162368 2051293440 (8204463043961 / 4000) (205124479690013 / 100000) := by
  exact
    packedTile65536 2051162368 2051293440 14 6018 45289 31 _ _ (1072083 / 50000) (2144169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051293440 :
    ThetaLowerSegment 2051293440 2051424512 (205124479690013 / 100000)
      (205137578436761 / 100000) := by
  exact
    packedTile65536 2051293440 2051424512 14 6109 45291 31 _ _ (536043 / 25000) (85767 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051424512 :
    ThetaLowerSegment 2051424512 2051555584 (205137578436761 / 100000)
      (25643836797463 / 12500) := by
  exact
    packedTile65536 2051424512 2051555584 14 6117 45292 31 _ _ (2144179 / 100000) (1072091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051555584 :
    ThetaLowerSegment 2051555584 2051686656 (25643836797463 / 12500)
      (205163720303579 / 100000) := by
  exact
    packedTile65536 2051555584 2051686656 14 6075 45294 31 _ _ (428837 / 20000) (536047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051686656 :
    ThetaLowerSegment 2051686656 2051817728 (205163720303579 / 100000) (12823553074067 / 6250) := by
  exact
    packedTile65536 2051686656 2051817728 14 6123 45295 31 _ _ (2144191 / 100000) (1072097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051817728 :
    ThetaLowerSegment 2051817728 2051948800 (12823553074067 / 6250) (102594978333723 / 50000) := by
  exact
    packedTile65536 2051817728 2051948800 14 6113 45296 31 _ _ (1072099 / 50000) (2144201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2051948800 :
    ThetaLowerSegment 2051948800 2052079872 (102594978333723 / 50000) (20520310278217 / 10000) := by
  exact
    packedTile65536 2051948800 2052079872 14 6131 45298 31 _ _ (536051 / 25000) (2144207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052079872 :
    ThetaLowerSegment 2052079872 2052210944 (20520310278217 / 10000) (20521621248211 / 10000) := by
  exact
    packedTile65536 2052079872 2052210944 14 6114 45299 31 _ _ (214421 / 10000) (2144213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052210944 :
    ThetaLowerSegment 2052210944 2052342016 (20521621248211 / 10000) (102614749025321 / 50000) := by
  exact
    packedTile65536 2052210944 2052342016 14 6196 45301 31 _ _ (2144217 / 100000) (107211 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052342016 :
    ThetaLowerSegment 2052342016 2052473088 (102614749025321 / 50000)
      (205242648570301 / 100000) := by
  exact
    packedTile65536 2052342016 2052473088 14 6133 45302 31 _ _ (2144223 / 100000) (1072113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052473088 :
    ThetaLowerSegment 2052473088 2052604160 (205242648570301 / 100000)
      (205255732661761 / 100000) := by
  exact
    packedTile65536 2052473088 2052604160 14 6102 45304 31 _ _ (214423 / 10000) (2144233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052604160 :
    ThetaLowerSegment 2052604160 2052735232 (205255732661761 / 100000)
      (205268731020393 / 100000) := by
  exact
    packedTile65536 2052604160 2052735232 14 6062 45305 31 _ _ (536059 / 25000) (2144239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052735232 :
    ThetaLowerSegment 2052735232 2052866304 (205268731020393 / 100000)
      (41056354031199 / 20000) := by
  exact
    packedTile65536 2052735232 2052866304 14 6081 45307 31 _ _ (1072121 / 50000) (428849 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052866304 :
    ThetaLowerSegment 2052866304 2052997376 (41056354031199 / 20000)
      (205294854363393 / 100000) := by
  exact
    packedTile65536 2052866304 2052997376 14 6102 45308 31 _ _ (2144249 / 100000) (536063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2052997376 :
    ThetaLowerSegment 2052997376 2053128448 (205294854363393 / 100000)
      (205307869991243 / 100000) := by
  exact
    packedTile65536 2052997376 2053128448 14 6070 45310 31 _ _ (428851 / 20000) (1072129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053128448 :
    ThetaLowerSegment 2053128448 2053259520 (205307869991243 / 100000)
      (205320707687837 / 100000) := by
  exact
    packedTile65536 2053128448 2053259520 14 5987 45311 31 _ _ (1072131 / 50000) (428853 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053259520 :
    ThetaLowerSegment 2053259520 2053390592 (205320707687837 / 100000)
      (205333599027053 / 100000) := by
  exact
    packedTile65536 2053259520 2053390592 14 6012 45312 31 _ _ (536067 / 25000) (2144271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053390592 :
    ThetaLowerSegment 2053390592 2053521664 (205333599027053 / 100000) (8213873854073 / 4000) := by
  exact
    packedTile65536 2053390592 2053521664 14 6178 45314 31 _ _ (1072137 / 50000) (2144277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053521664 :
    ThetaLowerSegment 2053521664 2053652736 (8213873854073 / 4000) (102679998613599 / 50000) := by
  exact
    packedTile65536 2053521664 2053652736 14 6133 45315 31 _ _ (2144281 / 100000) (536071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053652736 :
    ThetaLowerSegment 2053652736 2053783808 (102679998613599 / 50000) (12835825109159 / 6250) := by
  exact
    packedTile65536 2053652736 2053783808 14 6158 45317 31 _ _ (2144287 / 100000) (214429 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053783808 :
    ThetaLowerSegment 2053783808 2053914880 (12835825109159 / 6250) (205386326963997 / 100000) := by
  exact
    packedTile65536 2053783808 2053914880 14 6121 45318 31 _ _ (2144293 / 100000) (268037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2053914880 :
    ThetaLowerSegment 2053914880 2054045952 (205386326963997 / 100000)
      (205399501543197 / 100000) := by
  exact
    packedTile65536 2053914880 2054045952 14 6144 45320 31 _ _ (21443 / 1000) (2144303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054045952 :
    ThetaLowerSegment 2054045952 2054177024 (205399501543197 / 100000)
      (205412581809797 / 100000) := by
  exact
    packedTile65536 2054045952 2054177024 14 6100 45321 31 _ _ (1072153 / 50000) (2144309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054177024 :
    ThetaLowerSegment 2054177024 2054308096 (205412581809797 / 100000)
      (25678201063909 / 12500) := by
  exact
    packedTile65536 2054177024 2054308096 14 6075 45323 31 _ _ (2144313 / 100000) (536079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054308096 :
    ThetaLowerSegment 2054308096 2054439168 (25678201063909 / 12500)
      (205438695290129 / 100000) := by
  exact
    packedTile65536 2054308096 2054439168 14 6103 45324 31 _ _ (2144319 / 100000) (1072161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054439168 :
    ThetaLowerSegment 2054439168 2054570240 (205438695290129 / 100000)
      (102725846021977 / 50000) := by
  exact
    packedTile65536 2054439168 2054570240 14 6061 45325 31 _ _ (85773 / 4000) (268041 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054570240 :
    ThetaLowerSegment 2054570240 2054701312 (102725846021977 / 50000)
      (102732385162411 / 50000) := by
  exact
    packedTile65536 2054570240 2054701312 14 6099 45327 31 _ _ (536083 / 25000) (428867 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054701312 :
    ThetaLowerSegment 2054701312 2054832384 (102732385162411 / 50000)
      (102738991867789 / 50000) := by
  exact
    packedTile65536 2054701312 2054832384 14 6162 45328 31 _ _ (1072169 / 50000) (2144341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054832384 :
    ThetaLowerSegment 2054832384 2054963456 (102738991867789 / 50000)
      (205491263664163 / 100000) := by
  exact
    packedTile65536 2054832384 2054963456 14 6193 45330 31 _ _ (428869 / 20000) (536087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2054963456 :
    ThetaLowerSegment 2054963456 2055094528 (205491263664163 / 100000)
      (205504344205263 / 100000) := by
  exact
    packedTile65536 2054963456 2055094528 14 6100 45331 31 _ _ (2144351 / 100000) (1072177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055094528 :
    ThetaLowerSegment 2055094528 2055225600 (205504344205263 / 100000)
      (25689691232057 / 12500) := by
  exact
    packedTile65536 2055094528 2055225600 14 6149 45333 31 _ _ (2144357 / 100000) (53609 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055225600 :
    ThetaLowerSegment 2055225600 2055356672 (25689691232057 / 12500) (10276530631061 / 5000) := by
  exact
    packedTile65536 2055225600 2055356672 14 6101 45334 31 _ _ (536091 / 25000) (2144367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055356672 :
    ThetaLowerSegment 2055356672 2055487744 (10276530631061 / 5000) (20554354960543 / 10000) := by
  exact
    packedTile65536 2055356672 2055487744 14 6033 45336 31 _ _ (214437 / 10000) (2144373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055487744 :
    ThetaLowerSegment 2055487744 2055618816 (20554354960543 / 10000) (102778303355447 / 50000) := by
  exact
    packedTile65536 2055487744 2055618816 14 6089 45337 31 _ _ (268047 / 12500) (2144379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055618816 :
    ThetaLowerSegment 2055618816 2055749888 (102778303355447 / 50000)
      (205569792521961 / 100000) := by
  exact
    packedTile65536 2055618816 2055749888 14 6149 45338 31 _ _ (2144383 / 100000) (1072193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055749888 :
    ThetaLowerSegment 2055749888 2055880960 (205569792521961 / 100000)
      (205582980514311 / 100000) := by
  exact
    packedTile65536 2055749888 2055880960 14 6150 45340 31 _ _ (2144389 / 100000) (268049 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2055880960 :
    ThetaLowerSegment 2055880960 2056012032 (205582980514311 / 100000)
      (205596162116523 / 100000) := by
  exact
    packedTile65536 2055880960 2056012032 14 6147 45341 31 _ _ (536099 / 25000) (2144399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056012032 :
    ThetaLowerSegment 2056012032 2056143104 (205596162116523 / 100000)
      (205609290145567 / 100000) := by
  exact
    packedTile65536 2056012032 2056143104 14 6122 45343 31 _ _ (1072201 / 50000) (428881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056143104 :
    ThetaLowerSegment 2056143104 2056274176 (205609290145567 / 100000)
      (205622347445879 / 100000) := by
  exact
    packedTile65536 2056143104 2056274176 14 6089 45344 31 _ _ (268051 / 12500) (2144411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056274176 :
    ThetaLowerSegment 2056274176 2056405248 (205622347445879 / 100000)
      (25704435784573 / 12500) := by
  exact
    packedTile65536 2056274176 2056405248 14 6127 45346 31 _ _ (428883 / 20000) (1072209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056405248 :
    ThetaLowerSegment 2056405248 2056536320 (25704435784573 / 12500)
      (205648479323423 / 100000) := by
  exact
    packedTile65536 2056405248 2056536320 14 6059 45347 31 _ _ (2144421 / 100000) (268053 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056536320 :
    ThetaLowerSegment 2056536320 2056667392 (205648479323423 / 100000)
      (205661590350101 / 100000) := by
  exact
    packedTile65536 2056536320 2056667392 14 6114 45349 31 _ _ (2144427 / 100000) (214443 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056667392 :
    ThetaLowerSegment 2056667392 2056798464 (205661590350101 / 100000)
      (205674613497783 / 100000) := by
  exact
    packedTile65536 2056667392 2056798464 14 6073 45350 31 _ _ (1072217 / 50000) (2144437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056798464 :
    ThetaLowerSegment 2056798464 2056929536 (205674613497783 / 100000)
      (205687816814863 / 100000) := by
  exact
    packedTile65536 2056798464 2056929536 14 6157 45351 31 _ _ (53611 / 2500) (2144443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2056929536 :
    ThetaLowerSegment 2056929536 2057060608 (205687816814863 / 100000)
      (51425258260431 / 25000) := by
  exact
    packedTile65536 2056929536 2057060608 14 6163 45353 31 _ _ (2144447 / 100000) (42889 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057060608 :
    ThetaLowerSegment 2057060608 2057191680 (51425258260431 / 25000) (51428517828991 / 25000) := by
  exact
    packedTile65536 2057060608 2057191680 14 6080 45354 31 _ _ (2144453 / 100000) (268057 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057191680 :
    ThetaLowerSegment 2057191680 2057322752 (51428517828991 / 25000)
      (205727051726291 / 100000) := by
  exact
    packedTile65536 2057191680 2057322752 14 6053 45356 31 _ _ (2144459 / 100000) (1072231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057322752 :
    ThetaLowerSegment 2057322752 2057339136 (205727051726291 / 100000)
      (205728698676179 / 100000) := by
  exact
    packedTile65536 2057322752 2057339136 11 768 45357 31 _ _ (1072233 / 50000) (2144469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2057339136 :
    ThetaLowerSegment 2057339136 2057341184 (205728698676179 / 100000)
      (205728900255983 / 100000) := by
  exact
    packedTile65536 2057339136 2057341184 8 94 45357 31 _ _ (1072233 / 50000) (2144469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2025341184_2057341184 :
    ThetaLowerSegment 2025341184 2057341184 (50632294223973 / 25000)
      (205728900255983 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2025341184 cell2025472256)
                  (ThetaLowerSegment.join cell2025603328 cell2025734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2025865472 cell2025996544)
                  (ThetaLowerSegment.join cell2026127616 cell2026258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2026389760 cell2026520832)
                  (ThetaLowerSegment.join cell2026651904 cell2026782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2026914048 cell2027045120)
                  (ThetaLowerSegment.join cell2027176192 cell2027307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2027438336 cell2027569408)
                  (ThetaLowerSegment.join cell2027700480 cell2027831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2027962624 cell2028093696)
                  (ThetaLowerSegment.join cell2028224768 cell2028355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2028486912 cell2028617984)
                  (ThetaLowerSegment.join cell2028749056 cell2028880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2029011200 cell2029142272)
                  (ThetaLowerSegment.join cell2029273344 cell2029404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2029535488 cell2029666560)
                  (ThetaLowerSegment.join cell2029797632 cell2029928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2030059776 cell2030190848)
                  (ThetaLowerSegment.join cell2030321920 cell2030452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2030584064 cell2030715136)
                  (ThetaLowerSegment.join cell2030846208 cell2030977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2031108352 cell2031239424)
                  (ThetaLowerSegment.join cell2031370496 cell2031501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2031632640 cell2031763712)
                  (ThetaLowerSegment.join cell2031894784 cell2032025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2032156928 cell2032288000)
                  (ThetaLowerSegment.join cell2032419072 cell2032550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2032681216 cell2032812288)
                  (ThetaLowerSegment.join cell2032943360 cell2033074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2033205504 cell2033336576)
                  (ThetaLowerSegment.join cell2033467648 cell2033598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2033729792 cell2033860864)
                  (ThetaLowerSegment.join cell2033991936 cell2034123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2034254080 cell2034385152)
                  (ThetaLowerSegment.join cell2034516224 cell2034647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2034778368 cell2034909440)
                  (ThetaLowerSegment.join cell2035040512 cell2035171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2035302656 cell2035433728)
                  (ThetaLowerSegment.join cell2035564800 cell2035695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2035826944 cell2035958016)
                  (ThetaLowerSegment.join cell2036089088 cell2036220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2036351232 cell2036482304)
                  (ThetaLowerSegment.join cell2036613376 cell2036744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2036875520 cell2037006592)
                  (ThetaLowerSegment.join cell2037137664 cell2037268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2037399808 cell2037530880)
                  (ThetaLowerSegment.join cell2037661952 cell2037793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2037924096 cell2038055168)
                  (ThetaLowerSegment.join cell2038186240 cell2038317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2038448384 cell2038579456)
                  (ThetaLowerSegment.join cell2038710528 cell2038841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2038972672 cell2039103744)
                  (ThetaLowerSegment.join cell2039234816 cell2039365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2039496960 cell2039628032)
                  (ThetaLowerSegment.join cell2039759104 cell2039890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2040021248 cell2040152320)
                  (ThetaLowerSegment.join cell2040283392 cell2040414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2040545536 cell2040676608)
                  (ThetaLowerSegment.join cell2040807680 cell2040938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2041069824 cell2041200896)
                  (ThetaLowerSegment.join cell2041331968 cell2041463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2041594112 cell2041725184)
                  (ThetaLowerSegment.join cell2041856256 cell2041987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2042118400 cell2042249472)
                  (ThetaLowerSegment.join cell2042380544 cell2042511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2042642688 cell2042773760)
                  (ThetaLowerSegment.join cell2042904832 cell2043035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2043166976 cell2043298048)
                  (ThetaLowerSegment.join cell2043429120 cell2043560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2043691264 cell2043822336)
                  (ThetaLowerSegment.join cell2043953408 cell2044084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2044215552 cell2044346624)
                  (ThetaLowerSegment.join cell2044477696 cell2044608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2044739840 cell2044870912)
                  (ThetaLowerSegment.join cell2045001984 cell2045133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2045264128 cell2045395200)
                  (ThetaLowerSegment.join cell2045526272 cell2045657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2045788416 cell2045919488)
                  (ThetaLowerSegment.join cell2046050560 cell2046181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2046312704 cell2046443776)
                  (ThetaLowerSegment.join cell2046574848 cell2046705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2046836992 cell2046968064)
                  (ThetaLowerSegment.join cell2047099136 cell2047230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2047361280 cell2047492352)
                  (ThetaLowerSegment.join cell2047623424 cell2047754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2047885568 cell2048016640)
                  (ThetaLowerSegment.join cell2048147712 cell2048278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2048409856 cell2048540928)
                  (ThetaLowerSegment.join cell2048672000 cell2048803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2048934144 cell2049065216)
                  (ThetaLowerSegment.join cell2049196288 cell2049327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2049458432 cell2049589504)
                  (ThetaLowerSegment.join cell2049720576 cell2049851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2049982720 cell2050113792)
                  (ThetaLowerSegment.join cell2050244864 cell2050375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2050507008 cell2050638080)
                  (ThetaLowerSegment.join cell2050769152 cell2050900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2051031296 cell2051162368)
                  (ThetaLowerSegment.join cell2051293440 cell2051424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2051555584 cell2051686656)
                  (ThetaLowerSegment.join cell2051817728 cell2051948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2052079872 cell2052210944)
                  (ThetaLowerSegment.join cell2052342016 cell2052473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2052604160 cell2052735232)
                  (ThetaLowerSegment.join cell2052866304 cell2052997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2053128448 cell2053259520)
                  (ThetaLowerSegment.join cell2053390592 cell2053521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2053652736 cell2053783808)
                  (ThetaLowerSegment.join cell2053914880 cell2054045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2054177024 cell2054308096)
                  (ThetaLowerSegment.join cell2054439168 cell2054570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2054701312 cell2054832384)
                  (ThetaLowerSegment.join cell2054963456 cell2055094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2055225600 cell2055356672)
                  (ThetaLowerSegment.join cell2055487744 cell2055618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2055749888 cell2055880960)
                  (ThetaLowerSegment.join cell2056012032 cell2056143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2056274176 cell2056405248)
                  (ThetaLowerSegment.join cell2056536320 cell2056667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2056798464 cell2056929536)
                (ThetaLowerSegment.join cell2057060608 cell2057191680))
              (ThetaLowerSegment.join cell2057322752 cell2057339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
