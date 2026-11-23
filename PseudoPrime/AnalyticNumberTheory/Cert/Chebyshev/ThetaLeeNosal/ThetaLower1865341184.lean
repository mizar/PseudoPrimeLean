/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1865341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1833341184 :
    ThetaLowerSegment 1833341184 1833472256 (36665812746061 / 20000) (7333694077611 / 4000) := by
  exact
    packedTile65536 1833341184 1833472256 14 6230 42817 31 _ _ (2132939 / 100000) (1066471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833472256 :
    ThetaLowerSegment 1833472256 1833603328 (7333694077611 / 4000) (36671123772879 / 20000) := by
  exact
    packedTile65536 1833472256 1833603328 14 6220 42819 31 _ _ (1066473 / 50000) (2132949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833603328 :
    ThetaLowerSegment 1833603328 1833734400 (36671123772879 / 20000)
      (183368791982123 / 100000) := by
  exact
    packedTile65536 1833603328 1833734400 14 6176 42820 31 _ _ (2132953 / 100000) (533239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833734400 :
    ThetaLowerSegment 1833734400 1833865472 (183368791982123 / 100000) (7335279117881 / 4000) := by
  exact
    packedTile65536 1833734400 1833865472 14 6182 42822 31 _ _ (2132961 / 100000) (533241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833865472 :
    ThetaLowerSegment 1833865472 1833996544 (7335279117881 / 4000) (183395219412369 / 100000) := by
  exact
    packedTile65536 1833865472 1833996544 14 6208 42823 31 _ _ (266621 / 12500) (2132971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833996544 :
    ThetaLowerSegment 1833996544 1834127616 (183395219412369 / 100000)
      (91704118479397 / 50000) := by
  exact
    packedTile65536 1833996544 1834127616 14 6103 42825 31 _ _ (85319 / 4000) (1066489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834127616 :
    ThetaLowerSegment 1834127616 1834258688 (91704118479397 / 50000) (45855315769967 / 25000) := by
  exact
    packedTile65536 1834127616 1834258688 14 6107 42826 31 _ _ (1066491 / 50000) (426597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834258688 :
    ThetaLowerSegment 1834258688 1834389760 (45855315769967 / 25000) (36686890270171 / 20000) := by
  exact
    packedTile65536 1834258688 1834389760 14 6183 42828 31 _ _ (2132989 / 100000) (66656 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834389760 :
    ThetaLowerSegment 1834389760 1834520832 (36686890270171 / 20000) (7337906610443 / 4000) := by
  exact
    packedTile65536 1834389760 1834520832 14 6195 42829 31 _ _ (533249 / 25000) (2132999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834520832 :
    ThetaLowerSegment 1834520832 1834651904 (7337906610443 / 4000) (91730292430123 / 50000) := by
  exact
    packedTile65536 1834520832 1834651904 14 6057 42831 31 _ _ (2133003 / 100000) (1066503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834651904 :
    ThetaLowerSegment 1834651904 1834782976 (91730292430123 / 50000) (22934200061671 / 12500) := by
  exact
    packedTile65536 1834651904 1834782976 14 6102 42832 31 _ _ (2133011 / 100000) (1066507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834782976 :
    ThetaLowerSegment 1834782976 1834914048 (22934200061671 / 12500) (91743321949219 / 50000) := by
  exact
    packedTile65536 1834782976 1834914048 14 6115 42834 31 _ _ (1066509 / 50000) (2133021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1834914048 :
    ThetaLowerSegment 1834914048 1835045120 (91743321949219 / 50000) (45874995959197 / 25000) := by
  exact
    packedTile65536 1834914048 1835045120 14 6254 42835 31 _ _ (85321 / 4000) (533257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835045120 :
    ThetaLowerSegment 1835045120 1835176192 (45874995959197 / 25000) (45878267497027 / 25000) := by
  exact
    packedTile65536 1835045120 1835176192 14 6135 42837 31 _ _ (266629 / 12500) (426607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835176192 :
    ThetaLowerSegment 1835176192 1835307264 (45878267497027 / 25000)
      (183526309761181 / 100000) := by
  exact
    packedTile65536 1835176192 1835307264 14 6207 42838 31 _ _ (2133039 / 100000) (1066521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835307264 :
    ThetaLowerSegment 1835307264 1835438336 (183526309761181 / 100000)
      (183539300011321 / 100000) := by
  exact
    packedTile65536 1835307264 1835438336 14 6090 42840 31 _ _ (1066523 / 50000) (2133049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835438336 :
    ThetaLowerSegment 1835438336 1835569408 (183539300011321 / 100000)
      (183552495077179 / 100000) := by
  exact
    packedTile65536 1835438336 1835569408 14 6186 42842 31 _ _ (2133053 / 100000) (66658 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835569408 :
    ThetaLowerSegment 1835569408 1835700480 (183552495077179 / 100000)
      (183565404362351 / 100000) := by
  exact
    packedTile65536 1835569408 1835700480 14 6052 42843 31 _ _ (2133061 / 100000) (266633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835700480 :
    ThetaLowerSegment 1835700480 1835831552 (183565404362351 / 100000)
      (183578537662027 / 100000) := by
  exact
    packedTile65536 1835700480 1835831552 14 6157 42845 31 _ _ (533267 / 25000) (2133071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835831552 :
    ThetaLowerSegment 1835831552 1835962624 (183578537662027 / 100000)
      (183591664605577 / 100000) := by
  exact
    packedTile65536 1835831552 1835962624 14 6154 42846 31 _ _ (85323 / 4000) (1066539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1835962624 :
    ThetaLowerSegment 1835962624 1836093696 (183591664605577 / 100000) (293767444707 / 160) := by
  exact
    packedTile65536 1835962624 1836093696 14 6089 42848 31 _ _ (1066541 / 50000) (426617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836093696 :
    ThetaLowerSegment 1836093696 1836224768 (293767444707 / 160) (183618001812837 / 100000) := by
  exact
    packedTile65536 1836093696 1836224768 14 6258 42849 31 _ _ (2133089 / 100000) (533273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836224768 :
    ThetaLowerSegment 1836224768 1836355840 (183618001812837 / 100000)
      (183631003032957 / 100000) := by
  exact
    packedTile65536 1836224768 1836355840 14 6095 42851 31 _ _ (266637 / 12500) (2133099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836355840 :
    ThetaLowerSegment 1836355840 1836486912 (183631003032957 / 100000)
      (183644074688141 / 100000) := by
  exact
    packedTile65536 1836355840 1836486912 14 6128 42852 31 _ _ (2133103 / 100000) (1066553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836486912 :
    ThetaLowerSegment 1836486912 1836617984 (183644074688141 / 100000)
      (45914270066477 / 25000) := by
  exact
    packedTile65536 1836486912 1836617984 14 6097 42854 31 _ _ (2133111 / 100000) (1066557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836617984 :
    ThetaLowerSegment 1836617984 1836749056 (45914270066477 / 25000) (45917587064967 / 25000) := by
  exact
    packedTile65536 1836617984 1836749056 14 6220 42855 31 _ _ (1066559 / 50000) (2133121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836749056 :
    ThetaLowerSegment 1836749056 1836880128 (45917587064967 / 25000)
      (183683311260493 / 100000) := by
  exact
    packedTile65536 1836749056 1836880128 14 6077 42857 31 _ _ (3413 / 160) (266641 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1836880128 :
    ThetaLowerSegment 1836880128 1837011200 (183683311260493 / 100000)
      (183696447087349 / 100000) := by
  exact
    packedTile65536 1836880128 1837011200 14 6158 42858 31 _ _ (533283 / 25000) (426627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837011200 :
    ThetaLowerSegment 1837011200 1837142272 (183696447087349 / 100000)
      (91854869338229 / 50000) := by
  exact
    packedTile65536 1837011200 1837142272 14 6231 42860 31 _ _ (2133139 / 100000) (1066571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837142272 :
    ThetaLowerSegment 1837142272 1837273344 (91854869338229 / 50000) (91861415963303 / 50000) := by
  exact
    packedTile65536 1837142272 1837273344 14 6138 42861 31 _ _ (1066573 / 50000) (2133149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837273344 :
    ThetaLowerSegment 1837273344 1837404416 (91861415963303 / 50000) (91868028737603 / 50000) := by
  exact
    packedTile65536 1837273344 1837404416 14 6200 42863 31 _ _ (2133153 / 100000) (533289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837404416 :
    ThetaLowerSegment 1837404416 1837535488 (91868028737603 / 50000) (91874578605383 / 50000) := by
  exact
    packedTile65536 1837404416 1837535488 14 6141 42864 31 _ _ (53329 / 2500) (2133163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837535488 :
    ThetaLowerSegment 1837535488 1837666560 (91874578605383 / 50000) (18376215460339 / 10000) := by
  exact
    packedTile65536 1837535488 1837666560 14 6093 42866 31 _ _ (133323 / 6250) (2133171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837666560 :
    ThetaLowerSegment 1837666560 1837797632 (18376215460339 / 10000) (18377530349409 / 10000) := by
  exact
    packedTile65536 1837666560 1837797632 14 6164 42868 31 _ _ (85327 / 4000) (1066589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837797632 :
    ThetaLowerSegment 1837797632 1837928704 (18377530349409 / 10000) (91894155818963 / 50000) := by
  exact
    packedTile65536 1837797632 1837928704 14 6098 42869 31 _ _ (1066591 / 50000) (426637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837928704 :
    ThetaLowerSegment 1837928704 1838059776 (91894155818963 / 50000) (5743793377703 / 3125) := by
  exact
    packedTile65536 1837928704 1838059776 14 6130 42871 31 _ _ (2133189 / 100000) (266649 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838059776 :
    ThetaLowerSegment 1838059776 1838190848 (5743793377703 / 3125) (45953625210577 / 25000) := by
  exact
    packedTile65536 1838059776 1838190848 14 6147 42872 31 _ _ (533299 / 25000) (2133199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838190848 :
    ThetaLowerSegment 1838190848 1838321920 (45953625210577 / 25000) (36765489450263 / 20000) := by
  exact
    packedTile65536 1838190848 1838321920 14 6069 42874 31 _ _ (2133203 / 100000) (1066603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838321920 :
    ThetaLowerSegment 1838321920 1838452992 (36765489450263 / 20000) (1470723866381 / 800) := by
  exact
    packedTile65536 1838321920 1838452992 14 6111 42875 31 _ _ (213321 / 10000) (2133213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838452992 :
    ThetaLowerSegment 1838452992 1838584064 (1470723866381 / 800) (36770718384447 / 20000) := by
  exact
    packedTile65536 1838452992 1838584064 14 6145 42877 31 _ _ (1066609 / 50000) (2133221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838584064 :
    ThetaLowerSegment 1838584064 1838715136 (36770718384447 / 20000) (36773356757127 / 20000) := by
  exact
    packedTile65536 1838584064 1838715136 14 6184 42878 31 _ _ (85329 / 4000) (533307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838715136 :
    ThetaLowerSegment 1838715136 1838846208 (36773356757127 / 20000)
      (183880014090499 / 100000) := by
  exact
    packedTile65536 1838715136 1838846208 14 6202 42880 31 _ _ (133327 / 6250) (426647 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838846208 :
    ThetaLowerSegment 1838846208 1838977280 (183880014090499 / 100000)
      (22986623822917 / 12500) := by
  exact
    packedTile65536 1838846208 1838977280 14 6083 42881 31 _ _ (2133239 / 100000) (1066621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1838977280 :
    ThetaLowerSegment 1838977280 1839108352 (22986623822917 / 12500) (5747063672371 / 3125) := by
  exact
    packedTile65536 1838977280 1839108352 14 6116 42883 31 _ _ (1066623 / 50000) (2133249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839108352 :
    ThetaLowerSegment 1839108352 1839239424 (5747063672371 / 3125) (91959578510911 / 50000) := by
  exact
    packedTile65536 1839108352 1839239424 14 6150 42884 31 _ _ (2133253 / 100000) (266657 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839239424 :
    ThetaLowerSegment 1839239424 1839370496 (91959578510911 / 50000) (91966114819551 / 50000) := by
  exact
    packedTile65536 1839239424 1839370496 14 6128 42886 31 _ _ (106663 / 5000) (2133263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839370496 :
    ThetaLowerSegment 1839370496 1839501568 (91966114819551 / 50000) (91972612750833 / 50000) := by
  exact
    packedTile65536 1839370496 1839501568 14 6092 42887 31 _ _ (2133267 / 100000) (213327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839501568 :
    ThetaLowerSegment 1839501568 1839632640 (91972612750833 / 50000)
      (183958411274441 / 100000) := by
  exact
    packedTile65536 1839501568 1839632640 14 6181 42889 31 _ _ (85331 / 4000) (1066639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839632640 :
    ThetaLowerSegment 1839632640 1839763712 (183958411274441 / 100000)
      (36794319844753 / 20000) := by
  exact
    packedTile65536 1839632640 1839763712 14 6182 42890 31 _ _ (1066641 / 50000) (426657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839763712 :
    ThetaLowerSegment 1839763712 1839894784 (36794319844753 / 20000)
      (183984701884803 / 100000) := by
  exact
    packedTile65536 1839763712 1839894784 14 6142 42892 31 _ _ (2133289 / 100000) (533323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1839894784 :
    ThetaLowerSegment 1839894784 1840025856 (183984701884803 / 100000) (7359913463531 / 4000) := by
  exact
    packedTile65536 1839894784 1840025856 14 6157 42893 31 _ _ (133331 / 6250) (2133299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840025856 :
    ThetaLowerSegment 1840025856 1840156928 (7359913463531 / 4000) (92005498467241 / 50000) := by
  exact
    packedTile65536 1840025856 1840156928 14 6169 42895 31 _ _ (2133303 / 100000) (1066653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840156928 :
    ThetaLowerSegment 1840156928 1840288000 (92005498467241 / 50000) (92012000796121 / 50000) := by
  exact
    packedTile65536 1840156928 1840288000 14 6096 42897 31 _ _ (213331 / 10000) (2133313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840288000 :
    ThetaLowerSegment 1840288000 1840419072 (92012000796121 / 50000)
      (184037016959259 / 100000) := by
  exact
    packedTile65536 1840288000 1840419072 14 6101 42898 31 _ _ (2133317 / 100000) (53333 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840419072 :
    ThetaLowerSegment 1840419072 1840550144 (184037016959259 / 100000)
      (184050203034903 / 100000) := by
  exact
    packedTile65536 1840419072 1840550144 14 6181 42900 31 _ _ (533331 / 25000) (2133327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840550144 :
    ThetaLowerSegment 1840550144 1840681216 (184050203034903 / 100000)
      (184063267560071 / 100000) := by
  exact
    packedTile65536 1840550144 1840681216 14 6124 42901 31 _ _ (533333 / 25000) (426667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840681216 :
    ThetaLowerSegment 1840681216 1840812288 (184063267560071 / 100000)
      (184076434528379 / 100000) := by
  exact
    packedTile65536 1840681216 1840812288 14 6172 42903 31 _ _ (2133339 / 100000) (1066671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840812288 :
    ThetaLowerSegment 1840812288 1840943360 (184076434528379 / 100000)
      (184089501272629 / 100000) := by
  exact
    packedTile65536 1840812288 1840943360 14 6125 42904 31 _ _ (1066673 / 50000) (2133349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1840943360 :
    ThetaLowerSegment 1840943360 1841074432 (184089501272629 / 100000)
      (184102612860167 / 100000) := by
  exact
    packedTile65536 1840943360 1841074432 14 6146 42906 31 _ _ (2133353 / 100000) (533339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841074432 :
    ThetaLowerSegment 1841074432 1841205504 (184102612860167 / 100000)
      (184115811958487 / 100000) := by
  exact
    packedTile65536 1841074432 1841205504 14 6187 42907 31 _ _ (26667 / 1250) (2133363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841205504 :
    ThetaLowerSegment 1841205504 1841336576 (184115811958487 / 100000)
      (46032214374423 / 25000) := by
  exact
    packedTile65536 1841205504 1841336576 14 6115 42909 31 _ _ (2133367 / 100000) (213337 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841336576 :
    ThetaLowerSegment 1841336576 1841467648 (46032214374423 / 25000) (92070893938753 / 50000) := by
  exact
    packedTile65536 1841336576 1841467648 14 6061 42910 31 _ _ (1066687 / 50000) (2133377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841467648 :
    ThetaLowerSegment 1841467648 1841598720 (92070893938753 / 50000)
      (184154982838991 / 100000) := by
  exact
    packedTile65536 1841467648 1841598720 14 6185 42912 31 _ _ (2133381 / 100000) (266673 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841598720 :
    ThetaLowerSegment 1841598720 1841729792 (184154982838991 / 100000)
      (184168211977979 / 100000) := by
  exact
    packedTile65536 1841598720 1841729792 14 6201 42913 31 _ _ (533347 / 25000) (2133391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841729792 :
    ThetaLowerSegment 1841729792 1841860864 (184168211977979 / 100000)
      (184181300362439 / 100000) := by
  exact
    packedTile65536 1841729792 1841860864 14 6135 42915 31 _ _ (533349 / 25000) (2133399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841860864 :
    ThetaLowerSegment 1841860864 1841991936 (184181300362439 / 100000)
      (184194386656441 / 100000) := by
  exact
    packedTile65536 1841860864 1841991936 14 6134 42916 31 _ _ (2133403 / 100000) (1066703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841991936 :
    ThetaLowerSegment 1841991936 1842123008 (184194386656441 / 100000)
      (184207526328631 / 100000) := by
  exact
    packedTile65536 1841991936 1842123008 14 6159 42918 31 _ _ (213341 / 10000) (2133413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842123008 :
    ThetaLowerSegment 1842123008 1842254080 (184207526328631 / 100000)
      (23027560321259 / 12500) := by
  exact
    packedTile65536 1842123008 1842254080 14 6073 42919 31 _ _ (2133417 / 100000) (106671 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842254080 :
    ThetaLowerSegment 1842254080 1842385152 (23027560321259 / 12500) (23029203324417 / 12500) := by
  exact
    packedTile65536 1842254080 1842385152 14 6161 42921 31 _ _ (133339 / 6250) (2133427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842385152 :
    ThetaLowerSegment 1842385152 1842516224 (23029203324417 / 12500)
      (184246791998037 / 100000) := by
  exact
    packedTile65536 1842385152 1842516224 14 6171 42923 31 _ _ (2133431 / 100000) (1066717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842516224 :
    ThetaLowerSegment 1842516224 1842647296 (184246791998037 / 100000)
      (184259759034201 / 100000) := by
  exact
    packedTile65536 1842516224 1842647296 14 6078 42924 31 _ _ (1066719 / 50000) (2133441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842647296 :
    ThetaLowerSegment 1842647296 1842778368 (184259759034201 / 100000)
      (46068228997379 / 25000) := by
  exact
    packedTile65536 1842647296 1842778368 14 6167 42926 31 _ _ (426689 / 20000) (266681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842778368 :
    ThetaLowerSegment 1842778368 1842909440 (46068228997379 / 25000)
      (184286102862509 / 100000) := by
  exact
    packedTile65536 1842778368 1842909440 14 6181 42927 31 _ _ (2133453 / 100000) (133341 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1842909440 :
    ThetaLowerSegment 1842909440 1843040512 (184286102862509 / 100000)
      (184299262043789 / 100000) := by
  exact
    packedTile65536 1842909440 1843040512 14 6168 42929 31 _ _ (106673 / 5000) (2133463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843040512 :
    ThetaLowerSegment 1843040512 1843171584 (184299262043789 / 100000)
      (184312438335981 / 100000) := by
  exact
    packedTile65536 1843040512 1843171584 14 6176 42930 31 _ _ (2133467 / 100000) (213347 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843171584 :
    ThetaLowerSegment 1843171584 1843302656 (184312438335981 / 100000)
      (184325599737087 / 100000) := by
  exact
    packedTile65536 1843171584 1843302656 14 6169 42932 31 _ _ (1066737 / 50000) (2133477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843302656 :
    ThetaLowerSegment 1843302656 1843433728 (184325599737087 / 100000)
      (184338827319287 / 100000) := by
  exact
    packedTile65536 1843302656 1843433728 14 6200 42933 31 _ _ (2133481 / 100000) (533371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843433728 :
    ThetaLowerSegment 1843433728 1843564800 (184338827319287 / 100000)
      (184351899200263 / 100000) := by
  exact
    packedTile65536 1843433728 1843564800 14 6127 42935 31 _ _ (133343 / 6250) (2133491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843564800 :
    ThetaLowerSegment 1843564800 1843695872 (184351899200263 / 100000)
      (92182500496529 / 50000) := by
  exact
    packedTile65536 1843564800 1843695872 14 6141 42936 31 _ _ (426699 / 20000) (1066749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843695872 :
    ThetaLowerSegment 1843695872 1843826944 (92182500496529 / 50000) (92189075949693 / 50000) := by
  exact
    packedTile65536 1843695872 1843826944 14 6164 42938 31 _ _ (1066751 / 50000) (426701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843826944 :
    ThetaLowerSegment 1843826944 1843958016 (92189075949693 / 50000)
      (184391228176047 / 100000) := by
  exact
    packedTile65536 1843826944 1843958016 14 6129 42939 31 _ _ (2133509 / 100000) (266689 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1843958016 :
    ThetaLowerSegment 1843958016 1844089088 (184391228176047 / 100000)
      (36880867300899 / 20000) := by
  exact
    packedTile65536 1843958016 1844089088 14 6144 42941 31 _ _ (2133517 / 100000) (26669 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844089088 :
    ThetaLowerSegment 1844089088 1844220160 (36880867300899 / 20000)
      (184417449142999 / 100000) := by
  exact
    packedTile65536 1844089088 1844220160 14 6146 42942 31 _ _ (533381 / 25000) (2133527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844220160 :
    ThetaLowerSegment 1844220160 1844351232 (184417449142999 / 100000) (1844304018097 / 1000) := by
  exact
    packedTile65536 1844220160 1844351232 14 6071 42944 31 _ _ (2133531 / 100000) (1066767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844351232 :
    ThetaLowerSegment 1844351232 1844482304 (1844304018097 / 1000) (46110933038781 / 25000) := by
  exact
    packedTile65536 1844351232 1844482304 14 6248 42945 31 _ _ (1066769 / 50000) (2133541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844482304 :
    ThetaLowerSegment 1844482304 1844613376 (46110933038781 / 25000) (46114184561361 / 25000) := by
  exact
    packedTile65536 1844482304 1844613376 14 6096 42947 31 _ _ (426709 / 20000) (533387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844613376 :
    ThetaLowerSegment 1844613376 1844744448 (46114184561361 / 25000) (9223486898889 / 5000) := by
  exact
    packedTile65536 1844613376 1844744448 14 6093 42948 31 _ _ (133347 / 6250) (426711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844744448 :
    ThetaLowerSegment 1844744448 1844875520 (9223486898889 / 5000) (184482921238841 / 100000) := by
  exact
    packedTile65536 1844744448 1844875520 14 6179 42950 31 _ _ (2133559 / 100000) (1066781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1844875520 :
    ThetaLowerSegment 1844875520 1845006592 (184482921238841 / 100000)
      (184496023467647 / 100000) := by
  exact
    packedTile65536 1844875520 1845006592 14 6141 42952 31 _ _ (1066783 / 50000) (2133569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845006592 :
    ThetaLowerSegment 1845006592 1845137664 (184496023467647 / 100000)
      (46127266499849 / 25000) := by
  exact
    packedTile65536 1845006592 1845137664 14 6113 42953 31 _ _ (2133573 / 100000) (266697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845137664 :
    ThetaLowerSegment 1845137664 1845268736 (46127266499849 / 25000) (11532649921301 / 6250) := by
  exact
    packedTile65536 1845137664 1845268736 14 6249 42955 31 _ _ (106679 / 5000) (2133583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845268736 :
    ThetaLowerSegment 1845268736 1845399808 (11532649921301 / 6250) (46133899812443 / 25000) := by
  exact
    packedTile65536 1845268736 1845399808 14 6187 42956 31 _ _ (533397 / 25000) (2133591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845399808 :
    ThetaLowerSegment 1845399808 1845530880 (46133899812443 / 25000)
      (184548693122287 / 100000) := by
  exact
    packedTile65536 1845399808 1845530880 14 6137 42958 31 _ _ (426719 / 20000) (1066799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845530880 :
    ThetaLowerSegment 1845530880 1845661952 (184548693122287 / 100000)
      (184561840377811 / 100000) := by
  exact
    packedTile65536 1845530880 1845661952 14 6162 42959 31 _ _ (1066801 / 50000) (426721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845661952 :
    ThetaLowerSegment 1845661952 1845793024 (184561840377811 / 100000)
      (23071859324399 / 12500) := by
  exact
    packedTile65536 1845661952 1845793024 14 6109 42961 31 _ _ (2133609 / 100000) (533403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845793024 :
    ThetaLowerSegment 1845793024 1845924096 (23071859324399 / 12500) (23073497141381 / 12500) := by
  exact
    packedTile65536 1845793024 1845924096 14 6141 42962 31 _ _ (133351 / 6250) (2133619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845924096 :
    ThetaLowerSegment 1845924096 1846055168 (23073497141381 / 12500) (36920163881577 / 20000) := by
  exact
    packedTile65536 1845924096 1846055168 14 6019 42964 31 _ _ (2133623 / 100000) (1066813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846055168 :
    ThetaLowerSegment 1846055168 1846186240 (36920163881577 / 20000) (36922774164519 / 20000) := by
  exact
    packedTile65536 1846055168 1846186240 14 6117 42965 31 _ _ (213363 / 10000) (2133633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846186240 :
    ThetaLowerSegment 1846186240 1846317312 (36922774164519 / 20000) (92313505946439 / 50000) := by
  exact
    packedTile65536 1846186240 1846317312 14 6159 42967 31 _ _ (2133637 / 100000) (53341 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846317312 :
    ThetaLowerSegment 1846317312 1846448384 (92313505946439 / 50000) (18464009753153 / 10000) := by
  exact
    packedTile65536 1846317312 1846448384 14 6133 42968 31 _ _ (533411 / 25000) (2133647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846448384 :
    ThetaLowerSegment 1846448384 1846579456 (18464009753153 / 10000)
      (184653234420737 / 100000) := by
  exact
    packedTile65536 1846448384 1846579456 14 6157 42970 31 _ _ (2133651 / 100000) (1066827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846579456 :
    ThetaLowerSegment 1846579456 1846710528 (184653234420737 / 100000)
      (92333157942033 / 50000) := by
  exact
    packedTile65536 1846579456 1846710528 14 6131 42971 31 _ _ (2133659 / 100000) (1066831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846710528 :
    ThetaLowerSegment 1846710528 1846841600 (92333157942033 / 50000) (46169835478749 / 25000) := by
  exact
    packedTile65536 1846710528 1846841600 14 6105 42973 31 _ _ (1066833 / 50000) (2133669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846841600 :
    ThetaLowerSegment 1846841600 1846972672 (46169835478749 / 25000) (23086566001767 / 12500) := by
  exact
    packedTile65536 1846841600 1846972672 14 6180 42974 31 _ _ (2133673 / 100000) (533419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1846972672 :
    ThetaLowerSegment 1846972672 1847103744 (23086566001767 / 12500) (23088217736797 / 12500) := by
  exact
    packedTile65536 1846972672 1847103744 14 6193 42976 31 _ _ (26671 / 1250) (2133683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847103744 :
    ThetaLowerSegment 1847103744 1847234816 (23088217736797 / 12500)
      (184718780855633 / 100000) := by
  exact
    packedTile65536 1847103744 1847234816 14 6111 42977 31 _ _ (2133687 / 100000) (213369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847234816 :
    ThetaLowerSegment 1847234816 1847365888 (184718780855633 / 100000)
      (184731811324891 / 100000) := by
  exact
    packedTile65536 1847234816 1847365888 14 6107 42979 31 _ _ (1066847 / 50000) (2133697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847365888 :
    ThetaLowerSegment 1847365888 1847496960 (184731811324891 / 100000)
      (184744976260061 / 100000) := by
  exact
    packedTile65536 1847365888 1847496960 14 6170 42980 31 _ _ (2133701 / 100000) (266713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847496960 :
    ThetaLowerSegment 1847496960 1847628032 (184744976260061 / 100000)
      (184757951338409 / 100000) := by
  exact
    packedTile65536 1847496960 1847628032 14 6081 42982 31 _ _ (533427 / 25000) (2133711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847628032 :
    ThetaLowerSegment 1847628032 1847759104 (184757951338409 / 100000)
      (184770945662759 / 100000) := by
  exact
    packedTile65536 1847628032 1847759104 14 6090 42984 31 _ _ (426743 / 20000) (1066859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847759104 :
    ThetaLowerSegment 1847759104 1847890176 (184770945662759 / 100000)
      (36956802088513 / 20000) := by
  exact
    packedTile65536 1847759104 1847890176 14 6123 42985 31 _ _ (1066861 / 50000) (85349 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1847890176 :
    ThetaLowerSegment 1847890176 1848021248 (36956802088513 / 20000) (36959445779983 / 20000) := by
  exact
    packedTile65536 1847890176 1848021248 14 6195 42987 31 _ _ (213373 / 10000) (2133733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848021248 :
    ThetaLowerSegment 1848021248 1848152320 (36959445779983 / 20000) (46202602248341 / 25000) := by
  exact
    packedTile65536 1848021248 1848152320 14 6177 42988 31 _ _ (2133737 / 100000) (106687 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848152320 :
    ThetaLowerSegment 1848152320 1848283392 (46202602248341 / 25000) (9241175402389 / 5000) := by
  exact
    packedTile65536 1848152320 1848283392 14 6139 42990 31 _ _ (133359 / 6250) (2133747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848283392 :
    ThetaLowerSegment 1848283392 1848414464 (9241175402389 / 5000) (92418268365693 / 50000) := by
  exact
    packedTile65536 1848283392 1848414464 14 6106 42991 31 _ _ (2133751 / 100000) (1066877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848414464 :
    ThetaLowerSegment 1848414464 1848545536 (92418268365693 / 50000) (5776551254352 / 3125) := by
  exact
    packedTile65536 1848414464 1848545536 14 6141 42993 31 _ _ (1066879 / 50000) (2133761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848545536 :
    ThetaLowerSegment 1848545536 1848676608 (5776551254352 / 3125) (46215702434211 / 25000) := by
  exact
    packedTile65536 1848545536 1848676608 14 6172 42994 31 _ _ (426753 / 20000) (266721 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848676608 :
    ThetaLowerSegment 1848676608 1848807680 (46215702434211 / 25000) (11554737908881 / 6250) := by
  exact
    packedTile65536 1848676608 1848807680 14 6091 42996 31 _ _ (533443 / 25000) (85351 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848807680 :
    ThetaLowerSegment 1848807680 1848938752 (11554737908881 / 6250) (23111086820907 / 12500) := by
  exact
    packedTile65536 1848807680 1848938752 14 6040 42997 31 _ _ (2133779 / 100000) (1066891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1848938752 :
    ThetaLowerSegment 1848938752 1849069824 (23111086820907 / 12500) (92450839327533 / 50000) := by
  exact
    packedTile65536 1848938752 1849069824 14 6085 42999 31 _ _ (1066893 / 50000) (2133789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849069824 :
    ThetaLowerSegment 1849069824 1849200896 (92450839327533 / 50000) (36982999984953 / 20000) := by
  exact
    packedTile65536 1849069824 1849200896 14 6243 43000 31 _ _ (2133793 / 100000) (533449 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849200896 :
    ThetaLowerSegment 1849200896 1849331968 (36982999984953 / 20000) (36985630106833 / 20000) := by
  exact
    packedTile65536 1849200896 1849331968 14 6163 43002 31 _ _ (10669 / 500) (2133803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849331968 :
    ThetaLowerSegment 1849331968 1849463040 (36985630106833 / 20000) (7397650511373 / 4000) := by
  exact
    packedTile65536 1849331968 1849463040 14 6145 43003 31 _ _ (133363 / 6250) (2133811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849463040 :
    ThetaLowerSegment 1849463040 1849594112 (7397650511373 / 4000) (36990819109547 / 20000) := by
  exact
    packedTile65536 1849463040 1849594112 14 6014 43005 31 _ _ (426763 / 20000) (1066909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849594112 :
    ThetaLowerSegment 1849594112 1849725184 (36990819109547 / 20000)
      (184967184411883 / 100000) := by
  exact
    packedTile65536 1849594112 1849725184 14 6134 43006 31 _ _ (1066911 / 50000) (85353 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849725184 :
    ThetaLowerSegment 1849725184 1849856256 (184967184411883 / 100000)
      (184980337333839 / 100000) := by
  exact
    packedTile65536 1849725184 1849856256 14 6164 43008 31 _ _ (2133829 / 100000) (266729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849856256 :
    ThetaLowerSegment 1849856256 1849987328 (184980337333839 / 100000)
      (184993415614683 / 100000) := by
  exact
    packedTile65536 1849856256 1849987328 14 6129 43009 31 _ _ (533459 / 25000) (2133839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849987328 :
    ThetaLowerSegment 1849987328 1850118400 (184993415614683 / 100000)
      (37001279583099 / 20000) := by
  exact
    packedTile65536 1849987328 1850118400 14 6084 43011 31 _ _ (2133843 / 100000) (1066923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850118400 :
    ThetaLowerSegment 1850118400 1850249472 (37001279583099 / 20000) (37003900804439 / 20000) := by
  exact
    packedTile65536 1850118400 1850249472 14 6142 43013 31 _ _ (42677 / 2000) (2133853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850249472 :
    ThetaLowerSegment 1850249472 1850380544 (37003900804439 / 20000) (37006516913121 / 20000) := by
  exact
    packedTile65536 1850249472 1850380544 14 6130 43014 31 _ _ (2133857 / 100000) (106693 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850380544 :
    ThetaLowerSegment 1850380544 1850511616 (37006516913121 / 20000)
      (185045677955109 / 100000) := by
  exact
    packedTile65536 1850380544 1850511616 14 6136 43016 31 _ _ (266733 / 12500) (2133867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850511616 :
    ThetaLowerSegment 1850511616 1850642688 (185045677955109 / 100000)
      (92529397430073 / 50000) := by
  exact
    packedTile65536 1850511616 1850642688 14 6147 43017 31 _ _ (2133871 / 100000) (1066937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850642688 :
    ThetaLowerSegment 1850642688 1850773760 (92529397430073 / 50000) (46267958747151 / 25000) := by
  exact
    packedTile65536 1850642688 1850773760 14 6111 43019 31 _ _ (1066939 / 50000) (2133881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850773760 :
    ThetaLowerSegment 1850773760 1850904832 (46267958747151 / 25000)
      (185085067209489 / 100000) := by
  exact
    packedTile65536 1850773760 1850904832 14 6201 43020 31 _ _ (426777 / 20000) (66684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1850904832 :
    ThetaLowerSegment 1850904832 1851035904 (185085067209489 / 100000)
      (46274539660761 / 25000) := by
  exact
    packedTile65536 1850904832 1851035904 14 6135 43022 31 _ _ (2133893 / 100000) (266737 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851035904 :
    ThetaLowerSegment 1851035904 1851166976 (46274539660761 / 25000) (23138919068343 / 12500) := by
  exact
    packedTile65536 1851035904 1851166976 14 6183 43023 31 _ _ (21339 / 1000) (2133903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851166976 :
    ThetaLowerSegment 1851166976 1851298048 (23138919068343 / 12500)
      (185124388584607 / 100000) := by
  exact
    packedTile65536 1851166976 1851298048 14 6109 43025 31 _ _ (2133907 / 100000) (213391 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851298048 :
    ThetaLowerSegment 1851298048 1851429120 (185124388584607 / 100000)
      (185137507887879 / 100000) := by
  exact
    packedTile65536 1851298048 1851429120 14 6148 43026 31 _ _ (1066957 / 50000) (2133917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851429120 :
    ThetaLowerSegment 1851429120 1851560192 (185137507887879 / 100000)
      (46287644538501 / 25000) := by
  exact
    packedTile65536 1851429120 1851560192 14 6125 43028 31 _ _ (2133921 / 100000) (533481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851560192 :
    ThetaLowerSegment 1851560192 1851691264 (46287644538501 / 25000) (46290911048787 / 25000) := by
  exact
    packedTile65536 1851560192 1851691264 14 6123 43029 31 _ _ (266741 / 12500) (2133931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851691264 :
    ThetaLowerSegment 1851691264 1851822336 (46290911048787 / 25000) (23147103989181 / 12500) := by
  exact
    packedTile65536 1851691264 1851822336 14 6180 43031 31 _ _ (426787 / 20000) (1066969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851822336 :
    ThetaLowerSegment 1851822336 1851953408 (23147103989181 / 12500) (92595081324561 / 50000) := by
  exact
    packedTile65536 1851822336 1851953408 14 6247 43032 31 _ _ (1066971 / 50000) (426789 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1851953408 :
    ThetaLowerSegment 1851953408 1852084480 (92595081324561 / 50000) (18520316266643 / 10000) := by
  exact
    packedTile65536 1851953408 1852084480 14 6092 43034 31 _ _ (2133949 / 100000) (66686 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852084480 :
    ThetaLowerSegment 1852084480 1852215552 (18520316266643 / 10000) (92608177391211 / 50000) := by
  exact
    packedTile65536 1852084480 1852215552 14 6182 43035 31 _ _ (533489 / 25000) (2133959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852215552 :
    ThetaLowerSegment 1852215552 1852346624 (92608177391211 / 50000) (92614779872733 / 50000) := by
  exact
    packedTile65536 1852215552 1852346624 14 6188 43037 31 _ _ (2133963 / 100000) (1066983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852346624 :
    ThetaLowerSegment 1852346624 1852477696 (92614779872733 / 50000) (11577663060751 / 6250) := by
  exact
    packedTile65536 1852346624 1852477696 14 6115 43038 31 _ _ (213397 / 10000) (2133973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852477696 :
    ThetaLowerSegment 1852477696 1852608768 (11577663060751 / 6250) (185255679581141 / 100000) := by
  exact
    packedTile65536 1852477696 1852608768 14 6125 43040 31 _ _ (2133977 / 100000) (106699 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852608768 :
    ThetaLowerSegment 1852608768 1852739840 (185255679581141 / 100000)
      (23158582576487 / 12500) := by
  exact
    packedTile65536 1852608768 1852739840 14 6083 43041 31 _ _ (426797 / 20000) (533497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852739840 :
    ThetaLowerSegment 1852739840 1852870912 (23158582576487 / 12500) (11580112208291 / 6250) := by
  exact
    packedTile65536 1852739840 1852870912 14 6155 43043 31 _ _ (266749 / 12500) (426799 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1852870912 :
    ThetaLowerSegment 1852870912 1853001984 (11580112208291 / 6250) (185294959972487 / 100000) := by
  exact
    packedTile65536 1852870912 1853001984 14 6169 43044 31 _ _ (2133999 / 100000) (1067001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853001984 :
    ThetaLowerSegment 1853001984 1853133056 (185294959972487 / 100000)
      (185308099047429 / 100000) := by
  exact
    packedTile65536 1853001984 1853133056 14 6157 43046 31 _ _ (1067003 / 50000) (2134009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853133056 :
    ThetaLowerSegment 1853133056 1853264128 (185308099047429 / 100000)
      (185321069578443 / 100000) := by
  exact
    packedTile65536 1853133056 1853264128 14 6078 43048 31 _ _ (2134013 / 100000) (66688 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853264128 :
    ThetaLowerSegment 1853264128 1853395200 (185321069578443 / 100000)
      (185334304770483 / 100000) := by
  exact
    packedTile65536 1853264128 1853395200 14 6202 43049 31 _ _ (106701 / 5000) (2134023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853395200 :
    ThetaLowerSegment 1853395200 1853526272 (185334304770483 / 100000)
      (92673632358227 / 50000) := by
  exact
    packedTile65536 1853395200 1853526272 14 6073 43051 31 _ _ (2134027 / 100000) (213403 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853526272 :
    ThetaLowerSegment 1853526272 1853657344 (92673632358227 / 50000) (18536029085999 / 10000) := by
  exact
    packedTile65536 1853526272 1853657344 14 6104 43052 31 _ _ (1067017 / 50000) (2134037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853657344 :
    ThetaLowerSegment 1853657344 1853788416 (18536029085999 / 10000) (92686649986963 / 50000) := by
  exact
    packedTile65536 1853657344 1853788416 14 6096 43054 31 _ _ (2134041 / 100000) (533511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853788416 :
    ThetaLowerSegment 1853788416 1853919488 (92686649986963 / 50000) (3707725841163 / 2000) := by
  exact
    packedTile65536 1853788416 1853919488 14 6088 43055 31 _ _ (66689 / 3125) (2134051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853919488 :
    ThetaLowerSegment 1853919488 1854050560 (3707725841163 / 2000) (18539954880781 / 10000) := by
  exact
    packedTile65536 1853919488 1854050560 14 6212 43057 31 _ _ (426811 / 20000) (1067029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854050560 :
    ThetaLowerSegment 1854050560 1854181632 (18539954880781 / 10000) (46353162453607 / 25000) := by
  exact
    packedTile65536 1854050560 1854181632 14 6139 43058 31 _ _ (1067031 / 50000) (426813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854181632 :
    ThetaLowerSegment 1854181632 1854312704 (46353162453607 / 25000)
      (185425861835607 / 100000) := by
  exact
    packedTile65536 1854181632 1854312704 14 6191 43060 31 _ _ (2134069 / 100000) (266759 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854312704 :
    ThetaLowerSegment 1854312704 1854443776 (185425861835607 / 100000)
      (185438988537083 / 100000) := by
  exact
    packedTile65536 1854312704 1854443776 14 6151 43061 31 _ _ (533519 / 25000) (2134079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854443776 :
    ThetaLowerSegment 1854443776 1854574848 (185438988537083 / 100000)
      (185451872002191 / 100000) := by
  exact
    packedTile65536 1854443776 1854574848 14 6037 43063 31 _ _ (533521 / 25000) (2134087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854574848 :
    ThetaLowerSegment 1854574848 1854705920 (185451872002191 / 100000)
      (23183117380173 / 12500) := by
  exact
    packedTile65536 1854574848 1854705920 14 6123 43064 31 _ _ (2134091 / 100000) (1067047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854705920 :
    ThetaLowerSegment 1854705920 1854836992 (23183117380173 / 12500) (11592380851341 / 6250) := by
  exact
    packedTile65536 1854705920 1854836992 14 6164 43066 31 _ _ (1067049 / 50000) (2134101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854836992 :
    ThetaLowerSegment 1854836992 1854968064 (11592380851341 / 6250) (185491301597301 / 100000) := by
  exact
    packedTile65536 1854836992 1854968064 14 6189 43067 31 _ _ (426821 / 20000) (533527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1854968064 :
    ThetaLowerSegment 1854968064 1855099136 (185491301597301 / 100000) (7420177226173 / 4000) := by
  exact
    packedTile65536 1854968064 1855099136 14 6152 43069 31 _ _ (66691 / 3125) (426823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855099136 :
    ThetaLowerSegment 1855099136 1855230208 (7420177226173 / 4000) (185517551217937 / 100000) := by
  exact
    packedTile65536 1855099136 1855230208 14 6148 43070 31 _ _ (2134119 / 100000) (1067061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855230208 :
    ThetaLowerSegment 1855230208 1855361280 (185517551217937 / 100000)
      (185530486155623 / 100000) := by
  exact
    packedTile65536 1855230208 1855361280 14 6061 43072 31 _ _ (1067063 / 50000) (2134129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855361280 :
    ThetaLowerSegment 1855361280 1855492352 (185530486155623 / 100000)
      (92771883432641 / 50000) := by
  exact
    packedTile65536 1855361280 1855492352 14 6223 43073 31 _ _ (2134133 / 100000) (266767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855492352 :
    ThetaLowerSegment 1855492352 1855623424 (92771883432641 / 50000) (92778481126451 / 50000) := by
  exact
    packedTile65536 1855492352 1855623424 14 6183 43075 31 _ _ (106707 / 5000) (2134143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855623424 :
    ThetaLowerSegment 1855623424 1855754496 (92778481126451 / 50000) (23196269443707 / 12500) := by
  exact
    packedTile65536 1855623424 1855754496 14 6182 43076 31 _ _ (2134147 / 100000) (42683 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855754496 :
    ThetaLowerSegment 1855754496 1855885568 (23196269443707 / 12500) (92791686182689 / 50000) := by
  exact
    packedTile65536 1855754496 1855885568 14 6193 43078 31 _ _ (1067077 / 50000) (2134157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1855885568 :
    ThetaLowerSegment 1855885568 1856016640 (92791686182689 / 50000) (23199562181941 / 12500) := by
  exact
    packedTile65536 1855885568 1856016640 14 6150 43079 31 _ _ (2134161 / 100000) (533541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856016640 :
    ThetaLowerSegment 1856016640 1856147712 (23199562181941 / 12500) (5800302773373 / 3125) := by
  exact
    packedTile65536 1856016640 1856147712 14 6181 43081 31 _ _ (266771 / 12500) (2134171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856147712 :
    ThetaLowerSegment 1856147712 1856278784 (5800302773373 / 3125) (92811411230443 / 50000) := by
  exact
    packedTile65536 1856147712 1856278784 14 6154 43083 31 _ _ (85367 / 4000) (1067089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856278784 :
    ThetaLowerSegment 1856278784 1856409856 (92811411230443 / 50000) (92817967437547 / 50000) := by
  exact
    packedTile65536 1856278784 1856409856 14 6144 43084 31 _ _ (1067091 / 50000) (426837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856409856 :
    ThetaLowerSegment 1856409856 1856540928 (92817967437547 / 50000) (92824474582857 / 50000) := by
  exact
    packedTile65536 1856409856 1856540928 14 6098 43086 31 _ _ (213419 / 10000) (2134193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856540928 :
    ThetaLowerSegment 1856540928 1856672000 (92824474582857 / 50000)
      (185662196126493 / 100000) := by
  exact
    packedTile65536 1856540928 1856672000 14 6207 43087 31 _ _ (2134197 / 100000) (10671 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856672000 :
    ThetaLowerSegment 1856672000 1856803072 (185662196126493 / 100000)
      (185675214770893 / 100000) := by
  exact
    packedTile65536 1856672000 1856803072 14 6100 43089 31 _ _ (533551 / 25000) (2134207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856803072 :
    ThetaLowerSegment 1856803072 1856934144 (185675214770893 / 100000)
      (185688352973809 / 100000) := by
  exact
    packedTile65536 1856803072 1856934144 14 6156 43090 31 _ _ (2134211 / 100000) (1067107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1856934144 :
    ThetaLowerSegment 1856934144 1857065216 (185688352973809 / 100000)
      (185701608601807 / 100000) := by
  exact
    packedTile65536 1856934144 1857065216 14 6211 43092 31 _ _ (1067109 / 50000) (2134221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857065216 :
    ThetaLowerSegment 1857065216 1857196288 (185701608601807 / 100000)
      (185714529199957 / 100000) := by
  exact
    packedTile65536 1857065216 1857196288 14 6054 43093 31 _ _ (85369 / 4000) (533557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857196288 :
    ThetaLowerSegment 1857196288 1857327360 (185714529199957 / 100000)
      (37145534786969 / 20000) := by
  exact
    packedTile65536 1857196288 1857327360 14 6159 43095 31 _ _ (266779 / 12500) (426847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857327360 :
    ThetaLowerSegment 1857327360 1857458432 (37145534786969 / 20000)
      (185740825115563 / 100000) := by
  exact
    packedTile65536 1857327360 1857458432 14 6162 43096 31 _ _ (2134239 / 100000) (1067121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857458432 :
    ThetaLowerSegment 1857458432 1857589504 (185740825115563 / 100000)
      (185753867492869 / 100000) := by
  exact
    packedTile65536 1857458432 1857589504 14 6111 43098 31 _ _ (1067123 / 50000) (2134249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857589504 :
    ThetaLowerSegment 1857589504 1857720576 (185753867492869 / 100000)
      (185767176694577 / 100000) := by
  exact
    packedTile65536 1857589504 1857720576 14 6236 43099 31 _ _ (2134253 / 100000) (133391 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857720576 :
    ThetaLowerSegment 1857720576 1857851648 (185767176694577 / 100000)
      (185780370689897 / 100000) := by
  exact
    packedTile65536 1857720576 1857851648 14 6182 43101 31 _ _ (106713 / 5000) (2134263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857851648 :
    ThetaLowerSegment 1857851648 1857982720 (185780370689897 / 100000)
      (37158683919667 / 20000) := by
  exact
    packedTile65536 1857851648 1857982720 14 6114 43102 31 _ _ (2134267 / 100000) (213427 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857982720 :
    ThetaLowerSegment 1857982720 1858113792 (37158683919667 / 20000) (297290250649 / 160) := by
  exact
    packedTile65536 1857982720 1858113792 14 6085 43104 31 _ _ (1067137 / 50000) (2134277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858113792 :
    ThetaLowerSegment 1858113792 1858244864 (297290250649 / 160) (46454868714547 / 25000) := by
  exact
    packedTile65536 1858113792 1858244864 14 6123 43105 31 _ _ (2134281 / 100000) (533571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858244864 :
    ThetaLowerSegment 1858244864 1858375936 (46454868714547 / 25000) (46458150715919 / 25000) := by
  exact
    packedTile65536 1858244864 1858375936 14 6151 43107 31 _ _ (133393 / 6250) (2134291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858375936 :
    ThetaLowerSegment 1858375936 1858507008 (46458150715919 / 25000) (92922868657553 / 50000) := by
  exact
    packedTile65536 1858375936 1858507008 14 6154 43108 31 _ _ (426859 / 20000) (1067149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858507008 :
    ThetaLowerSegment 1858507008 1858638080 (92922868657553 / 50000) (92929457247827 / 50000) := by
  exact
    packedTile65536 1858507008 1858638080 14 6174 43110 31 _ _ (1067151 / 50000) (426861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858638080 :
    ThetaLowerSegment 1858638080 1858769152 (92929457247827 / 50000)
      (185871999944133 / 100000) := by
  exact
    packedTile65536 1858638080 1858769152 14 6131 43111 31 _ _ (2134309 / 100000) (266789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858769152 :
    ThetaLowerSegment 1858769152 1858900224 (185871999944133 / 100000) (5808905985366 / 3125) := by
  exact
    packedTile65536 1858769152 1858900224 14 6087 43113 31 _ _ (2134317 / 100000) (26679 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1858900224 :
    ThetaLowerSegment 1858900224 1859031296 (5808905985366 / 3125) (46474532073983 / 25000) := by
  exact
    packedTile65536 1858900224 1859031296 14 6155 43114 31 _ _ (533581 / 25000) (2134327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859031296 :
    ThetaLowerSegment 1859031296 1859162368 (46474532073983 / 25000)
      (185911119968729 / 100000) := by
  exact
    packedTile65536 1859031296 1859162368 14 6087 43116 31 _ _ (2134331 / 100000) (1067167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859162368 :
    ThetaLowerSegment 1859162368 1859293440 (185911119968729 / 100000)
      (185924393416751 / 100000) := by
  exact
    packedTile65536 1859162368 1859293440 14 6219 43118 31 _ _ (1067169 / 50000) (2134341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859293440 :
    ThetaLowerSegment 1859293440 1859424512 (185924393416751 / 100000)
      (185937515369811 / 100000) := by
  exact
    packedTile65536 1859293440 1859424512 14 6148 43119 31 _ _ (426869 / 20000) (533587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859424512 :
    ThetaLowerSegment 1859424512 1859555584 (185937515369811 / 100000)
      (185950413258947 / 100000) := by
  exact
    packedTile65536 1859424512 1859555584 14 6043 43121 31 _ _ (133397 / 6250) (426871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859555584 :
    ThetaLowerSegment 1859555584 1859686656 (185950413258947 / 100000)
      (185963377355513 / 100000) := by
  exact
    packedTile65536 1859555584 1859686656 14 6074 43122 31 _ _ (2134359 / 100000) (1067181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859686656 :
    ThetaLowerSegment 1859686656 1859817728 (185963377355513 / 100000)
      (185976320150937 / 100000) := by
  exact
    packedTile65536 1859686656 1859817728 14 6064 43124 31 _ _ (1067183 / 50000) (2134369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859817728 :
    ThetaLowerSegment 1859817728 1859948800 (185976320150937 / 100000)
      (46497357901069 / 25000) := by
  exact
    packedTile65536 1859817728 1859948800 14 6143 43125 31 _ _ (2134373 / 100000) (266797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1859948800 :
    ThetaLowerSegment 1859948800 1860079872 (46497357901069 / 25000) (11625170416081 / 6250) := by
  exact
    packedTile65536 1859948800 1860079872 14 6229 43127 31 _ _ (106719 / 5000) (2134383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860079872 :
    ThetaLowerSegment 1860079872 1860210944 (11625170416081 / 6250) (186015714402191 / 100000) := by
  exact
    packedTile65536 1860079872 1860210944 14 6085 43128 31 _ _ (2134387 / 100000) (213439 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860210944 :
    ThetaLowerSegment 1860210944 1860342016 (186015714402191 / 100000)
      (186028828118927 / 100000) := by
  exact
    packedTile65536 1860210944 1860342016 14 6144 43130 31 _ _ (1067197 / 50000) (2134397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860342016 :
    ThetaLowerSegment 1860342016 1860473088 (186028828118927 / 100000)
      (93020910108907 / 50000) := by
  exact
    packedTile65536 1860342016 1860473088 14 6087 43131 31 _ _ (2134401 / 100000) (533601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860473088 :
    ThetaLowerSegment 1860473088 1860604160 (93020910108907 / 50000) (93027543848971 / 50000) := by
  exact
    packedTile65536 1860473088 1860604160 14 6216 43133 31 _ _ (266801 / 12500) (2134411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860604160 :
    ThetaLowerSegment 1860604160 1860735232 (93027543848971 / 50000)
      (186068067075557 / 100000) := by
  exact
    packedTile65536 1860604160 1860735232 14 6081 43134 31 _ _ (426883 / 20000) (1067209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860735232 :
    ThetaLowerSegment 1860735232 1860866304 (186068067075557 / 100000)
      (186081285551003 / 100000) := by
  exact
    packedTile65536 1860735232 1860866304 14 6193 43136 31 _ _ (1067211 / 50000) (85377 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860866304 :
    ThetaLowerSegment 1860866304 1860997376 (186081285551003 / 100000)
      (93047194405317 / 50000) := by
  exact
    packedTile65536 1860866304 1860997376 14 6139 43137 31 _ _ (2134429 / 100000) (66701 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1860997376 :
    ThetaLowerSegment 1860997376 1861128448 (93047194405317 / 50000) (18610745369339 / 10000) := by
  exact
    packedTile65536 1860997376 1861128448 14 6121 43139 31 _ _ (533609 / 25000) (2134439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861128448 :
    ThetaLowerSegment 1861128448 1861259520 (18610745369339 / 10000) (93060330813337 / 50000) := by
  exact
    packedTile65536 1861128448 1861259520 14 6188 43140 31 _ _ (2134443 / 100000) (1067223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861259520 :
    ThetaLowerSegment 1861259520 1861390592 (93060330813337 / 50000) (93066870768137 / 50000) := by
  exact
    packedTile65536 1861259520 1861390592 14 6128 43142 31 _ _ (42689 / 2000) (2134453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861390592 :
    ThetaLowerSegment 1861390592 1861521664 (93066870768137 / 50000) (46536719246163 / 25000) := by
  exact
    packedTile65536 1861390592 1861521664 14 6154 43143 31 _ _ (2134457 / 100000) (106723 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861521664 :
    ThetaLowerSegment 1861521664 1861652736 (46536719246163 / 25000) (93080070275081 / 50000) := by
  exact
    packedTile65536 1861521664 1861652736 14 6214 43145 31 _ _ (426893 / 20000) (533617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861652736 :
    ThetaLowerSegment 1861652736 1861783808 (93080070275081 / 50000) (93086598557693 / 50000) := by
  exact
    packedTile65536 1861652736 1861783808 14 6117 43146 31 _ _ (266809 / 12500) (85379 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861783808 :
    ThetaLowerSegment 1861783808 1861914880 (93086598557693 / 50000)
      (186186151268437 / 100000) := by
  exact
    packedTile65536 1861783808 1861914880 14 6069 43148 31 _ _ (2134479 / 100000) (1067241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861914880 :
    ThetaLowerSegment 1861914880 1862045952 (186186151268437 / 100000)
      (37239824934869 / 20000) := by
  exact
    packedTile65536 1861914880 1862045952 14 6078 43149 31 _ _ (1067243 / 50000) (2134489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862045952 :
    ThetaLowerSegment 1862045952 1862177024 (37239824934869 / 20000) (37242437554301 / 20000) := by
  exact
    packedTile65536 1862045952 1862177024 14 6120 43151 31 _ _ (2134493 / 100000) (66703 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862177024 :
    ThetaLowerSegment 1862177024 1862308096 (37242437554301 / 20000) (37245049328501 / 20000) := by
  exact
    packedTile65536 1862177024 1862308096 14 6118 43152 31 _ _ (4269 / 200) (2134503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862308096 :
    ThetaLowerSegment 1862308096 1862439168 (37245049328501 / 20000) (93119252032741 / 50000) := by
  exact
    packedTile65536 1862308096 1862439168 14 6211 43154 31 _ _ (2134507 / 100000) (213451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862439168 :
    ThetaLowerSegment 1862439168 1862570240 (93119252032741 / 50000) (93125772973011 / 50000) := by
  exact
    packedTile65536 1862439168 1862570240 14 6110 43155 31 _ _ (1067257 / 50000) (2134517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862570240 :
    ThetaLowerSegment 1862570240 1862701312 (93125772973011 / 50000) (46566155505417 / 25000) := by
  exact
    packedTile65536 1862570240 1862701312 14 6126 43157 31 _ _ (2134521 / 100000) (533631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862701312 :
    ThetaLowerSegment 1862701312 1862832384 (46566155505417 / 25000) (9313885760821 / 5000) := by
  exact
    packedTile65536 1862701312 1862832384 14 6134 43159 31 _ _ (66704 / 3125) (2134531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862832384 :
    ThetaLowerSegment 1862832384 1862963456 (9313885760821 / 5000) (18629092798807 / 10000) := by
  exact
    packedTile65536 1862832384 1862963456 14 6190 43160 31 _ _ (426907 / 20000) (1067269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1862963456 :
    ThetaLowerSegment 1862963456 1863094528 (18629092798807 / 10000) (93152010634349 / 50000) := by
  exact
    packedTile65536 1862963456 1863094528 14 6134 43162 31 _ _ (1067271 / 50000) (426909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863094528 :
    ThetaLowerSegment 1863094528 1863225600 (93152010634349 / 50000) (93158627736249 / 50000) := by
  exact
    packedTile65536 1863094528 1863225600 14 6200 43163 31 _ _ (2134549 / 100000) (266819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863225600 :
    ThetaLowerSegment 1863225600 1863356672 (93158627736249 / 50000) (93165146670273 / 50000) := by
  exact
    packedTile65536 1863225600 1863356672 14 6108 43165 31 _ _ (533639 / 25000) (2134559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863356672 :
    ThetaLowerSegment 1863356672 1863487744 (93165146670273 / 50000) (23292943622097 / 12500) := by
  exact
    packedTile65536 1863356672 1863487744 14 6210 43166 31 _ _ (2134563 / 100000) (1067283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863487744 :
    ThetaLowerSegment 1863487744 1863618816 (23292943622097 / 12500) (93178341492993 / 50000) := by
  exact
    packedTile65536 1863487744 1863618816 14 6153 43168 31 _ _ (213457 / 10000) (2134573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863618816 :
    ThetaLowerSegment 1863618816 1863749888 (93178341492993 / 50000) (93184937335923 / 50000) := by
  exact
    packedTile65536 1863618816 1863749888 14 6180 43169 31 _ _ (2134577 / 100000) (106729 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863749888 :
    ThetaLowerSegment 1863749888 1863880960 (93184937335923 / 50000) (18638288709591 / 10000) := by
  exact
    packedTile65536 1863749888 1863880960 14 6096 43171 31 _ _ (266823 / 12500) (2134587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1863880960 :
    ThetaLowerSegment 1863880960 1864012032 (18638288709591 / 10000) (93198005280689 / 50000) := by
  exact
    packedTile65536 1863880960 1864012032 14 6148 43172 31 _ _ (2134591 / 100000) (1067297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864012032 :
    ThetaLowerSegment 1864012032 1864143104 (93198005280689 / 50000) (93204652418861 / 50000) := by
  exact
    packedTile65536 1864012032 1864143104 14 6228 43174 31 _ _ (1067299 / 50000) (2134601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864143104 :
    ThetaLowerSegment 1864143104 1864274176 (93204652418861 / 50000)
      (186422370754927 / 100000) := by
  exact
    packedTile65536 1864143104 1864274176 14 6121 43175 31 _ _ (426921 / 20000) (133413 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864274176 :
    ThetaLowerSegment 1864274176 1864405248 (186422370754927 / 100000)
      (186435323580543 / 100000) := by
  exact
    packedTile65536 1864274176 1864405248 14 6068 43177 31 _ _ (533653 / 25000) (426923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864405248 :
    ThetaLowerSegment 1864405248 1864536320 (186435323580543 / 100000)
      (23306053500823 / 12500) := by
  exact
    packedTile65536 1864405248 1864536320 14 6139 43178 31 _ _ (2134619 / 100000) (1067311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864536320 :
    ThetaLowerSegment 1864536320 1864667392 (23306053500823 / 12500) (46615369777487 / 25000) := by
  exact
    packedTile65536 1864536320 1864667392 14 6114 43180 31 _ _ (1067313 / 50000) (2134629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864667392 :
    ThetaLowerSegment 1864667392 1864798464 (46615369777487 / 25000) (37294903916589 / 20000) := by
  exact
    packedTile65536 1864667392 1864798464 14 6109 43181 31 _ _ (2134633 / 100000) (533659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864798464 :
    ThetaLowerSegment 1864798464 1864929536 (37294903916589 / 20000) (37297466765373 / 20000) := by
  exact
    packedTile65536 1864798464 1864929536 14 6003 43183 31 _ _ (26683 / 1250) (2134643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1864929536 :
    ThetaLowerSegment 1864929536 1865060608 (37297466765373 / 20000) (11656285673307 / 6250) := by
  exact
    packedTile65536 1864929536 1865060608 14 6201 43184 31 _ _ (2134647 / 100000) (42693 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865060608 :
    ThetaLowerSegment 1865060608 1865191680 (11656285673307 / 6250) (46628437531677 / 25000) := by
  exact
    packedTile65536 1865060608 1865191680 14 6174 43186 31 _ _ (1067327 / 50000) (2134657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865191680 :
    ThetaLowerSegment 1865191680 1865322752 (46628437531677 / 25000)
      (186526756616181 / 100000) := by
  exact
    packedTile65536 1865191680 1865322752 14 6093 43187 31 _ _ (2134661 / 100000) (266833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865322752 :
    ThetaLowerSegment 1865322752 1865339136 (186526756616181 / 100000)
      (37305689881581 / 20000) := by
  exact
    packedTile65536 1865322752 1865339136 11 793 43189 31 _ _ (533667 / 25000) (2134671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865339136 :
    ThetaLowerSegment 1865339136 1865341184 (37305689881581 / 20000)
      (186528645797453 / 100000) := by
  exact
    packedTile65536 1865339136 1865341184 8 92 43189 31 _ _ (2134669 / 100000) (133417 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1833341184_1865341184 :
    ThetaLowerSegment 1833341184 1865341184 (36665812746061 / 20000)
      (186528645797453 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1833341184 cell1833472256)
                  (ThetaLowerSegment.join cell1833603328 cell1833734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1833865472 cell1833996544)
                  (ThetaLowerSegment.join cell1834127616 cell1834258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1834389760 cell1834520832)
                  (ThetaLowerSegment.join cell1834651904 cell1834782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1834914048 cell1835045120)
                  (ThetaLowerSegment.join cell1835176192 cell1835307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1835438336 cell1835569408)
                  (ThetaLowerSegment.join cell1835700480 cell1835831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1835962624 cell1836093696)
                  (ThetaLowerSegment.join cell1836224768 cell1836355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1836486912 cell1836617984)
                  (ThetaLowerSegment.join cell1836749056 cell1836880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1837011200 cell1837142272)
                  (ThetaLowerSegment.join cell1837273344 cell1837404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1837535488 cell1837666560)
                  (ThetaLowerSegment.join cell1837797632 cell1837928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1838059776 cell1838190848)
                  (ThetaLowerSegment.join cell1838321920 cell1838452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1838584064 cell1838715136)
                  (ThetaLowerSegment.join cell1838846208 cell1838977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1839108352 cell1839239424)
                  (ThetaLowerSegment.join cell1839370496 cell1839501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1839632640 cell1839763712)
                  (ThetaLowerSegment.join cell1839894784 cell1840025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1840156928 cell1840288000)
                  (ThetaLowerSegment.join cell1840419072 cell1840550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1840681216 cell1840812288)
                  (ThetaLowerSegment.join cell1840943360 cell1841074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1841205504 cell1841336576)
                  (ThetaLowerSegment.join cell1841467648 cell1841598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1841729792 cell1841860864)
                  (ThetaLowerSegment.join cell1841991936 cell1842123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1842254080 cell1842385152)
                  (ThetaLowerSegment.join cell1842516224 cell1842647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1842778368 cell1842909440)
                  (ThetaLowerSegment.join cell1843040512 cell1843171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1843302656 cell1843433728)
                  (ThetaLowerSegment.join cell1843564800 cell1843695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1843826944 cell1843958016)
                  (ThetaLowerSegment.join cell1844089088 cell1844220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1844351232 cell1844482304)
                  (ThetaLowerSegment.join cell1844613376 cell1844744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1844875520 cell1845006592)
                  (ThetaLowerSegment.join cell1845137664 cell1845268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1845399808 cell1845530880)
                  (ThetaLowerSegment.join cell1845661952 cell1845793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1845924096 cell1846055168)
                  (ThetaLowerSegment.join cell1846186240 cell1846317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1846448384 cell1846579456)
                  (ThetaLowerSegment.join cell1846710528 cell1846841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1846972672 cell1847103744)
                  (ThetaLowerSegment.join cell1847234816 cell1847365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1847496960 cell1847628032)
                  (ThetaLowerSegment.join cell1847759104 cell1847890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1848021248 cell1848152320)
                  (ThetaLowerSegment.join cell1848283392 cell1848414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1848545536 cell1848676608)
                  (ThetaLowerSegment.join cell1848807680 cell1848938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1849069824 cell1849200896)
                  (ThetaLowerSegment.join cell1849331968 cell1849463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1849594112 cell1849725184)
                  (ThetaLowerSegment.join cell1849856256 cell1849987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1850118400 cell1850249472)
                  (ThetaLowerSegment.join cell1850380544 cell1850511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1850642688 cell1850773760)
                  (ThetaLowerSegment.join cell1850904832 cell1851035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1851166976 cell1851298048)
                  (ThetaLowerSegment.join cell1851429120 cell1851560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1851691264 cell1851822336)
                  (ThetaLowerSegment.join cell1851953408 cell1852084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1852215552 cell1852346624)
                  (ThetaLowerSegment.join cell1852477696 cell1852608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1852739840 cell1852870912)
                  (ThetaLowerSegment.join cell1853001984 cell1853133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1853264128 cell1853395200)
                  (ThetaLowerSegment.join cell1853526272 cell1853657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1853788416 cell1853919488)
                  (ThetaLowerSegment.join cell1854050560 cell1854181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1854312704 cell1854443776)
                  (ThetaLowerSegment.join cell1854574848 cell1854705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1854836992 cell1854968064)
                  (ThetaLowerSegment.join cell1855099136 cell1855230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1855361280 cell1855492352)
                  (ThetaLowerSegment.join cell1855623424 cell1855754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1855885568 cell1856016640)
                  (ThetaLowerSegment.join cell1856147712 cell1856278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1856409856 cell1856540928)
                  (ThetaLowerSegment.join cell1856672000 cell1856803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1856934144 cell1857065216)
                  (ThetaLowerSegment.join cell1857196288 cell1857327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1857458432 cell1857589504)
                  (ThetaLowerSegment.join cell1857720576 cell1857851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1857982720 cell1858113792)
                  (ThetaLowerSegment.join cell1858244864 cell1858375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1858507008 cell1858638080)
                  (ThetaLowerSegment.join cell1858769152 cell1858900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1859031296 cell1859162368)
                  (ThetaLowerSegment.join cell1859293440 cell1859424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1859555584 cell1859686656)
                  (ThetaLowerSegment.join cell1859817728 cell1859948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1860079872 cell1860210944)
                  (ThetaLowerSegment.join cell1860342016 cell1860473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1860604160 cell1860735232)
                  (ThetaLowerSegment.join cell1860866304 cell1860997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1861128448 cell1861259520)
                  (ThetaLowerSegment.join cell1861390592 cell1861521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1861652736 cell1861783808)
                  (ThetaLowerSegment.join cell1861914880 cell1862045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1862177024 cell1862308096)
                  (ThetaLowerSegment.join cell1862439168 cell1862570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1862701312 cell1862832384)
                  (ThetaLowerSegment.join cell1862963456 cell1863094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1863225600 cell1863356672)
                  (ThetaLowerSegment.join cell1863487744 cell1863618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1863749888 cell1863880960)
                  (ThetaLowerSegment.join cell1864012032 cell1864143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1864274176 cell1864405248)
                  (ThetaLowerSegment.join cell1864536320 cell1864667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1864798464 cell1864929536)
                (ThetaLowerSegment.join cell1865060608 cell1865191680))
              (ThetaLowerSegment.join cell1865322752 cell1865339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
