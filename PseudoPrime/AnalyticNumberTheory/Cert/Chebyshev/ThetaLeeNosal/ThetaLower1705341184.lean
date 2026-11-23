/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1705341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1673341184 :
    ThetaLowerSegment 1673341184 1673472256 (167328895060343 / 100000)
      (33468376852791 / 20000) := by
  exact
    packedTile65536 1673341184 1673472256 14 6116 40906 31 _ _ (2123807 / 100000) (212381 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673472256 :
    ThetaLowerSegment 1673472256 1673603328 (33468376852791 / 20000) (8367748242027 / 5000) := by
  exact
    packedTile65536 1673472256 1673603328 14 6159 40908 31 _ _ (424763 / 20000) (1061909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673603328 :
    ThetaLowerSegment 1673603328 1673734400 (8367748242027 / 5000) (167368087942857 / 100000) := by
  exact
    packedTile65536 1673603328 1673734400 14 6179 40909 31 _ _ (2123823 / 100000) (1061913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673734400 :
    ThetaLowerSegment 1673734400 1673865472 (167368087942857 / 100000)
      (167381051807281 / 100000) := by
  exact
    packedTile65536 1673734400 1673865472 14 6104 40911 31 _ _ (2123831 / 100000) (1061917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673865472 :
    ThetaLowerSegment 1673865472 1673996544 (167381051807281 / 100000)
      (167394160141589 / 100000) := by
  exact
    packedTile65536 1673865472 1673996544 14 6172 40912 31 _ _ (2123839 / 100000) (1061921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673996544 :
    ThetaLowerSegment 1673996544 1674127616 (167394160141589 / 100000)
      (167407289757561 / 100000) := by
  exact
    packedTile65536 1673996544 1674127616 14 6182 40914 31 _ _ (1061923 / 50000) (2123849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674127616 :
    ThetaLowerSegment 1674127616 1674258688 (167407289757561 / 100000) (6696817541507 / 4000) := by
  exact
    packedTile65536 1674127616 1674258688 14 6191 40916 31 _ _ (1061927 / 50000) (2123857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674258688 :
    ThetaLowerSegment 1674258688 1674389760 (6696817541507 / 4000) (167433614977523 / 100000) := by
  exact
    packedTile65536 1674258688 1674389760 14 6204 40917 31 _ _ (1061931 / 50000) (424773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674389760 :
    ThetaLowerSegment 1674389760 1674520832 (167433614977523 / 100000)
      (167446585451613 / 100000) := by
  exact
    packedTile65536 1674389760 1674520832 14 6107 40919 31 _ _ (212387 / 10000) (2123873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674520832 :
    ThetaLowerSegment 1674520832 1674651904 (167446585451613 / 100000)
      (167459619690899 / 100000) := by
  exact
    packedTile65536 1674520832 1674651904 14 6137 40920 31 _ _ (1061939 / 50000) (2123881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674651904 :
    ThetaLowerSegment 1674651904 1674782976 (167459619690899 / 100000)
      (167472660350939 / 100000) := by
  exact
    packedTile65536 1674651904 1674782976 14 6140 40922 31 _ _ (1061943 / 50000) (2123889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674782976 :
    ThetaLowerSegment 1674782976 1674914048 (167472660350939 / 100000)
      (16748571592121 / 10000) := by
  exact
    packedTile65536 1674782976 1674914048 14 6147 40924 31 _ _ (2123893 / 100000) (265487 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1674914048 :
    ThetaLowerSegment 1674914048 1675045120 (16748571592121 / 10000) (33499808679997 / 20000) := by
  exact
    packedTile65536 1674914048 1675045120 14 6275 40925 31 _ _ (2123901 / 100000) (66372 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675045120 :
    ThetaLowerSegment 1675045120 1675176192 (33499808679997 / 20000) (20939006011849 / 12500) := by
  exact
    packedTile65536 1675045120 1675176192 14 6123 40927 31 _ _ (2123909 / 100000) (265489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675176192 :
    ThetaLowerSegment 1675176192 1675307264 (20939006011849 / 12500) (83762593322677 / 50000) := by
  exact
    packedTile65536 1675176192 1675307264 14 6186 40928 31 _ _ (2123917 / 100000) (26549 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675307264 :
    ThetaLowerSegment 1675307264 1675438336 (83762593322677 / 50000) (83769126515977 / 50000) := by
  exact
    packedTile65536 1675307264 1675438336 14 6152 40930 31 _ _ (84957 / 4000) (265491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675438336 :
    ThetaLowerSegment 1675438336 1675569408 (83769126515977 / 50000)
      (167551342831033 / 100000) := by
  exact
    packedTile65536 1675438336 1675569408 14 6163 40932 31 _ _ (2123933 / 100000) (66373 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675569408 :
    ThetaLowerSegment 1675569408 1675700480 (167551342831033 / 100000)
      (167564511259033 / 100000) := by
  exact
    packedTile65536 1675569408 1675700480 14 6200 40933 31 _ _ (106197 / 5000) (2123943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675700480 :
    ThetaLowerSegment 1675700480 1675831552 (167564511259033 / 100000)
      (167577622390037 / 100000) := by
  exact
    packedTile65536 1675700480 1675831552 14 6173 40935 31 _ _ (530987 / 25000) (2123951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675831552 :
    ThetaLowerSegment 1675831552 1675962624 (167577622390037 / 100000)
      (167590731446469 / 100000) := by
  exact
    packedTile65536 1675831552 1675962624 14 6172 40936 31 _ _ (530989 / 25000) (2123959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675962624 :
    ThetaLowerSegment 1675962624 1676093696 (167590731446469 / 100000)
      (167603910643089 / 100000) := by
  exact
    packedTile65536 1675962624 1676093696 14 6205 40938 31 _ _ (530991 / 25000) (2123967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676093696 :
    ThetaLowerSegment 1676093696 1676224768 (167603910643089 / 100000)
      (167617111129069 / 100000) := by
  exact
    packedTile65536 1676093696 1676224768 14 6215 40940 31 _ _ (530993 / 25000) (84959 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676224768 :
    ThetaLowerSegment 1676224768 1676355840 (167617111129069 / 100000)
      (167630271302953 / 100000) := by
  exact
    packedTile65536 1676224768 1676355840 14 6196 40941 31 _ _ (2123979 / 100000) (1061991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676355840 :
    ThetaLowerSegment 1676355840 1676486912 (167630271302953 / 100000) (4191076495717 / 2500) := by
  exact
    packedTile65536 1676355840 1676486912 14 6021 40943 31 _ _ (2123987 / 100000) (212399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676486912 :
    ThetaLowerSegment 1676486912 1676617984 (4191076495717 / 2500) (33531253790717 / 20000) := by
  exact
    packedTile65536 1676486912 1676617984 14 6219 40944 31 _ _ (424799 / 20000) (1061999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676617984 :
    ThetaLowerSegment 1676617984 1676749056 (33531253790717 / 20000)
      (167669293339981 / 100000) := by
  exact
    packedTile65536 1676617984 1676749056 14 6132 40946 31 _ _ (2124003 / 100000) (1062003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676749056 :
    ThetaLowerSegment 1676749056 1676880128 (167669293339981 / 100000)
      (167682445216093 / 100000) := by
  exact
    packedTile65536 1676749056 1676880128 14 6192 40948 31 _ _ (2124011 / 100000) (1062007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1676880128 :
    ThetaLowerSegment 1676880128 1677011200 (167682445216093 / 100000)
      (41923923180649 / 25000) := by
  exact
    packedTile65536 1676880128 1677011200 14 6237 40949 31 _ _ (2124019 / 100000) (1062011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677011200 :
    ThetaLowerSegment 1677011200 1677142272 (41923923180649 / 25000) (41927215420949 / 25000) := by
  exact
    packedTile65536 1677011200 1677142272 14 6200 40951 31 _ _ (1062013 / 50000) (2124029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677142272 :
    ThetaLowerSegment 1677142272 1677273344 (41927215420949 / 25000) (3354435558691 / 2000) := by
  exact
    packedTile65536 1677142272 1677273344 14 6081 40952 31 _ _ (1062017 / 50000) (2124037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677273344 :
    ThetaLowerSegment 1677273344 1677404416 (3354435558691 / 2000) (83867486241727 / 50000) := by
  exact
    packedTile65536 1677273344 1677404416 14 6212 40954 31 _ _ (1062021 / 50000) (424809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677404416 :
    ThetaLowerSegment 1677404416 1677535488 (83867486241727 / 50000) (41937032743301 / 25000) := by
  exact
    packedTile65536 1677404416 1677535488 14 6195 40956 31 _ _ (42481 / 2000) (2124053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677535488 :
    ThetaLowerSegment 1677535488 1677666560 (41937032743301 / 25000) (20970146055151 / 12500) := by
  exact
    packedTile65536 1677535488 1677666560 14 6138 40957 31 _ _ (1062029 / 50000) (2124061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677666560 :
    ThetaLowerSegment 1677666560 1677797632 (20970146055151 / 12500)
      (167774356760793 / 100000) := by
  exact
    packedTile65536 1677666560 1677797632 14 6209 40959 31 _ _ (424813 / 20000) (531017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677797632 :
    ThetaLowerSegment 1677797632 1677928704 (167774356760793 / 100000)
      (167787398569013 / 100000) := by
  exact
    packedTile65536 1677797632 1677928704 14 6140 40960 31 _ _ (2124073 / 100000) (531019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1677928704 :
    ThetaLowerSegment 1677928704 1678059776 (167787398569013 / 100000)
      (83900297742133 / 50000) := by
  exact
    packedTile65536 1677928704 1678059776 14 6213 40962 31 _ _ (2124081 / 100000) (531021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678059776 :
    ThetaLowerSegment 1678059776 1678190848 (83900297742133 / 50000)
      (167813796697401 / 100000) := by
  exact
    packedTile65536 1678059776 1678190848 14 6215 40964 31 _ _ (2124089 / 100000) (531023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678190848 :
    ThetaLowerSegment 1678190848 1678321920 (167813796697401 / 100000) (8391351172471 / 5000) := by
  exact
    packedTile65536 1678190848 1678321920 14 6227 40965 31 _ _ (2124097 / 100000) (21241 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678321920 :
    ThetaLowerSegment 1678321920 1678452992 (8391351172471 / 5000) (16784026511999 / 10000) := by
  exact
    packedTile65536 1678321920 1678452992 14 6234 40967 31 _ _ (424821 / 20000) (531027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678452992 :
    ThetaLowerSegment 1678452992 1678584064 (16784026511999 / 10000) (83926695004019 / 50000) := by
  exact
    packedTile65536 1678452992 1678584064 14 6179 40968 31 _ _ (132757 / 6250) (424823 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678584064 :
    ThetaLowerSegment 1678584064 1678715136 (83926695004019 / 50000) (83933205431819 / 50000) := by
  exact
    packedTile65536 1678584064 1678715136 14 6130 40970 31 _ _ (53103 / 2500) (2124123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678715136 :
    ThetaLowerSegment 1678715136 1678846208 (83933205431819 / 50000) (16787968453951 / 10000) := by
  exact
    packedTile65536 1678715136 1678846208 14 6249 40972 31 _ _ (66379 / 3125) (2124131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678846208 :
    ThetaLowerSegment 1678846208 1678977280 (16787968453951 / 10000) (83946393105179 / 50000) := by
  exact
    packedTile65536 1678846208 1678977280 14 6168 40973 31 _ _ (265517 / 12500) (2124139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1678977280 :
    ThetaLowerSegment 1678977280 1679108352 (83946393105179 / 50000) (83952956710139 / 50000) := by
  exact
    packedTile65536 1678977280 1679108352 14 6180 40975 31 _ _ (132759 / 6250) (2124147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679108352 :
    ThetaLowerSegment 1679108352 1679239424 (83952956710139 / 50000) (1679189174727 / 1000) := by
  exact
    packedTile65536 1679108352 1679239424 14 6122 40976 31 _ _ (2124151 / 100000) (1062077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679239424 :
    ThetaLowerSegment 1679239424 1679370496 (1679189174727 / 1000) (83966058498363 / 50000) := by
  exact
    packedTile65536 1679239424 1679370496 14 6214 40978 31 _ _ (2124159 / 100000) (1062081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679370496 :
    ThetaLowerSegment 1679370496 1679501568 (83966058498363 / 50000)
      (167945148761271 / 100000) := by
  exact
    packedTile65536 1679370496 1679501568 14 6135 40980 31 _ _ (2124167 / 100000) (212417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679501568 :
    ThetaLowerSegment 1679501568 1679632640 (167945148761271 / 100000)
      (83979134895123 / 50000) := by
  exact
    packedTile65536 1679501568 1679632640 14 6177 40981 31 _ _ (84967 / 4000) (1062089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679632640 :
    ThetaLowerSegment 1679632640 1679763712 (83979134895123 / 50000)
      (167971157208507 / 100000) := by
  exact
    packedTile65536 1679632640 1679763712 14 6067 40983 31 _ _ (2124183 / 100000) (1062093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679763712 :
    ThetaLowerSegment 1679763712 1679894784 (167971157208507 / 100000)
      (167984331434887 / 100000) := by
  exact
    packedTile65536 1679763712 1679894784 14 6202 40984 31 _ _ (212419 / 10000) (2124193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679894784 :
    ThetaLowerSegment 1679894784 1680025856 (167984331434887 / 100000)
      (167997484468903 / 100000) := by
  exact
    packedTile65536 1679894784 1680025856 14 6192 40986 31 _ _ (1062099 / 50000) (2124201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680025856 :
    ThetaLowerSegment 1680025856 1680156928 (167997484468903 / 100000)
      (33602068032723 / 20000) := by
  exact
    packedTile65536 1680025856 1680156928 14 6052 40988 31 _ _ (1062103 / 50000) (2124209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680156928 :
    ThetaLowerSegment 1680156928 1680288000 (33602068032723 / 20000)
      (168023433818711 / 100000) := by
  exact
    packedTile65536 1680156928 1680288000 14 6164 40989 31 _ _ (1062107 / 50000) (2124217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680288000 :
    ThetaLowerSegment 1680288000 1680419072 (168023433818711 / 100000)
      (168036553013783 / 100000) := by
  exact
    packedTile65536 1680288000 1680419072 14 6176 40991 31 _ _ (1062111 / 50000) (84969 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680419072 :
    ThetaLowerSegment 1680419072 1680550144 (168036553013783 / 100000)
      (168049693494377 / 100000) := by
  exact
    packedTile65536 1680419072 1680550144 14 6186 40992 31 _ _ (2124229 / 100000) (265529 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680550144 :
    ThetaLowerSegment 1680550144 1680681216 (168049693494377 / 100000)
      (84031386210793 / 50000) := by
  exact
    packedTile65536 1680550144 1680681216 14 6157 40994 31 _ _ (2124237 / 100000) (26553 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680681216 :
    ThetaLowerSegment 1680681216 1680812288 (84031386210793 / 50000) (84037920388413 / 50000) := by
  exact
    packedTile65536 1680681216 1680812288 14 6152 40996 31 _ _ (424849 / 20000) (265531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680812288 :
    ThetaLowerSegment 1680812288 1680943360 (84037920388413 / 50000) (84044475833171 / 50000) := by
  exact
    packedTile65536 1680812288 1680943360 14 6172 40997 31 _ _ (2124253 / 100000) (66383 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1680943360 :
    ThetaLowerSegment 1680943360 1681074432 (84044475833171 / 50000) (42025491222307 / 25000) := by
  exact
    packedTile65536 1680943360 1681074432 14 6126 40999 31 _ _ (2124261 / 100000) (265533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681074432 :
    ThetaLowerSegment 1681074432 1681205504 (42025491222307 / 25000) (42028756222223 / 25000) := by
  exact
    packedTile65536 1681074432 1681205504 14 6148 41000 31 _ _ (531067 / 25000) (2124271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681205504 :
    ThetaLowerSegment 1681205504 1681336576 (42028756222223 / 25000) (8406418054681 / 5000) := by
  exact
    packedTile65536 1681205504 1681336576 14 6278 41002 31 _ _ (531069 / 25000) (2124279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681336576 :
    ThetaLowerSegment 1681336576 1681467648 (8406418054681 / 5000) (42035369105759 / 25000) := by
  exact
    packedTile65536 1681336576 1681467648 14 6174 41004 31 _ _ (531071 / 25000) (2124287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681467648 :
    ThetaLowerSegment 1681467648 1681598720 (42035369105759 / 25000) (42038639453293 / 25000) := by
  exact
    packedTile65536 1681467648 1681598720 14 6158 41005 31 _ _ (531073 / 25000) (424859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681598720 :
    ThetaLowerSegment 1681598720 1681729792 (42038639453293 / 25000) (42041919372493 / 25000) := by
  exact
    packedTile65536 1681598720 1681729792 14 6176 41007 31 _ _ (21243 / 1000) (2124303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681729792 :
    ThetaLowerSegment 1681729792 1681860864 (42041919372493 / 25000)
      (168180854566293 / 100000) := by
  exact
    packedTile65536 1681729792 1681860864 14 6203 41008 31 _ _ (2124307 / 100000) (212431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681860864 :
    ThetaLowerSegment 1681860864 1681991936 (168180854566293 / 100000)
      (84097071078309 / 50000) := by
  exact
    packedTile65536 1681860864 1681991936 14 6255 41010 31 _ _ (424863 / 20000) (1062159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1681991936 :
    ThetaLowerSegment 1681991936 1682123008 (84097071078309 / 50000) (33641428177811 / 20000) := by
  exact
    packedTile65536 1681991936 1682123008 14 6119 41012 31 _ _ (2124323 / 100000) (1062163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682123008 :
    ThetaLowerSegment 1682123008 1682254080 (33641428177811 / 20000) (6728809920453 / 4000) := by
  exact
    packedTile65536 1682123008 1682254080 14 6170 41013 31 _ _ (2124331 / 100000) (1062167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682254080 :
    ThetaLowerSegment 1682254080 1682385152 (6728809920453 / 4000) (84116517203883 / 50000) := by
  exact
    packedTile65536 1682254080 1682385152 14 6019 41015 31 _ _ (2124339 / 100000) (1062171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682385152 :
    ThetaLowerSegment 1682385152 1682516224 (84116517203883 / 50000) (84123087806061 / 50000) := by
  exact
    packedTile65536 1682385152 1682516224 14 6186 41016 31 _ _ (1062173 / 50000) (2124349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682516224 :
    ThetaLowerSegment 1682516224 1682647296 (84123087806061 / 50000) (84129690298293 / 50000) := by
  exact
    packedTile65536 1682516224 1682647296 14 6216 41018 31 _ _ (1062177 / 50000) (2124357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682647296 :
    ThetaLowerSegment 1682647296 1682778368 (84129690298293 / 50000) (10517021598617 / 6250) := by
  exact
    packedTile65536 1682647296 1682778368 14 6103 41020 31 _ _ (1062181 / 50000) (424873 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682778368 :
    ThetaLowerSegment 1682778368 1682909440 (10517021598617 / 6250) (21035692770539 / 12500) := by
  exact
    packedTile65536 1682778368 1682909440 14 6212 41021 31 _ _ (212437 / 10000) (2124373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1682909440 :
    ThetaLowerSegment 1682909440 1683040512 (21035692770539 / 12500) (33659725240451 / 20000) := by
  exact
    packedTile65536 1682909440 1683040512 14 6159 41023 31 _ _ (2124377 / 100000) (106219 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683040512 :
    ThetaLowerSegment 1683040512 1683171584 (33659725240451 / 20000) (33662335684739 / 20000) := by
  exact
    packedTile65536 1683040512 1683171584 14 6144 41024 31 _ _ (424877 / 20000) (531097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683171584 :
    ThetaLowerSegment 1683171584 1683302656 (33662335684739 / 20000)
      (168324887899369 / 100000) := by
  exact
    packedTile65536 1683171584 1683302656 14 6218 41026 31 _ _ (2124393 / 100000) (531099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683302656 :
    ThetaLowerSegment 1683302656 1683433728 (168324887899369 / 100000) (6733518628477 / 4000) := by
  exact
    packedTile65536 1683302656 1683433728 14 6156 41028 31 _ _ (2124401 / 100000) (531101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683433728 :
    ThetaLowerSegment 1683433728 1683564800 (6733518628477 / 4000) (21043905674073 / 12500) := by
  exact
    packedTile65536 1683433728 1683564800 14 6251 41029 31 _ _ (2124409 / 100000) (531103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683564800 :
    ThetaLowerSegment 1683564800 1683695872 (21043905674073 / 12500) (21045542005497 / 12500) := by
  exact
    packedTile65536 1683564800 1683695872 14 6162 41031 31 _ _ (66388 / 3125) (2124419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683695872 :
    ThetaLowerSegment 1683695872 1683826944 (21045542005497 / 12500) (21047194807369 / 12500) := by
  exact
    packedTile65536 1683695872 1683826944 14 6224 41032 31 _ _ (265553 / 12500) (2124427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683826944 :
    ThetaLowerSegment 1683826944 1683958016 (21047194807369 / 12500) (4209769788647 / 2500) := by
  exact
    packedTile65536 1683826944 1683958016 14 6229 41034 31 _ _ (132777 / 6250) (424887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683958016 :
    ThetaLowerSegment 1683958016 1684089088 (4209769788647 / 2500) (2105048077871 / 1250) := by
  exact
    packedTile65536 1683958016 1684089088 14 6145 41036 31 _ _ (53111 / 2500) (2124443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684089088 :
    ThetaLowerSegment 1684089088 1684220160 (2105048077871 / 1250) (10526054716829 / 6250) := by
  exact
    packedTile65536 1684089088 1684220160 14 6133 41037 31 _ _ (66389 / 3125) (2124451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684220160 :
    ThetaLowerSegment 1684220160 1684351232 (10526054716829 / 6250) (168430057712539 / 100000) := by
  exact
    packedTile65536 1684220160 1684351232 14 6205 41039 31 _ _ (424891 / 20000) (1062229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684351232 :
    ThetaLowerSegment 1684351232 1684482304 (168430057712539 / 100000)
      (84221522277429 / 50000) := by
  exact
    packedTile65536 1684351232 1684482304 14 6113 41040 31 _ _ (2124463 / 100000) (1062233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684482304 :
    ThetaLowerSegment 1684482304 1684613376 (84221522277429 / 50000) (33691267473981 / 20000) := by
  exact
    packedTile65536 1684482304 1684613376 14 6257 41042 31 _ _ (2124471 / 100000) (1062237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684613376 :
    ThetaLowerSegment 1684613376 1684744448 (33691267473981 / 20000) (1347755733201 / 800) := by
  exact
    packedTile65536 1684613376 1684744448 14 6180 41044 31 _ _ (2124479 / 100000) (1062241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684744448 :
    ThetaLowerSegment 1684744448 1684875520 (1347755733201 / 800) (168482366529117 / 100000) := by
  exact
    packedTile65536 1684744448 1684875520 14 6072 41045 31 _ _ (1062243 / 50000) (2124489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1684875520 :
    ThetaLowerSegment 1684875520 1685006592 (168482366529117 / 100000)
      (168495644616617 / 100000) := by
  exact
    packedTile65536 1684875520 1685006592 14 6250 41047 31 _ _ (1062247 / 50000) (2124497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685006592 :
    ThetaLowerSegment 1685006592 1685137664 (168495644616617 / 100000)
      (168508943999137 / 100000) := by
  exact
    packedTile65536 1685006592 1685137664 14 6260 41048 31 _ _ (1062251 / 50000) (424901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685137664 :
    ThetaLowerSegment 1685137664 1685268736 (168508943999137 / 100000)
      (168522050101327 / 100000) := by
  exact
    packedTile65536 1685137664 1685268736 14 6169 41050 31 _ _ (212451 / 10000) (2124513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685268736 :
    ThetaLowerSegment 1685268736 1685399808 (168522050101327 / 100000)
      (168535105264437 / 100000) := by
  exact
    packedTile65536 1685268736 1685399808 14 6145 41052 31 _ _ (1062259 / 50000) (2124521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685399808 :
    ThetaLowerSegment 1685399808 1685530880 (168535105264437 / 100000)
      (168548022376437 / 100000) := by
  exact
    packedTile65536 1685399808 1685530880 14 6080 41053 31 _ _ (84981 / 4000) (132783 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685530880 :
    ThetaLowerSegment 1685530880 1685661952 (168548022376437 / 100000)
      (168561011771199 / 100000) := by
  exact
    packedTile65536 1685530880 1685661952 14 6114 41055 31 _ _ (2124533 / 100000) (265567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685661952 :
    ThetaLowerSegment 1685661952 1685793024 (168561011771199 / 100000)
      (168573975720381 / 100000) := by
  exact
    packedTile65536 1685661952 1685793024 14 6102 41056 31 _ _ (2124541 / 100000) (66392 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685793024 :
    ThetaLowerSegment 1685793024 1685924096 (168573975720381 / 100000)
      (168586986458457 / 100000) := by
  exact
    packedTile65536 1685793024 1685924096 14 6124 41058 31 _ _ (2124549 / 100000) (265569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1685924096 :
    ThetaLowerSegment 1685924096 1686055168 (168586986458457 / 100000)
      (168600177826661 / 100000) := by
  exact
    packedTile65536 1685924096 1686055168 14 6209 41060 31 _ _ (531139 / 25000) (2124559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686055168 :
    ThetaLowerSegment 1686055168 1686186240 (168600177826661 / 100000)
      (168613360746281 / 100000) := by
  exact
    packedTile65536 1686055168 1686186240 14 6205 41061 31 _ _ (531141 / 25000) (2124567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686186240 :
    ThetaLowerSegment 1686186240 1686317312 (168613360746281 / 100000)
      (168626361002349 / 100000) := by
  exact
    packedTile65536 1686186240 1686317312 14 6119 41063 31 _ _ (531143 / 25000) (84983 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686317312 :
    ThetaLowerSegment 1686317312 1686448384 (168626361002349 / 100000)
      (168639450539729 / 100000) := by
  exact
    packedTile65536 1686317312 1686448384 14 6161 41064 31 _ _ (106229 / 5000) (2124583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686448384 :
    ThetaLowerSegment 1686448384 1686579456 (168639450539729 / 100000)
      (168652561372277 / 100000) := by
  exact
    packedTile65536 1686448384 1686579456 14 6171 41066 31 _ _ (531147 / 25000) (2124591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686579456 :
    ThetaLowerSegment 1686579456 1686710528 (168652561372277 / 100000)
      (168665806097507 / 100000) := by
  exact
    packedTile65536 1686579456 1686710528 14 6234 41067 31 _ _ (424919 / 20000) (1062299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686710528 :
    ThetaLowerSegment 1686710528 1686841600 (168665806097507 / 100000)
      (33735781279921 / 20000) := by
  exact
    packedTile65536 1686710528 1686841600 14 6166 41069 31 _ _ (2124603 / 100000) (1062303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686841600 :
    ThetaLowerSegment 1686841600 1686972672 (33735781279921 / 20000)
      (168692095984693 / 100000) := by
  exact
    packedTile65536 1686841600 1686972672 14 6208 41071 31 _ _ (2124611 / 100000) (1062307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1686972672 :
    ThetaLowerSegment 1686972672 1687103744 (168692095984693 / 100000)
      (84352645996651 / 50000) := by
  exact
    packedTile65536 1686972672 1687103744 14 6211 41072 31 _ _ (2124619 / 100000) (1062311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687103744 :
    ThetaLowerSegment 1687103744 1687234816 (84352645996651 / 50000) (42179560397193 / 25000) := by
  exact
    packedTile65536 1687103744 1687234816 14 6095 41074 31 _ _ (1062313 / 50000) (2124629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687234816 :
    ThetaLowerSegment 1687234816 1687365888 (42179560397193 / 25000) (10545720565613 / 6250) := by
  exact
    packedTile65536 1687234816 1687365888 14 6254 41075 31 _ _ (1062317 / 50000) (2124637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687365888 :
    ThetaLowerSegment 1687365888 1687496960 (10545720565613 / 6250) (21093095165023 / 12500) := by
  exact
    packedTile65536 1687365888 1687496960 14 6228 41077 31 _ _ (1062321 / 50000) (424929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687496960 :
    ThetaLowerSegment 1687496960 1687628032 (21093095165023 / 12500) (21094712023673 / 12500) := by
  exact
    packedTile65536 1687496960 1687628032 14 6088 41079 31 _ _ (42493 / 2000) (2124653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687628032 :
    ThetaLowerSegment 1687628032 1687759104 (21094712023673 / 12500)
      (168770845691557 / 100000) := by
  exact
    packedTile65536 1687628032 1687759104 14 6189 41080 31 _ _ (2124657 / 100000) (106233 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687759104 :
    ThetaLowerSegment 1687759104 1687890176 (168770845691557 / 100000)
      (168784137595797 / 100000) := by
  exact
    packedTile65536 1687759104 1687890176 14 6256 41082 31 _ _ (424933 / 20000) (531167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687890176 :
    ThetaLowerSegment 1687890176 1688021248 (168784137595797 / 100000)
      (84398652097189 / 50000) := by
  exact
    packedTile65536 1687890176 1688021248 14 6197 41083 31 _ _ (2124673 / 100000) (531169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688021248 :
    ThetaLowerSegment 1688021248 1688152320 (84398652097189 / 50000) (5275324093204 / 3125) := by
  exact
    packedTile65536 1688021248 1688152320 14 6150 41085 31 _ _ (2124681 / 100000) (531171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688152320 :
    ThetaLowerSegment 1688152320 1688283392 (5275324093204 / 3125) (168823575924663 / 100000) := by
  exact
    packedTile65536 1688152320 1688283392 14 6215 41087 31 _ _ (2124689 / 100000) (531173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688283392 :
    ThetaLowerSegment 1688283392 1688414464 (168823575924663 / 100000)
      (168836734166991 / 100000) := by
  exact
    packedTile65536 1688283392 1688414464 14 6193 41088 31 _ _ (265587 / 12500) (2124699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688414464 :
    ThetaLowerSegment 1688414464 1688545536 (168836734166991 / 100000)
      (168849900957679 / 100000) := by
  exact
    packedTile65536 1688414464 1688545536 14 6197 41090 31 _ _ (66397 / 3125) (2124707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688545536 :
    ThetaLowerSegment 1688545536 1688676608 (168849900957679 / 100000)
      (168863297266839 / 100000) := by
  exact
    packedTile65536 1688545536 1688676608 14 6305 41091 31 _ _ (265589 / 12500) (424943 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688676608 :
    ThetaLowerSegment 1688676608 1688807680 (168863297266839 / 100000)
      (168876311176839 / 100000) := by
  exact
    packedTile65536 1688676608 1688807680 14 6125 41093 31 _ _ (26559 / 1250) (2124723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688807680 :
    ThetaLowerSegment 1688807680 1688938752 (168876311176839 / 100000)
      (168889361250073 / 100000) := by
  exact
    packedTile65536 1688807680 1688938752 14 6142 41095 31 _ _ (2124727 / 100000) (212473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1688938752 :
    ThetaLowerSegment 1688938752 1689069824 (168889361250073 / 100000)
      (168902330632513 / 100000) := by
  exact
    packedTile65536 1688938752 1689069824 14 6104 41096 31 _ _ (424947 / 20000) (1062369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689069824 :
    ThetaLowerSegment 1689069824 1689200896 (168902330632513 / 100000)
      (42228857418277 / 25000) := by
  exact
    packedTile65536 1689069824 1689200896 14 6165 41098 31 _ _ (2124743 / 100000) (1062373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689200896 :
    ThetaLowerSegment 1689200896 1689331968 (42228857418277 / 25000) (16892852238877 / 10000) := by
  exact
    packedTile65536 1689200896 1689331968 14 6162 41099 31 _ _ (2124751 / 100000) (1062377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689331968 :
    ThetaLowerSegment 1689331968 1689463040 (16892852238877 / 10000) (84470884065071 / 50000) := by
  exact
    packedTile65536 1689331968 1689463040 14 6234 41101 31 _ _ (1062379 / 50000) (2124761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689463040 :
    ThetaLowerSegment 1689463040 1689594112 (84470884065071 / 50000) (42238750824389 / 25000) := by
  exact
    packedTile65536 1689463040 1689594112 14 6229 41103 31 _ _ (1062383 / 50000) (2124769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689594112 :
    ThetaLowerSegment 1689594112 1689725184 (42238750824389 / 25000) (42242003853383 / 25000) := by
  exact
    packedTile65536 1689594112 1689725184 14 6124 41104 31 _ _ (1062387 / 50000) (2124777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689725184 :
    ThetaLowerSegment 1689725184 1689856256 (42242003853383 / 25000) (84490584969447 / 50000) := by
  exact
    packedTile65536 1689725184 1689856256 14 6191 41106 31 _ _ (1062391 / 50000) (424957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689856256 :
    ThetaLowerSegment 1689856256 1689987328 (84490584969447 / 50000)
      (168994286261391 / 100000) := by
  exact
    packedTile65536 1689856256 1689987328 14 6173 41107 31 _ _ (2124789 / 100000) (265599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1689987328 :
    ThetaLowerSegment 1689987328 1690118400 (168994286261391 / 100000)
      (169007175279993 / 100000) := by
  exact
    packedTile65536 1689987328 1690118400 14 6066 41109 31 _ _ (2124797 / 100000) (2656 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690118400 :
    ThetaLowerSegment 1690118400 1690249472 (169007175279993 / 100000) (10563774340143 / 6250) := by
  exact
    packedTile65536 1690118400 1690249472 14 6219 41111 31 _ _ (424961 / 20000) (265601 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690249472 :
    ThetaLowerSegment 1690249472 1690380544 (10563774340143 / 6250) (169033531410693 / 100000) := by
  exact
    packedTile65536 1690249472 1690380544 14 6185 41112 31 _ _ (2124813 / 100000) (132801 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690380544 :
    ThetaLowerSegment 1690380544 1690511616 (169033531410693 / 100000)
      (169046705294693 / 100000) := by
  exact
    packedTile65536 1690380544 1690511616 14 6200 41114 31 _ _ (106241 / 5000) (2124823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690511616 :
    ThetaLowerSegment 1690511616 1690642688 (169046705294693 / 100000)
      (169060021591769 / 100000) := by
  exact
    packedTile65536 1690511616 1690642688 14 6267 41115 31 _ _ (531207 / 25000) (2124831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690642688 :
    ThetaLowerSegment 1690642688 1690773760 (169060021591769 / 100000)
      (169072946969157 / 100000) := by
  exact
    packedTile65536 1690642688 1690773760 14 6083 41117 31 _ _ (531209 / 25000) (2124839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690773760 :
    ThetaLowerSegment 1690773760 1690904832 (169072946969157 / 100000)
      (169086161373993 / 100000) := by
  exact
    packedTile65536 1690773760 1690904832 14 6219 41119 31 _ _ (531211 / 25000) (2124847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1690904832 :
    ThetaLowerSegment 1690904832 1691035904 (169086161373993 / 100000)
      (42274834393761 / 25000) := by
  exact
    packedTile65536 1690904832 1691035904 14 6201 41120 31 _ _ (2124851 / 100000) (1062427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691035904 :
    ThetaLowerSegment 1691035904 1691166976 (42274834393761 / 25000) (84556168731203 / 50000) := by
  exact
    packedTile65536 1691035904 1691166976 14 6118 41122 31 _ _ (2124859 / 100000) (1062431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691166976 :
    ThetaLowerSegment 1691166976 1691298048 (84556168731203 / 50000)
      (169125496763737 / 100000) := by
  exact
    packedTile65536 1691166976 1691298048 14 6193 41123 31 _ _ (2124867 / 100000) (212487 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691298048 :
    ThetaLowerSegment 1691298048 1691429120 (169125496763737 / 100000)
      (169138454251487 / 100000) := by
  exact
    packedTile65536 1691298048 1691429120 14 6098 41125 31 _ _ (16999 / 800) (1062439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691429120 :
    ThetaLowerSegment 1691429120 1691560192 (169138454251487 / 100000)
      (169151581772483 / 100000) := by
  exact
    packedTile65536 1691429120 1691560192 14 6178 41126 31 _ _ (1062441 / 50000) (424977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691560192 :
    ThetaLowerSegment 1691560192 1691691264 (169151581772483 / 100000)
      (169164620097523 / 100000) := by
  exact
    packedTile65536 1691560192 1691691264 14 6136 41128 31 _ _ (212489 / 10000) (2124893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691691264 :
    ThetaLowerSegment 1691691264 1691822336 (169164620097523 / 100000)
      (169177692470019 / 100000) := by
  exact
    packedTile65536 1691691264 1691822336 14 6152 41130 31 _ _ (1062449 / 50000) (2124901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691822336 :
    ThetaLowerSegment 1691822336 1691953408 (169177692470019 / 100000)
      (169190818014381 / 100000) := by
  exact
    packedTile65536 1691822336 1691953408 14 6177 41131 31 _ _ (1062453 / 50000) (2124909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691953408 :
    ThetaLowerSegment 1691953408 1692084480 (169190818014381 / 100000)
      (84601920803079 / 50000) := by
  exact
    packedTile65536 1691953408 1692084480 14 6129 41133 31 _ _ (2124913 / 100000) (531229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692084480 :
    ThetaLowerSegment 1692084480 1692215552 (84601920803079 / 50000) (84608452810233 / 50000) := by
  exact
    packedTile65536 1692084480 1692215552 14 6148 41134 31 _ _ (2124921 / 100000) (531231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692215552 :
    ThetaLowerSegment 1692215552 1692346624 (84608452810233 / 50000)
      (169230065305763 / 100000) := by
  exact
    packedTile65536 1692215552 1692346624 14 6193 41136 31 _ _ (2124929 / 100000) (531233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692346624 :
    ThetaLowerSegment 1692346624 1692477696 (169230065305763 / 100000)
      (169243176167053 / 100000) := by
  exact
    packedTile65536 1692346624 1692477696 14 6170 41138 31 _ _ (2124937 / 100000) (106247 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692477696 :
    ThetaLowerSegment 1692477696 1692608768 (169243176167053 / 100000)
      (169256253072429 / 100000) := by
  exact
    packedTile65536 1692477696 1692608768 14 6154 41139 31 _ _ (132809 / 6250) (2124947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692608768 :
    ThetaLowerSegment 1692608768 1692739840 (169256253072429 / 100000)
      (169269389525693 / 100000) := by
  exact
    packedTile65536 1692608768 1692739840 14 6182 41141 31 _ _ (265619 / 12500) (424991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692739840 :
    ThetaLowerSegment 1692739840 1692870912 (169269389525693 / 100000)
      (169282583402333 / 100000) := by
  exact
    packedTile65536 1692739840 1692870912 14 6209 41142 31 _ _ (13281 / 625) (2124963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1692870912 :
    ThetaLowerSegment 1692870912 1693001984 (169282583402333 / 100000)
      (33859146965857 / 20000) := by
  exact
    packedTile65536 1692870912 1693001984 14 6189 41144 31 _ _ (265621 / 12500) (2124971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693001984 :
    ThetaLowerSegment 1693001984 1693133056 (33859146965857 / 20000) (33861771734977 / 20000) := by
  exact
    packedTile65536 1693001984 1693133056 14 6176 41146 31 _ _ (84999 / 4000) (1062489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693133056 :
    ThetaLowerSegment 1693133056 1693264128 (33861771734977 / 20000) (33864368464203 / 20000) := by
  exact
    packedTile65536 1693133056 1693264128 14 6110 41147 31 _ _ (2124983 / 100000) (1062493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693264128 :
    ThetaLowerSegment 1693264128 1693395200 (33864368464203 / 20000) (84667518195067 / 50000) := by
  exact
    packedTile65536 1693264128 1693395200 14 6209 41149 31 _ _ (2124991 / 100000) (1062497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693395200 :
    ThetaLowerSegment 1693395200 1693526272 (84667518195067 / 50000) (33869637601789 / 20000) := by
  exact
    packedTile65536 1693395200 1693526272 14 6189 41150 31 _ _ (2124999 / 100000) (1062501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693526272 :
    ThetaLowerSegment 1693526272 1693657344 (33869637601789 / 20000) (33872244984151 / 20000) := by
  exact
    packedTile65536 1693526272 1693657344 14 6135 41152 31 _ _ (1062503 / 50000) (2125009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693657344 :
    ThetaLowerSegment 1693657344 1693788416 (33872244984151 / 20000) (33874852376329 / 20000) := by
  exact
    packedTile65536 1693657344 1693788416 14 6135 41154 31 _ _ (1062507 / 50000) (2125017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693788416 :
    ThetaLowerSegment 1693788416 1693919488 (33874852376329 / 20000)
      (169387451893199 / 100000) := by
  exact
    packedTile65536 1693788416 1693919488 14 6207 41155 31 _ _ (1062511 / 50000) (85001 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1693919488 :
    ThetaLowerSegment 1693919488 1694050560 (169387451893199 / 100000)
      (169400493202309 / 100000) := by
  exact
    packedTile65536 1693919488 1694050560 14 6137 41157 31 _ _ (212503 / 10000) (2125033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694050560 :
    ThetaLowerSegment 1694050560 1694181632 (169400493202309 / 100000)
      (169413523929193 / 100000) := by
  exact
    packedTile65536 1694050560 1694181632 14 6132 41158 31 _ _ (2125037 / 100000) (26563 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694181632 :
    ThetaLowerSegment 1694181632 1694312704 (169413523929193 / 100000)
      (21178331822781 / 12500) := by
  exact
    packedTile65536 1694181632 1694312704 14 6179 41160 31 _ _ (425009 / 20000) (265631 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694312704 :
    ThetaLowerSegment 1694312704 1694443776 (21178331822781 / 12500) (1058997661911 / 625) := by
  exact
    packedTile65536 1694312704 1694443776 14 6104 41162 31 _ _ (2125053 / 100000) (66408 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694443776 :
    ThetaLowerSegment 1694443776 1694574848 (1058997661911 / 625) (33890553881609 / 20000) := by
  exact
    packedTile65536 1694443776 1694574848 14 6185 41163 31 _ _ (2125061 / 100000) (265633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694574848 :
    ThetaLowerSegment 1694574848 1694705920 (33890553881609 / 20000) (33893180465657 / 20000) := by
  exact
    packedTile65536 1694574848 1694705920 14 6180 41165 31 _ _ (531267 / 25000) (2125071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694705920 :
    ThetaLowerSegment 1694705920 1694836992 (33893180465657 / 20000)
      (169478986421217 / 100000) := by
  exact
    packedTile65536 1694705920 1694836992 14 6157 41166 31 _ _ (531269 / 25000) (2125079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694836992 :
    ThetaLowerSegment 1694836992 1694968064 (169478986421217 / 100000)
      (169491994060381 / 100000) := by
  exact
    packedTile65536 1694836992 1694968064 14 6121 41168 31 _ _ (531271 / 25000) (2125087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1694968064 :
    ThetaLowerSegment 1694968064 1695099136 (169491994060381 / 100000)
      (169505216376583 / 100000) := by
  exact
    packedTile65536 1694968064 1695099136 14 6222 41169 31 _ _ (2125091 / 100000) (1062547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695099136 :
    ThetaLowerSegment 1695099136 1695230208 (169505216376583 / 100000)
      (33903626545661 / 20000) := by
  exact
    packedTile65536 1695099136 1695230208 14 6078 41171 31 _ _ (2125099 / 100000) (1062551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695230208 :
    ThetaLowerSegment 1695230208 1695361280 (33903626545661 / 20000) (84765559628591 / 50000) := by
  exact
    packedTile65536 1695230208 1695361280 14 6111 41173 31 _ _ (2125107 / 100000) (212511 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695361280 :
    ThetaLowerSegment 1695361280 1695492352 (84765559628591 / 50000)
      (169544275844147 / 100000) := by
  exact
    packedTile65536 1695361280 1695492352 14 6191 41174 31 _ _ (425023 / 20000) (1062559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695492352 :
    ThetaLowerSegment 1695492352 1695623424 (169544275844147 / 100000)
      (169557324093227 / 100000) := by
  exact
    packedTile65536 1695492352 1695623424 14 6140 41176 31 _ _ (1062561 / 50000) (17001 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695623424 :
    ThetaLowerSegment 1695623424 1695754496 (169557324093227 / 100000)
      (169570550902347 / 100000) := by
  exact
    packedTile65536 1695623424 1695754496 14 6224 41177 31 _ _ (212513 / 10000) (2125133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695754496 :
    ThetaLowerSegment 1695754496 1695885568 (169570550902347 / 100000)
      (33916764902859 / 20000) := by
  exact
    packedTile65536 1695754496 1695885568 14 6246 41179 31 _ _ (1062569 / 50000) (2125141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695885568 :
    ThetaLowerSegment 1695885568 1696016640 (33916764902859 / 20000)
      (169596722025369 / 100000) := by
  exact
    packedTile65536 1695885568 1696016640 14 6069 41181 31 _ _ (1062573 / 50000) (2125149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696016640 :
    ThetaLowerSegment 1696016640 1696147712 (169596722025369 / 100000)
      (169609910724887 / 100000) := by
  exact
    packedTile65536 1696016640 1696147712 14 6206 41182 31 _ _ (2125153 / 100000) (531289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696147712 :
    ThetaLowerSegment 1696147712 1696278784 (169609910724887 / 100000) (2120288398087 / 1250) := by
  exact
    packedTile65536 1696147712 1696278784 14 6193 41184 31 _ _ (2125161 / 100000) (531291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696278784 :
    ThetaLowerSegment 1696278784 1696409856 (2120288398087 / 1250) (8481814519907 / 5000) := by
  exact
    packedTile65536 1696278784 1696409856 14 6220 41185 31 _ _ (2125169 / 100000) (531293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696409856 :
    ThetaLowerSegment 1696409856 1696540928 (8481814519907 / 5000) (8482473324777 / 5000) := by
  exact
    packedTile65536 1696409856 1696540928 14 6200 41187 31 _ _ (2125177 / 100000) (106259 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696540928 :
    ThetaLowerSegment 1696540928 1696672000 (8482473324777 / 5000) (42415621343181 / 25000) := by
  exact
    packedTile65536 1696540928 1696672000 14 6126 41189 31 _ _ (66412 / 3125) (2125187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696672000 :
    ThetaLowerSegment 1696672000 1696803072 (42415621343181 / 25000) (42418898920543 / 25000) := by
  exact
    packedTile65536 1696672000 1696803072 14 6169 41190 31 _ _ (265649 / 12500) (425039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696803072 :
    ThetaLowerSegment 1696803072 1696934144 (42418898920543 / 25000) (42422183948443 / 25000) := by
  exact
    packedTile65536 1696803072 1696934144 14 6183 41192 31 _ _ (5313 / 250) (2125203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1696934144 :
    ThetaLowerSegment 1696934144 1697065216 (42422183948443 / 25000) (8485093903693 / 5000) := by
  exact
    packedTile65536 1696934144 1697065216 14 6184 41193 31 _ _ (2125207 / 100000) (212521 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697065216 :
    ThetaLowerSegment 1697065216 1697196288 (8485093903693 / 5000) (8485745069569 / 5000) := by
  exact
    packedTile65536 1697065216 1697196288 14 6128 41195 31 _ _ (425043 / 20000) (1062609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697196288 :
    ThetaLowerSegment 1697196288 1697327360 (8485745069569 / 5000) (42432023693941 / 25000) := by
  exact
    packedTile65536 1697196288 1697327360 14 6208 41197 31 _ _ (2125223 / 100000) (1062613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697327360 :
    ThetaLowerSegment 1697327360 1697458432 (42432023693941 / 25000)
      (169741077811943 / 100000) := by
  exact
    packedTile65536 1697327360 1697458432 14 6109 41198 31 _ _ (2125231 / 100000) (1062617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697458432 :
    ThetaLowerSegment 1697458432 1697589504 (169741077811943 / 100000)
      (169754133148977 / 100000) := by
  exact
    packedTile65536 1697458432 1697589504 14 6143 41200 31 _ _ (1062619 / 50000) (2125241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697589504 :
    ThetaLowerSegment 1697589504 1697720576 (169754133148977 / 100000)
      (33953431331293 / 20000) := by
  exact
    packedTile65536 1697589504 1697720576 14 6128 41201 31 _ _ (1062623 / 50000) (2125249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697720576 :
    ThetaLowerSegment 1697720576 1697851648 (33953431331293 / 20000)
      (169780282225169 / 100000) := by
  exact
    packedTile65536 1697720576 1697851648 14 6176 41203 31 _ _ (1062627 / 50000) (2125257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697851648 :
    ThetaLowerSegment 1697851648 1697982720 (169780282225169 / 100000) (10612083075153 / 6250) := by
  exact
    packedTile65536 1697851648 1697982720 14 6139 41204 31 _ _ (2125261 / 100000) (132829 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1697982720 :
    ThetaLowerSegment 1697982720 1698113792 (10612083075153 / 6250) (33961264194369 / 20000) := by
  exact
    packedTile65536 1697982720 1698113792 14 6113 41206 31 _ _ (2125269 / 100000) (265659 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698113792 :
    ThetaLowerSegment 1698113792 1698244864 (33961264194369 / 20000) (42454884517377 / 25000) := by
  exact
    packedTile65536 1698113792 1698244864 14 6219 41208 31 _ _ (2125277 / 100000) (13283 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698244864 :
    ThetaLowerSegment 1698244864 1698375936 (42454884517377 / 25000)
      (169832869982313 / 100000) := by
  exact
    packedTile65536 1698244864 1698375936 14 6273 41209 31 _ _ (425057 / 20000) (265661 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698375936 :
    ThetaLowerSegment 1698375936 1698507008 (169832869982313 / 100000)
      (169846019163917 / 100000) := by
  exact
    packedTile65536 1698375936 1698507008 14 6187 41211 31 _ _ (531323 / 25000) (425059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698507008 :
    ThetaLowerSegment 1698507008 1698638080 (169846019163917 / 100000)
      (169858953739717 / 100000) := by
  exact
    packedTile65536 1698507008 1698638080 14 6086 41212 31 _ _ (21253 / 1000) (2125303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698638080 :
    ThetaLowerSegment 1698638080 1698769152 (169858953739717 / 100000) (6794881060369 / 4000) := by
  exact
    packedTile65536 1698638080 1698769152 14 6151 41214 31 _ _ (531327 / 25000) (2125311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698769152 :
    ThetaLowerSegment 1698769152 1698900224 (6794881060369 / 4000) (16988508231927 / 10000) := by
  exact
    packedTile65536 1698769152 1698900224 14 6143 41216 31 _ _ (425063 / 20000) (1062659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1698900224 :
    ThetaLowerSegment 1698900224 1699031296 (16988508231927 / 10000)
      (169898167932981 / 100000) := by
  exact
    packedTile65536 1698900224 1699031296 14 6157 41217 31 _ _ (2125323 / 100000) (1062663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699031296 :
    ThetaLowerSegment 1699031296 1699162368 (169898167932981 / 100000)
      (169911026185531 / 100000) := by
  exact
    packedTile65536 1699031296 1699162368 14 6050 41219 31 _ _ (2125331 / 100000) (1062667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699162368 :
    ThetaLowerSegment 1699162368 1699293440 (169911026185531 / 100000)
      (169924105521737 / 100000) := by
  exact
    packedTile65536 1699162368 1699293440 14 6154 41220 31 _ _ (2125339 / 100000) (1062671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699293440 :
    ThetaLowerSegment 1699293440 1699424512 (169924105521737 / 100000)
      (169937223157249 / 100000) := by
  exact
    packedTile65536 1699293440 1699424512 14 6172 41222 31 _ _ (1062673 / 50000) (2125349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699424512 :
    ThetaLowerSegment 1699424512 1699555584 (169937223157249 / 100000)
      (169950340842137 / 100000) := by
  exact
    packedTile65536 1699424512 1699555584 14 6172 41224 31 _ _ (1062677 / 50000) (2125357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699555584 :
    ThetaLowerSegment 1699555584 1699686656 (169950340842137 / 100000)
      (169963532964071 / 100000) := by
  exact
    packedTile65536 1699555584 1699686656 14 6207 41225 31 _ _ (1062681 / 50000) (425073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699686656 :
    ThetaLowerSegment 1699686656 1699817728 (169963532964071 / 100000)
      (169976518968661 / 100000) := by
  exact
    packedTile65536 1699686656 1699817728 14 6110 41227 31 _ _ (2125369 / 100000) (531343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699817728 :
    ThetaLowerSegment 1699817728 1699948800 (169976518968661 / 100000) (4249739591527 / 2500) := by
  exact
    packedTile65536 1699817728 1699948800 14 6147 41228 31 _ _ (2125377 / 100000) (106269 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1699948800 :
    ThetaLowerSegment 1699948800 1700079872 (4249739591527 / 2500) (8500140177789 / 5000) := by
  exact
    packedTile65536 1699948800 1700079872 14 6220 41230 31 _ _ (425077 / 20000) (531347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700079872 :
    ThetaLowerSegment 1700079872 1700210944 (8500140177789 / 5000) (21251996561351 / 12500) := by
  exact
    packedTile65536 1700079872 1700210944 14 6196 41232 31 _ _ (2125393 / 100000) (531349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700210944 :
    ThetaLowerSegment 1700210944 1700342016 (21251996561351 / 12500) (10626825725463 / 6250) := by
  exact
    packedTile65536 1700210944 1700342016 14 6229 41233 31 _ _ (10627 / 500) (2125403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700342016 :
    ThetaLowerSegment 1700342016 1700473088 (10626825725463 / 6250) (10627634044693 / 6250) := by
  exact
    packedTile65536 1700342016 1700473088 14 6085 41235 31 _ _ (66419 / 3125) (2125411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700473088 :
    ThetaLowerSegment 1700473088 1700604160 (10627634044693 / 6250) (4251377053057 / 2500) := by
  exact
    packedTile65536 1700473088 1700604160 14 6087 41236 31 _ _ (265677 / 12500) (2125419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700604160 :
    ThetaLowerSegment 1700604160 1700735232 (4251377053057 / 2500) (42517088315873 / 25000) := by
  exact
    packedTile65536 1700604160 1700735232 14 6244 41238 31 _ _ (2125423 / 100000) (1062713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700735232 :
    ThetaLowerSegment 1700735232 1700866304 (42517088315873 / 25000)
      (170081613827501 / 100000) := by
  exact
    packedTile65536 1700735232 1700866304 14 6239 41239 31 _ _ (2125431 / 100000) (1062717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700866304 :
    ThetaLowerSegment 1700866304 1700997376 (170081613827501 / 100000)
      (85047390461053 / 50000) := by
  exact
    packedTile65536 1700866304 1700997376 14 6195 41241 31 _ _ (2125439 / 100000) (1062721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1700997376 :
    ThetaLowerSegment 1700997376 1701128448 (85047390461053 / 50000) (8505391770879 / 5000) := by
  exact
    packedTile65536 1700997376 1701128448 14 6142 41243 31 _ _ (2125447 / 100000) (42509 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701128448 :
    ThetaLowerSegment 1701128448 1701259520 (8505391770879 / 5000) (85060488549831 / 50000) := by
  exact
    packedTile65536 1701128448 1701259520 14 6183 41244 31 _ _ (1062727 / 50000) (2125457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701259520 :
    ThetaLowerSegment 1701259520 1701390592 (85060488549831 / 50000) (42533515892299 / 25000) := by
  exact
    packedTile65536 1701259520 1701390592 14 6157 41246 31 _ _ (1062731 / 50000) (425093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701390592 :
    ThetaLowerSegment 1701390592 1701521664 (42533515892299 / 25000) (85073617553393 / 50000) := by
  exact
    packedTile65536 1701390592 1701521664 14 6197 41247 31 _ _ (212547 / 10000) (2125473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701521664 :
    ThetaLowerSegment 1701521664 1701652736 (85073617553393 / 50000)
      (170160232398641 / 100000) := by
  exact
    packedTile65536 1701521664 1701652736 14 6115 41249 31 _ _ (2125477 / 100000) (53137 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701652736 :
    ThetaLowerSegment 1701652736 1701783808 (170160232398641 / 100000)
      (170173295629451 / 100000) := by
  exact
    packedTile65536 1701652736 1701783808 14 6146 41251 31 _ _ (425097 / 20000) (132843 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701783808 :
    ThetaLowerSegment 1701783808 1701914880 (170173295629451 / 100000) (6807456226811 / 4000) := by
  exact
    packedTile65536 1701783808 1701914880 14 6168 41252 31 _ _ (2125493 / 100000) (265687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1701914880 :
    ThetaLowerSegment 1701914880 1702045952 (6807456226811 / 4000) (6807971958131 / 4000) := by
  exact
    packedTile65536 1701914880 1702045952 14 6066 41254 31 _ _ (4251 / 200) (2125503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702045952 :
    ThetaLowerSegment 1702045952 1702177024 (6807971958131 / 4000) (34042491169559 / 20000) := by
  exact
    packedTile65536 1702045952 1702177024 14 6190 41255 31 _ _ (531377 / 25000) (2125511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702177024 :
    ThetaLowerSegment 1702177024 1702308096 (34042491169559 / 20000)
      (170225551151871 / 100000) := by
  exact
    packedTile65536 1702177024 1702308096 14 6161 41257 31 _ _ (531379 / 25000) (2125519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702308096 :
    ThetaLowerSegment 1702308096 1702439168 (170225551151871 / 100000)
      (170238682639143 / 100000) := by
  exact
    packedTile65536 1702308096 1702439168 14 6178 41259 31 _ _ (531381 / 25000) (2125527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702439168 :
    ThetaLowerSegment 1702439168 1702570240 (170238682639143 / 100000) (5320368727842 / 3125) := by
  exact
    packedTile65536 1702439168 1702570240 14 6171 41260 31 _ _ (2125531 / 100000) (1062767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702570240 :
    ThetaLowerSegment 1702570240 1702701312 (5320368727842 / 3125) (170264852225943 / 100000) := by
  exact
    packedTile65536 1702570240 1702701312 14 6141 41262 31 _ _ (2125539 / 100000) (1062771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702701312 :
    ThetaLowerSegment 1702701312 1702832384 (170264852225943 / 100000)
      (42569498620761 / 25000) := by
  exact
    packedTile65536 1702701312 1702832384 14 6183 41263 31 _ _ (2125547 / 100000) (42511 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702832384 :
    ThetaLowerSegment 1702832384 1702963456 (42569498620761 / 25000) (85145493997323 / 50000) := by
  exact
    packedTile65536 1702832384 1702963456 14 6113 41265 31 _ _ (1062777 / 50000) (2125557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1702963456 :
    ThetaLowerSegment 1702963456 1703094528 (85145493997323 / 50000) (85152055607217 / 50000) := by
  exact
    packedTile65536 1702963456 1703094528 14 6174 41266 31 _ _ (1062781 / 50000) (425113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703094528 :
    ThetaLowerSegment 1703094528 1703225600 (85152055607217 / 50000) (85158681008907 / 50000) := by
  exact
    packedTile65536 1703094528 1703225600 14 6234 41268 31 _ _ (212557 / 10000) (2125573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703225600 :
    ThetaLowerSegment 1703225600 1703356672 (85158681008907 / 50000) (21291303226757 / 12500) := by
  exact
    packedTile65536 1703225600 1703356672 14 6146 41270 31 _ _ (2125577 / 100000) (106279 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703356672 :
    ThetaLowerSegment 1703356672 1703487744 (21291303226757 / 12500)
      (170343593813131 / 100000) := by
  exact
    packedTile65536 1703356672 1703487744 14 6195 41271 31 _ _ (425117 / 20000) (531397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703487744 :
    ThetaLowerSegment 1703487744 1703618816 (170343593813131 / 100000)
      (170356632200593 / 100000) := by
  exact
    packedTile65536 1703487744 1703618816 14 6134 41273 31 _ _ (2125593 / 100000) (531399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703618816 :
    ThetaLowerSegment 1703618816 1703749888 (170356632200593 / 100000)
      (170369640878713 / 100000) := by
  exact
    packedTile65536 1703618816 1703749888 14 6120 41274 31 _ _ (2125601 / 100000) (531401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703749888 :
    ThetaLowerSegment 1703749888 1703880960 (170369640878713 / 100000)
      (170382832401961 / 100000) := by
  exact
    packedTile65536 1703749888 1703880960 14 6206 41276 31 _ _ (265701 / 12500) (2125611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1703880960 :
    ThetaLowerSegment 1703880960 1704012032 (170382832401961 / 100000)
      (34079178437333 / 20000) := by
  exact
    packedTile65536 1703880960 1704012032 14 6144 41278 31 _ _ (132851 / 6250) (2125619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704012032 :
    ThetaLowerSegment 1704012032 1704143104 (34079178437333 / 20000)
      (170409066804217 / 100000) := by
  exact
    packedTile65536 1704012032 1704143104 14 6198 41279 31 _ _ (265703 / 12500) (2125627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704143104 :
    ThetaLowerSegment 1704143104 1704274176 (170409066804217 / 100000)
      (170422360500491 / 100000) := by
  exact
    packedTile65536 1704143104 1704274176 14 6254 41281 31 _ _ (2125631 / 100000) (1062817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704274176 :
    ThetaLowerSegment 1704274176 1704405248 (170422360500491 / 100000)
      (170435420426507 / 100000) := by
  exact
    packedTile65536 1704274176 1704405248 14 6144 41282 31 _ _ (2125639 / 100000) (1062821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704405248 :
    ThetaLowerSegment 1704405248 1704536320 (170435420426507 / 100000)
      (170448510160733 / 100000) := by
  exact
    packedTile65536 1704405248 1704536320 14 6158 41284 31 _ _ (2125647 / 100000) (42513 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704536320 :
    ThetaLowerSegment 1704536320 1704667392 (170448510160733 / 100000)
      (34092298731073 / 20000) := by
  exact
    packedTile65536 1704536320 1704667392 14 6108 41286 31 _ _ (1062827 / 50000) (2125657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704667392 :
    ThetaLowerSegment 1704667392 1704798464 (34092298731073 / 20000)
      (170474698267709 / 100000) := by
  exact
    packedTile65536 1704667392 1704798464 14 6212 41287 31 _ _ (1062831 / 50000) (425133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704798464 :
    ThetaLowerSegment 1704798464 1704929536 (170474698267709 / 100000)
      (170487862542019 / 100000) := by
  exact
    packedTile65536 1704798464 1704929536 14 6193 41289 31 _ _ (212567 / 10000) (2125673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704929536 :
    ThetaLowerSegment 1704929536 1705060608 (170487862542019 / 100000)
      (170500939706923 / 100000) := by
  exact
    packedTile65536 1704929536 1705060608 14 6152 41290 31 _ _ (2125677 / 100000) (26571 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705060608 :
    ThetaLowerSegment 1705060608 1705191680 (170500939706923 / 100000)
      (170514059434743 / 100000) := by
  exact
    packedTile65536 1705060608 1705191680 14 6172 41292 31 _ _ (425137 / 20000) (265711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705191680 :
    ThetaLowerSegment 1705191680 1705322752 (170514059434743 / 100000)
      (170527383278467 / 100000) := by
  exact
    packedTile65536 1705191680 1705322752 14 6268 41293 31 _ _ (2125693 / 100000) (66428 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705322752 :
    ThetaLowerSegment 1705322752 1705339136 (170527383278467 / 100000)
      (42632243857129 / 25000) := by
  exact
    packedTile65536 1705322752 1705339136 11 749 41295 31 _ _ (2125701 / 100000) (265713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1705339136 :
    ThetaLowerSegment 1705339136 1705341184 (42632243857129 / 25000) (85264617382019 / 50000) := by
  exact
    packedTile65536 1705339136 1705341184 8 122 41295 31 _ _ (2125701 / 100000) (265713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1673341184_1705341184 :
    ThetaLowerSegment 1673341184 1705341184 (167328895060343 / 100000)
      (85264617382019 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1673341184 cell1673472256)
                  (ThetaLowerSegment.join cell1673603328 cell1673734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1673865472 cell1673996544)
                  (ThetaLowerSegment.join cell1674127616 cell1674258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1674389760 cell1674520832)
                  (ThetaLowerSegment.join cell1674651904 cell1674782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1674914048 cell1675045120)
                  (ThetaLowerSegment.join cell1675176192 cell1675307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1675438336 cell1675569408)
                  (ThetaLowerSegment.join cell1675700480 cell1675831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1675962624 cell1676093696)
                  (ThetaLowerSegment.join cell1676224768 cell1676355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1676486912 cell1676617984)
                  (ThetaLowerSegment.join cell1676749056 cell1676880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1677011200 cell1677142272)
                  (ThetaLowerSegment.join cell1677273344 cell1677404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1677535488 cell1677666560)
                  (ThetaLowerSegment.join cell1677797632 cell1677928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1678059776 cell1678190848)
                  (ThetaLowerSegment.join cell1678321920 cell1678452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1678584064 cell1678715136)
                  (ThetaLowerSegment.join cell1678846208 cell1678977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1679108352 cell1679239424)
                  (ThetaLowerSegment.join cell1679370496 cell1679501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1679632640 cell1679763712)
                  (ThetaLowerSegment.join cell1679894784 cell1680025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1680156928 cell1680288000)
                  (ThetaLowerSegment.join cell1680419072 cell1680550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1680681216 cell1680812288)
                  (ThetaLowerSegment.join cell1680943360 cell1681074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1681205504 cell1681336576)
                  (ThetaLowerSegment.join cell1681467648 cell1681598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1681729792 cell1681860864)
                  (ThetaLowerSegment.join cell1681991936 cell1682123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1682254080 cell1682385152)
                  (ThetaLowerSegment.join cell1682516224 cell1682647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1682778368 cell1682909440)
                  (ThetaLowerSegment.join cell1683040512 cell1683171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1683302656 cell1683433728)
                  (ThetaLowerSegment.join cell1683564800 cell1683695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1683826944 cell1683958016)
                  (ThetaLowerSegment.join cell1684089088 cell1684220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1684351232 cell1684482304)
                  (ThetaLowerSegment.join cell1684613376 cell1684744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1684875520 cell1685006592)
                  (ThetaLowerSegment.join cell1685137664 cell1685268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1685399808 cell1685530880)
                  (ThetaLowerSegment.join cell1685661952 cell1685793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1685924096 cell1686055168)
                  (ThetaLowerSegment.join cell1686186240 cell1686317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1686448384 cell1686579456)
                  (ThetaLowerSegment.join cell1686710528 cell1686841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1686972672 cell1687103744)
                  (ThetaLowerSegment.join cell1687234816 cell1687365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1687496960 cell1687628032)
                  (ThetaLowerSegment.join cell1687759104 cell1687890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1688021248 cell1688152320)
                  (ThetaLowerSegment.join cell1688283392 cell1688414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1688545536 cell1688676608)
                  (ThetaLowerSegment.join cell1688807680 cell1688938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1689069824 cell1689200896)
                  (ThetaLowerSegment.join cell1689331968 cell1689463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1689594112 cell1689725184)
                  (ThetaLowerSegment.join cell1689856256 cell1689987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1690118400 cell1690249472)
                  (ThetaLowerSegment.join cell1690380544 cell1690511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1690642688 cell1690773760)
                  (ThetaLowerSegment.join cell1690904832 cell1691035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1691166976 cell1691298048)
                  (ThetaLowerSegment.join cell1691429120 cell1691560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1691691264 cell1691822336)
                  (ThetaLowerSegment.join cell1691953408 cell1692084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1692215552 cell1692346624)
                  (ThetaLowerSegment.join cell1692477696 cell1692608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1692739840 cell1692870912)
                  (ThetaLowerSegment.join cell1693001984 cell1693133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1693264128 cell1693395200)
                  (ThetaLowerSegment.join cell1693526272 cell1693657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1693788416 cell1693919488)
                  (ThetaLowerSegment.join cell1694050560 cell1694181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1694312704 cell1694443776)
                  (ThetaLowerSegment.join cell1694574848 cell1694705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1694836992 cell1694968064)
                  (ThetaLowerSegment.join cell1695099136 cell1695230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1695361280 cell1695492352)
                  (ThetaLowerSegment.join cell1695623424 cell1695754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1695885568 cell1696016640)
                  (ThetaLowerSegment.join cell1696147712 cell1696278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1696409856 cell1696540928)
                  (ThetaLowerSegment.join cell1696672000 cell1696803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1696934144 cell1697065216)
                  (ThetaLowerSegment.join cell1697196288 cell1697327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1697458432 cell1697589504)
                  (ThetaLowerSegment.join cell1697720576 cell1697851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1697982720 cell1698113792)
                  (ThetaLowerSegment.join cell1698244864 cell1698375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1698507008 cell1698638080)
                  (ThetaLowerSegment.join cell1698769152 cell1698900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1699031296 cell1699162368)
                  (ThetaLowerSegment.join cell1699293440 cell1699424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1699555584 cell1699686656)
                  (ThetaLowerSegment.join cell1699817728 cell1699948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1700079872 cell1700210944)
                  (ThetaLowerSegment.join cell1700342016 cell1700473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1700604160 cell1700735232)
                  (ThetaLowerSegment.join cell1700866304 cell1700997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1701128448 cell1701259520)
                  (ThetaLowerSegment.join cell1701390592 cell1701521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1701652736 cell1701783808)
                  (ThetaLowerSegment.join cell1701914880 cell1702045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1702177024 cell1702308096)
                  (ThetaLowerSegment.join cell1702439168 cell1702570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1702701312 cell1702832384)
                  (ThetaLowerSegment.join cell1702963456 cell1703094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1703225600 cell1703356672)
                  (ThetaLowerSegment.join cell1703487744 cell1703618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1703749888 cell1703880960)
                  (ThetaLowerSegment.join cell1704012032 cell1704143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1704274176 cell1704405248)
                  (ThetaLowerSegment.join cell1704536320 cell1704667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1704798464 cell1704929536)
                (ThetaLowerSegment.join cell1705060608 cell1705191680))
              (ThetaLowerSegment.join cell1705322752 cell1705339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
