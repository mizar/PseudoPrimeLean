/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis16384

/-! # Direct theta estimate up to 88412416 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell71139584 :
    ThetaLowerSegment 71139584 71155968 (7112973541849 / 100000) (7114618834589 / 100000) := by
  exact
    packedTile16384 71139584 71155968 11 910 8434 26 _ _ (904007 / 50000) (1808017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71155968 :
    ThetaLowerSegment 71155968 71172352 (7114618834589 / 100000) (7116238835741 / 100000) := by
  exact
    packedTile16384 71155968 71172352 11 896 8435 26 _ _ (1808037 / 100000) (45201 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71172352 :
    ThetaLowerSegment 71172352 71188736 (7116238835741 / 100000) (7117800999581 / 100000) := by
  exact
    packedTile16384 71172352 71188736 11 864 8436 26 _ _ (90403 / 5000) (1808063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71188736 :
    ThetaLowerSegment 71188736 71205120 (7117800999581 / 100000) (1779868369089 / 25000) := by
  exact
    packedTile16384 71188736 71205120 11 925 8437 26 _ _ (1808083 / 100000) (904043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71205120 :
    ThetaLowerSegment 71205120 71221504 (1779868369089 / 25000) (1780275192939 / 25000) := by
  exact
    packedTile16384 71205120 71221504 11 900 8438 26 _ _ (904053 / 50000) (1808109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71221504 :
    ThetaLowerSegment 71221504 71237888 (1780275192939 / 25000) (1424560444229 / 20000) := by
  exact
    packedTile16384 71221504 71237888 11 941 8439 26 _ _ (1808129 / 100000) (452033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71237888 :
    ThetaLowerSegment 71237888 71254272 (1424560444229 / 20000) (7124398819361 / 100000) := by
  exact
    packedTile16384 71237888 71254272 11 883 8440 26 _ _ (226019 / 12500) (361631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71254272 :
    ThetaLowerSegment 71254272 71270656 (7124398819361 / 100000) (7126047874961 / 100000) := by
  exact
    packedTile16384 71254272 71270656 11 912 8441 26 _ _ (72327 / 4000) (904089 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71270656 :
    ThetaLowerSegment 71270656 71287040 (7126047874961 / 100000) (1425537943749 / 20000) := by
  exact
    packedTile16384 71270656 71287040 11 908 8442 26 _ _ (904099 / 50000) (1808201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71287040 :
    ThetaLowerSegment 71287040 71303424 (1425537943749 / 20000) (3564666695817 / 50000) := by
  exact
    packedTile16384 71287040 71303424 11 909 8443 26 _ _ (1808221 / 100000) (56507 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71303424 :
    ThetaLowerSegment 71303424 71319808 (3564666695817 / 50000) (3565483117983 / 50000) := by
  exact
    packedTile16384 71303424 71319808 11 903 8444 26 _ _ (452061 / 25000) (1808247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71319808 :
    ThetaLowerSegment 71319808 71336192 (3565483117983 / 50000) (7132548469591 / 100000) := by
  exact
    packedTile16384 71319808 71336192 11 875 8445 26 _ _ (1808267 / 100000) (180827 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71336192 :
    ThetaLowerSegment 71336192 71352576 (7132548469591 / 100000) (7134215712971 / 100000) := by
  exact
    packedTile16384 71336192 71352576 11 922 8446 26 _ _ (180829 / 10000) (1808293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71352576 :
    ThetaLowerSegment 71352576 71368960 (7134215712971 / 100000) (713584861961 / 10000) := by
  exact
    packedTile16384 71352576 71368960 11 903 8447 26 _ _ (1808313 / 100000) (452079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71368960 :
    ThetaLowerSegment 71368960 71385344 (713584861961 / 10000) (3568750719357 / 50000) := by
  exact
    packedTile16384 71368960 71385344 11 914 8448 26 _ _ (113021 / 6250) (1808339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71385344 :
    ThetaLowerSegment 71385344 71401728 (3568750719357 / 50000) (7139105453147 / 100000) := by
  exact
    packedTile16384 71385344 71401728 11 887 8448 26 _ _ (1808359 / 100000) (904181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71401728 :
    ThetaLowerSegment 71401728 71418112 (7139105453147 / 100000) (7140817990901 / 100000) := by
  exact
    packedTile16384 71401728 71418112 11 947 8449 26 _ _ (904191 / 50000) (361677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71418112 :
    ThetaLowerSegment 71418112 71434496 (7140817990901 / 100000) (7142514274791 / 100000) := by
  exact
    packedTile16384 71418112 71434496 11 938 8450 26 _ _ (361681 / 20000) (226051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71434496 :
    ThetaLowerSegment 71434496 71467264 (7142514274791 / 100000) (7145834548599 / 100000) := by
  exact
    packedTile16384 71434496 71467264 12 1836 8451 26 _ _ (452107 / 25000) (1808431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71467264 :
    ThetaLowerSegment 71467264 71500032 (7145834548599 / 100000) (7149077142481 / 100000) := by
  exact
    packedTile16384 71467264 71500032 12 1793 8453 26 _ _ (904237 / 50000) (1808477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71500032 :
    ThetaLowerSegment 71500032 71532800 (7149077142481 / 100000) (1788099847971 / 25000) := by
  exact
    packedTile16384 71500032 71532800 12 1837 8455 26 _ _ (1808519 / 100000) (904261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71532800 :
    ThetaLowerSegment 71532800 71565568 (1788099847971 / 25000) (7155671085969 / 100000) := by
  exact
    packedTile16384 71532800 71565568 12 1809 8457 26 _ _ (361713 / 20000) (226071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71565568 :
    ThetaLowerSegment 71565568 71598336 (7155671085969 / 100000) (223718094859 / 3125) := by
  exact
    packedTile16384 71565568 71598336 12 1829 8459 26 _ _ (1808611 / 100000) (904307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71598336 :
    ThetaLowerSegment 71598336 71631104 (223718094859 / 3125) (7162283451827 / 100000) := by
  exact
    packedTile16384 71598336 71631104 12 1827 8461 26 _ _ (1808657 / 100000) (90433 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71631104 :
    ThetaLowerSegment 71631104 71663872 (7162283451827 / 100000) (286621492269 / 4000) := by
  exact
    packedTile16384 71631104 71663872 12 1799 8463 26 _ _ (904351 / 50000) (361741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71663872 :
    ThetaLowerSegment 71663872 71696640 (286621492269 / 4000) (7168809331857 / 100000) := by
  exact
    packedTile16384 71663872 71696640 12 1809 8465 26 _ _ (452187 / 25000) (1808751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71696640 :
    ThetaLowerSegment 71696640 71729408 (7168809331857 / 100000) (7172010897237 / 100000) := by
  exact
    packedTile16384 71696640 71729408 12 1770 8467 26 _ _ (904397 / 50000) (1808797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71729408 :
    ThetaLowerSegment 71729408 71762176 (7172010897237 / 100000) (7175293941837 / 100000) := by
  exact
    packedTile16384 71729408 71762176 12 1815 8469 26 _ _ (45221 / 2500) (1808843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71762176 :
    ThetaLowerSegment 71762176 71794944 (7175293941837 / 100000) (3589210752001 / 50000) := by
  exact
    packedTile16384 71762176 71794944 12 1729 8471 26 _ _ (361777 / 20000) (226111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71794944 :
    ThetaLowerSegment 71794944 71811328 (3589210752001 / 50000) (7180083911591 / 100000) := by
  exact
    packedTile16384 71794944 71811328 11 919 8473 26 _ _ (1808931 / 100000) (904467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71811328 :
    ThetaLowerSegment 71811328 71827712 (7180083911591 / 100000) (7181778901489 / 100000) := by
  exact
    packedTile16384 71811328 71827712 11 937 8474 26 _ _ (904477 / 50000) (1808957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71827712 :
    ThetaLowerSegment 71827712 71844096 (7181778901489 / 100000) (3591693541021 / 50000) := by
  exact
    packedTile16384 71827712 71844096 11 889 8475 26 _ _ (1808977 / 100000) (90449 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71844096 :
    ThetaLowerSegment 71844096 71860480 (3591693541021 / 50000) (898130063391 / 12500) := by
  exact
    packedTile16384 71844096 71860480 11 914 8476 26 _ _ (1808999 / 100000) (904501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71860480 :
    ThetaLowerSegment 71860480 71876864 (898130063391 / 12500) (3593349690151 / 50000) := by
  exact
    packedTile16384 71860480 71876864 11 917 8477 26 _ _ (904511 / 50000) (72361 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71876864 :
    ThetaLowerSegment 71876864 71893248 (3593349690151 / 50000) (7188332947937 / 100000) := by
  exact
    packedTile16384 71876864 71893248 11 903 8478 26 _ _ (361809 / 20000) (226131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71893248 :
    ThetaLowerSegment 71893248 71909632 (7188332947937 / 100000) (1437996201777 / 20000) := by
  exact
    packedTile16384 71893248 71909632 11 911 8478 26 _ _ (452267 / 25000) (1809071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71909632 :
    ThetaLowerSegment 71909632 71926016 (1437996201777 / 20000) (1797906368151 / 25000) := by
  exact
    packedTile16384 71909632 71926016 11 909 8479 26 _ _ (1809091 / 100000) (904547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71926016 :
    ThetaLowerSegment 71926016 71942400 (1797906368151 / 25000) (35966196007 / 500) := by
  exact
    packedTile16384 71926016 71942400 11 892 8480 26 _ _ (1809113 / 100000) (452279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71942400 :
    ThetaLowerSegment 71942400 71958784 (35966196007 / 500) (899359784827 / 12500) := by
  exact
    packedTile16384 71942400 71958784 11 906 8481 26 _ _ (113071 / 6250) (1809139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71958784 :
    ThetaLowerSegment 71958784 71975168 (899359784827 / 12500) (7196519185829 / 100000) := by
  exact
    packedTile16384 71958784 71975168 11 907 8482 26 _ _ (1809159 / 100000) (904581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71975168 :
    ThetaLowerSegment 71975168 71991552 (7196519185829 / 100000) (7198105838443 / 100000) := by
  exact
    packedTile16384 71975168 71991552 11 877 8483 26 _ _ (904591 / 50000) (361837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell71991552 :
    ThetaLowerSegment 71991552 72007936 (7198105838443 / 100000) (7199743168063 / 100000) := by
  exact
    packedTile16384 71991552 72007936 11 905 8484 26 _ _ (452301 / 25000) (1809207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72007936 :
    ThetaLowerSegment 72007936 72024320 (7199743168063 / 100000) (7201367853909 / 100000) := by
  exact
    packedTile16384 72007936 72024320 11 898 8485 26 _ _ (1809227 / 100000) (180923 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72024320 :
    ThetaLowerSegment 72024320 72040704 (7201367853909 / 100000) (7203023317659 / 100000) := by
  exact
    packedTile16384 72024320 72040704 11 915 8486 26 _ _ (7237 / 400) (1809253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72040704 :
    ThetaLowerSegment 72040704 72057088 (7203023317659 / 100000) (3602361112503 / 50000) := by
  exact
    packedTile16384 72040704 72057088 11 939 8487 26 _ _ (1809273 / 100000) (452319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72057088 :
    ThetaLowerSegment 72057088 72073472 (3602361112503 / 50000) (7206363255571 / 100000) := by
  exact
    packedTile16384 72057088 72073472 11 907 8488 26 _ _ (361859 / 20000) (904649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72073472 :
    ThetaLowerSegment 72073472 72089856 (7206363255571 / 100000) (7208011544269 / 100000) := by
  exact
    packedTile16384 72073472 72089856 11 911 8489 26 _ _ (904659 / 50000) (1809321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72089856 :
    ThetaLowerSegment 72089856 72106240 (7208011544269 / 100000) (7209672519307 / 100000) := by
  exact
    packedTile16384 72089856 72106240 11 918 8490 26 _ _ (1809341 / 100000) (56542 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72106240 :
    ThetaLowerSegment 72106240 72139008 (7209672519307 / 100000) (7212943849419 / 100000) := by
  exact
    packedTile16384 72106240 72139008 12 1808 8491 26 _ _ (452341 / 25000) (1809367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72139008 :
    ThetaLowerSegment 72139008 72171776 (7212943849419 / 100000) (902029847901 / 12500) := by
  exact
    packedTile16384 72139008 72171776 12 1821 8493 26 _ _ (1809409 / 100000) (452353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72171776 :
    ThetaLowerSegment 72171776 72204544 (902029847901 / 12500) (3609808516913 / 50000) := by
  exact
    packedTile16384 72171776 72204544 12 1867 8495 26 _ _ (904727 / 50000) (1809457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72204544 :
    ThetaLowerSegment 72204544 72237312 (3609808516913 / 50000) (3611466018913 / 50000) := by
  exact
    packedTile16384 72204544 72237312 12 1832 8497 26 _ _ (3619 / 200) (1809503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72237312 :
    ThetaLowerSegment 72237312 72270080 (3611466018913 / 50000) (7226223600181 / 100000) := by
  exact
    packedTile16384 72237312 72270080 12 1819 8499 26 _ _ (361909 / 20000) (452387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72270080 :
    ThetaLowerSegment 72270080 72302848 (7226223600181 / 100000) (7229571343531 / 100000) := by
  exact
    packedTile16384 72270080 72302848 12 1850 8501 26 _ _ (1809591 / 100000) (904797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72302848 :
    ThetaLowerSegment 72302848 72335616 (7229571343531 / 100000) (1446570804647 / 20000) := by
  exact
    packedTile16384 72302848 72335616 12 1814 8503 26 _ _ (452409 / 25000) (1809639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72335616 :
    ThetaLowerSegment 72335616 72368384 (1446570804647 / 20000) (7236100590949 / 100000) := by
  exact
    packedTile16384 72335616 72368384 12 1794 8505 26 _ _ (1809681 / 100000) (452421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72368384 :
    ThetaLowerSegment 72368384 72401152 (7236100590949 / 100000) (7239379816273 / 100000) := by
  exact
    packedTile16384 72368384 72401152 12 1812 8506 26 _ _ (1809727 / 100000) (180973 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72401152 :
    ThetaLowerSegment 72401152 72433920 (7239379816273 / 100000) (7242624737469 / 100000) := by
  exact
    packedTile16384 72401152 72433920 12 1793 8508 26 _ _ (452443 / 25000) (72391 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72433920 :
    ThetaLowerSegment 72433920 72466688 (7242624737469 / 100000) (1449175757687 / 20000) := by
  exact
    packedTile16384 72433920 72466688 12 1798 8510 26 _ _ (1809817 / 100000) (90491 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72466688 :
    ThetaLowerSegment 72466688 72499456 (1449175757687 / 20000) (7249107582243 / 100000) := by
  exact
    packedTile16384 72466688 72499456 12 1784 8512 26 _ _ (904931 / 50000) (361973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72499456 :
    ThetaLowerSegment 72499456 72532224 (7249107582243 / 100000) (290096498897 / 4000) := by
  exact
    packedTile16384 72499456 72532224 12 1826 8514 26 _ _ (1809907 / 100000) (180991 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72532224 :
    ThetaLowerSegment 72532224 72564992 (290096498897 / 4000) (7255786224817 / 100000) := by
  exact
    packedTile16384 72532224 72564992 12 1864 8516 26 _ _ (1809953 / 100000) (452489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72564992 :
    ThetaLowerSegment 72564992 72597760 (7255786224817 / 100000) (7258977251291 / 100000) := by
  exact
    packedTile16384 72564992 72597760 12 1763 8518 26 _ _ (904999 / 50000) (1810001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72597760 :
    ThetaLowerSegment 72597760 72630528 (7258977251291 / 100000) (3631118569367 / 50000) := by
  exact
    packedTile16384 72597760 72630528 12 1801 8520 26 _ _ (1810043 / 100000) (905023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72630528 :
    ThetaLowerSegment 72630528 72663296 (3631118569367 / 50000) (3632742218303 / 50000) := by
  exact
    packedTile16384 72630528 72663296 12 1794 8522 26 _ _ (226261 / 12500) (1810091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72663296 :
    ThetaLowerSegment 72663296 72696064 (3632742218303 / 50000) (7268769828001 / 100000) := by
  exact
    packedTile16384 72663296 72696064 12 1815 8524 26 _ _ (1810133 / 100000) (226267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72696064 :
    ThetaLowerSegment 72696064 72728832 (7268769828001 / 100000) (1454415766677 / 20000) := by
  exact
    packedTile16384 72696064 72728832 12 1828 8526 26 _ _ (905089 / 50000) (1810181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72728832 :
    ThetaLowerSegment 72728832 72761600 (1454415766677 / 20000) (7275311891663 / 100000) := by
  exact
    packedTile16384 72728832 72761600 12 1786 8528 26 _ _ (1810223 / 100000) (905113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72761600 :
    ThetaLowerSegment 72761600 72794368 (7275311891663 / 100000) (7278519686559 / 100000) := by
  exact
    packedTile16384 72761600 72794368 12 1772 8530 26 _ _ (452567 / 25000) (1810271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72794368 :
    ThetaLowerSegment 72794368 72827136 (7278519686559 / 100000) (3640946149839 / 50000) := by
  exact
    packedTile16384 72794368 72827136 12 1863 8531 26 _ _ (1810313 / 100000) (452579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72827136 :
    ThetaLowerSegment 72827136 72859904 (3640946149839 / 50000) (3642611679199 / 50000) := by
  exact
    packedTile16384 72827136 72859904 12 1840 8533 26 _ _ (905179 / 50000) (1810361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72859904 :
    ThetaLowerSegment 72859904 72892672 (3642611679199 / 50000) (911057997471 / 12500) := by
  exact
    packedTile16384 72859904 72892672 12 1790 8535 26 _ _ (1810403 / 100000) (905203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72892672 :
    ThetaLowerSegment 72892672 72925440 (911057997471 / 12500) (182293929617 / 2500) := by
  exact
    packedTile16384 72892672 72925440 12 1819 8537 26 _ _ (113153 / 6250) (1810451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72925440 :
    ThetaLowerSegment 72925440 72958208 (182293929617 / 2500) (911878819503 / 12500) := by
  exact
    packedTile16384 72925440 72958208 12 1808 8539 26 _ _ (1810493 / 100000) (56578 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72958208 :
    ThetaLowerSegment 72958208 72990976 (911878819503 / 12500) (912291622167 / 12500) := by
  exact
    packedTile16384 72958208 72990976 12 1824 8541 26 _ _ (905269 / 50000) (1810541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell72990976 :
    ThetaLowerSegment 72990976 73023744 (912291622167 / 12500) (7301644533643 / 100000) := by
  exact
    packedTile16384 72990976 73023744 12 1829 8543 26 _ _ (1810583 / 100000) (905293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73023744 :
    ThetaLowerSegment 73023744 73056512 (7301644533643 / 100000) (7304945308487 / 100000) := by
  exact
    packedTile16384 73023744 73056512 12 1823 8545 26 _ _ (452657 / 25000) (1810631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73056512 :
    ThetaLowerSegment 73056512 73089280 (7304945308487 / 100000) (730818822383 / 10000) := by
  exact
    packedTile16384 73056512 73089280 12 1791 8547 26 _ _ (1810673 / 100000) (452669 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73089280 :
    ThetaLowerSegment 73089280 73122048 (730818822383 / 10000) (913928902471 / 12500) := by
  exact
    packedTile16384 73089280 73122048 12 1791 8549 26 _ _ (905359 / 50000) (1810721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73122048 :
    ThetaLowerSegment 73122048 73154816 (913928902471 / 12500) (3657347107347 / 50000) := by
  exact
    packedTile16384 73122048 73154816 12 1802 8551 26 _ _ (1810763 / 100000) (905383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73154816 :
    ThetaLowerSegment 73154816 73187584 (3657347107347 / 50000) (7317883045821 / 100000) := by
  exact
    packedTile16384 73154816 73187584 12 1761 8553 26 _ _ (1810807 / 100000) (181081 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73187584 :
    ThetaLowerSegment 73187584 73220352 (7317883045821 / 100000) (7321171553053 / 100000) := by
  exact
    packedTile16384 73187584 73220352 12 1816 8554 26 _ _ (452713 / 25000) (362171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73220352 :
    ThetaLowerSegment 73220352 73253120 (7321171553053 / 100000) (7324449276623 / 100000) := by
  exact
    packedTile16384 73220352 73253120 12 1810 8556 26 _ _ (1810897 / 100000) (18109 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73253120 :
    ThetaLowerSegment 73253120 73285888 (7324449276623 / 100000) (7327714405049 / 100000) := by
  exact
    packedTile16384 73253120 73285888 12 1803 8558 26 _ _ (905471 / 50000) (362189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73285888 :
    ThetaLowerSegment 73285888 73318656 (7327714405049 / 100000) (7331035753373 / 100000) := by
  exact
    packedTile16384 73285888 73318656 12 1834 8560 26 _ _ (905493 / 50000) (1810989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73318656 :
    ThetaLowerSegment 73318656 73351424 (7331035753373 / 100000) (7334320963607 / 100000) := by
  exact
    packedTile16384 73318656 73351424 12 1814 8562 26 _ _ (1811031 / 100000) (905517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73351424 :
    ThetaLowerSegment 73351424 73384192 (7334320963607 / 100000) (7337599011167 / 100000) := by
  exact
    packedTile16384 73351424 73384192 12 1810 8564 26 _ _ (452769 / 25000) (1811079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73384192 :
    ThetaLowerSegment 73384192 73416960 (7337599011167 / 100000) (7340813749167 / 100000) := by
  exact
    packedTile16384 73384192 73416960 12 1775 8566 26 _ _ (22639 / 1250) (1811123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73416960 :
    ThetaLowerSegment 73416960 73449728 (7340813749167 / 100000) (3672043262161 / 50000) := by
  exact
    packedTile16384 73416960 73449728 12 1807 8568 26 _ _ (362233 / 20000) (56599 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73449728 :
    ThetaLowerSegment 73449728 73482496 (3672043262161 / 50000) (3673662483901 / 50000) := by
  exact
    packedTile16384 73449728 73482496 12 1788 8570 26 _ _ (181121 / 10000) (1811213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73482496 :
    ThetaLowerSegment 73482496 73515264 (3673662483901 / 50000) (459412595393 / 6250) := by
  exact
    packedTile16384 73482496 73515264 12 1809 8572 26 _ _ (905627 / 50000) (1811257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73515264 :
    ThetaLowerSegment 73515264 73548032 (459412595393 / 6250) (3676950856533 / 50000) := by
  exact
    packedTile16384 73515264 73548032 12 1822 8574 26 _ _ (1811299 / 100000) (905651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73548032 :
    ThetaLowerSegment 73548032 73580800 (3676950856533 / 50000) (7357254508959 / 100000) := by
  exact
    packedTile16384 73548032 73580800 12 1851 8576 26 _ _ (1811343 / 100000) (905673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73580800 :
    ThetaLowerSegment 73580800 73613568 (7357254508959 / 100000) (7360520441523 / 100000) := by
  exact
    packedTile16384 73580800 73613568 12 1803 8577 26 _ _ (452847 / 25000) (1811391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73613568 :
    ThetaLowerSegment 73613568 73646336 (7360520441523 / 100000) (7363777396259 / 100000) := by
  exact
    packedTile16384 73613568 73646336 12 1798 8579 26 _ _ (226429 / 12500) (362287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73646336 :
    ThetaLowerSegment 73646336 73679104 (7363777396259 / 100000) (736711594837 / 10000) := by
  exact
    packedTile16384 73646336 73679104 12 1843 8581 26 _ _ (1811477 / 100000) (45287 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73679104 :
    ThetaLowerSegment 73679104 73711872 (736711594837 / 10000) (1842605946429 / 25000) := by
  exact
    packedTile16384 73679104 73711872 12 1826 8583 26 _ _ (1811521 / 100000) (452881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73711872 :
    ThetaLowerSegment 73711872 73744640 (1842605946429 / 25000) (92170921689 / 1250) := by
  exact
    packedTile16384 73711872 73744640 12 1794 8585 26 _ _ (905783 / 50000) (1811569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73744640 :
    ThetaLowerSegment 73744640 73777408 (92170921689 / 1250) (737691108219 / 10000) := by
  exact
    packedTile16384 73744640 73777408 12 1787 8587 26 _ _ (181161 / 10000) (1811613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73777408 :
    ThetaLowerSegment 73777408 73810176 (737691108219 / 10000) (14760351369 / 200) := by
  exact
    packedTile16384 73777408 73810176 12 1802 8589 26 _ _ (362331 / 20000) (905829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73810176 :
    ThetaLowerSegment 73810176 73842944 (14760351369 / 200) (3691723806447 / 50000) := by
  exact
    packedTile16384 73810176 73842944 12 1806 8591 26 _ _ (1811699 / 100000) (905851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73842944 :
    ThetaLowerSegment 73842944 73875712 (3691723806447 / 50000) (3693367964127 / 50000) := by
  exact
    packedTile16384 73842944 73875712 12 1815 8593 26 _ _ (56617 / 3125) (1811747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73875712 :
    ThetaLowerSegment 73875712 73908480 (3693367964127 / 50000) (739006418281 / 10000) := by
  exact
    packedTile16384 73875712 73908480 12 1837 8595 26 _ _ (452947 / 25000) (1811791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73908480 :
    ThetaLowerSegment 73908480 73941248 (739006418281 / 10000) (3696663646121 / 50000) := by
  exact
    packedTile16384 73908480 73941248 12 1801 8597 26 _ _ (226479 / 12500) (362367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73941248 :
    ThetaLowerSegment 73941248 73974016 (3696663646121 / 50000) (46228837732 / 625) := by
  exact
    packedTile16384 73941248 73974016 12 1814 8598 26 _ _ (1811877 / 100000) (45297 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell73974016 :
    ThetaLowerSegment 73974016 74006784 (46228837732 / 625) (3699935935539 / 50000) := by
  exact
    packedTile16384 73974016 74006784 12 1798 8600 26 _ _ (1811921 / 100000) (452981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74006784 :
    ThetaLowerSegment 74006784 74039552 (3699935935539 / 50000) (3701555832249 / 50000) := by
  exact
    packedTile16384 74006784 74039552 12 1788 8602 26 _ _ (362393 / 20000) (56624 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74039552 :
    ThetaLowerSegment 74039552 74072320 (3701555832249 / 50000) (7406298988329 / 100000) := by
  exact
    packedTile16384 74039552 74072320 12 1759 8604 26 _ _ (1812009 / 100000) (453003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74072320 :
    ThetaLowerSegment 74072320 74105088 (7406298988329 / 100000) (1481908150587 / 20000) := by
  exact
    packedTile16384 74072320 74105088 12 1789 8606 26 _ _ (906027 / 50000) (1812057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74105088 :
    ThetaLowerSegment 74105088 74137856 (1481908150587 / 20000) (7412849643883 / 100000) := by
  exact
    packedTile16384 74105088 74137856 12 1826 8608 26 _ _ (906049 / 50000) (1812101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74137856 :
    ThetaLowerSegment 74137856 74170624 (7412849643883 / 100000) (7416039013803 / 100000) := by
  exact
    packedTile16384 74137856 74170624 12 1760 8610 26 _ _ (906071 / 50000) (362429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74170624 :
    ThetaLowerSegment 74170624 74203392 (7416039013803 / 100000) (7419378872601 / 100000) := by
  exact
    packedTile16384 74170624 74203392 12 1843 8612 26 _ _ (906093 / 50000) (1812189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74203392 :
    ThetaLowerSegment 74203392 74236160 (7419378872601 / 100000) (3711326787009 / 50000) := by
  exact
    packedTile16384 74203392 74236160 12 1807 8614 26 _ _ (1812231 / 100000) (906117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74236160 :
    ThetaLowerSegment 74236160 74268928 (3711326787009 / 50000) (1856470762017 / 25000) := by
  exact
    packedTile16384 74236160 74268928 12 1782 8616 26 _ _ (72491 / 4000) (906139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74268928 :
    ThetaLowerSegment 74268928 74301696 (1856470762017 / 25000) (7429147034587 / 100000) := by
  exact
    packedTile16384 74268928 74301696 12 1801 8617 26 _ _ (1812319 / 100000) (906161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74301696 :
    ThetaLowerSegment 74301696 74334464 (7429147034587 / 100000) (232263186704 / 3125) := by
  exact
    packedTile16384 74301696 74334464 12 1807 8619 26 _ _ (1812363 / 100000) (906183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74334464 :
    ThetaLowerSegment 74334464 74367232 (232263186704 / 3125) (1858922889189 / 25000) := by
  exact
    packedTile16384 74334464 74367232 12 1804 8621 26 _ _ (1812407 / 100000) (181241 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74367232 :
    ThetaLowerSegment 74367232 74400000 (1858922889189 / 25000) (3719518670651 / 50000) := by
  exact
    packedTile16384 74367232 74400000 12 1846 8623 26 _ _ (1812451 / 100000) (906227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74400000 :
    ThetaLowerSegment 74400000 74432768 (3719518670651 / 50000) (7442258144917 / 100000) := by
  exact
    packedTile16384 74400000 74432768 12 1777 8625 26 _ _ (362499 / 20000) (906249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74432768 :
    ThetaLowerSegment 74432768 74465536 (7442258144917 / 100000) (1861393319687 / 25000) := by
  exact
    packedTile16384 74432768 74465536 12 1829 8627 26 _ _ (1812539 / 100000) (906271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74465536 :
    ThetaLowerSegment 74465536 74498304 (1861393319687 / 25000) (3724387150163 / 50000) := by
  exact
    packedTile16384 74465536 74498304 12 1766 8629 26 _ _ (1812583 / 100000) (906293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74498304 :
    ThetaLowerSegment 74498304 74514688 (3724387150163 / 50000) (1490087295857 / 20000) := by
  exact
    packedTile16384 74498304 74514688 11 917 8631 26 _ _ (1812627 / 100000) (181263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74514688 :
    ThetaLowerSegment 74514688 74547456 (1490087295857 / 20000) (1490739849497 / 20000) := by
  exact
    packedTile16384 74514688 74547456 12 1800 8632 26 _ _ (1812649 / 100000) (453163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74547456 :
    ThetaLowerSegment 74547456 74563840 (1490739849497 / 20000) (3727637238851 / 50000) := by
  exact
    packedTile16384 74547456 74563840 11 869 8634 26 _ _ (1812693 / 100000) (226587 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74563840 :
    ThetaLowerSegment 74563840 74580224 (3727637238851 / 50000) (3728471087751 / 50000) := by
  exact
    packedTile16384 74563840 74580224 11 920 8635 26 _ _ (362543 / 20000) (906359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74580224 :
    ThetaLowerSegment 74580224 74596608 (3728471087751 / 50000) (7458622582701 / 100000) := by
  exact
    packedTile16384 74580224 74596608 11 927 8635 26 _ _ (1812737 / 100000) (90637 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74596608 :
    ThetaLowerSegment 74596608 74629376 (7458622582701 / 100000) (7461907302009 / 100000) := by
  exact
    packedTile16384 74596608 74629376 12 1812 8636 26 _ _ (1812759 / 100000) (906381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74629376 :
    ThetaLowerSegment 74629376 74662144 (7461907302009 / 100000) (933149239231 / 12500) := by
  exact
    packedTile16384 74629376 74662144 12 1813 8638 26 _ _ (1812803 / 100000) (906403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74662144 :
    ThetaLowerSegment 74662144 74694912 (933149239231 / 12500) (7468415342967 / 100000) := by
  exact
    packedTile16384 74662144 74694912 12 1777 8640 26 _ _ (1812847 / 100000) (36257 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74694912 :
    ThetaLowerSegment 74694912 74711296 (7468415342967 / 100000) (7470057822213 / 100000) := by
  exact
    packedTile16384 74694912 74711296 11 906 8642 26 _ _ (1812891 / 100000) (906447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74711296 :
    ThetaLowerSegment 74711296 74727680 (7470057822213 / 100000) (7471725702173 / 100000) := by
  exact
    packedTile16384 74711296 74727680 11 920 8643 26 _ _ (1812913 / 100000) (453229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74727680 :
    ThetaLowerSegment 74727680 74760448 (7471725702173 / 100000) (7475003488653 / 100000) := by
  exact
    packedTile16384 74727680 74760448 12 1808 8644 26 _ _ (362587 / 20000) (906469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74760448 :
    ThetaLowerSegment 74760448 74793216 (7475003488653 / 100000) (7478317612437 / 100000) := by
  exact
    packedTile16384 74760448 74793216 12 1828 8646 26 _ _ (906489 / 50000) (1812981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74793216 :
    ThetaLowerSegment 74793216 74825984 (7478317612437 / 100000) (7481593743191 / 100000) := by
  exact
    packedTile16384 74793216 74825984 12 1807 8648 26 _ _ (906511 / 50000) (72521 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74825984 :
    ThetaLowerSegment 74825984 74858752 (7481593743191 / 100000) (7484830066001 / 100000) := by
  exact
    packedTile16384 74825984 74858752 12 1785 8650 26 _ _ (906533 / 50000) (1813069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74858752 :
    ThetaLowerSegment 74858752 74891520 (7484830066001 / 100000) (7488113608211 / 100000) := by
  exact
    packedTile16384 74858752 74891520 12 1811 8652 26 _ _ (181311 / 10000) (1813113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74891520 :
    ThetaLowerSegment 74891520 74924288 (7488113608211 / 100000) (7491446185263 / 100000) := by
  exact
    packedTile16384 74891520 74924288 12 1838 8653 26 _ _ (906577 / 50000) (1813157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74924288 :
    ThetaLowerSegment 74924288 74957056 (7491446185263 / 100000) (3747354063333 / 50000) := by
  exact
    packedTile16384 74924288 74957056 12 1799 8655 26 _ _ (1813197 / 100000) (4533 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74957056 :
    ThetaLowerSegment 74957056 74989824 (3747354063333 / 50000) (7497984653153 / 100000) := by
  exact
    packedTile16384 74957056 74989824 12 1807 8657 26 _ _ (1813241 / 100000) (453311 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell74989824 :
    ThetaLowerSegment 74989824 75022592 (7497984653153 / 100000) (1875293555367 / 25000) := by
  exact
    packedTile16384 74989824 75022592 12 1759 8659 26 _ _ (362657 / 20000) (226661 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75022592 :
    ThetaLowerSegment 75022592 75038976 (1875293555367 / 25000) (1875697020847 / 25000) := by
  exact
    packedTile16384 75022592 75038976 11 890 8661 26 _ _ (113333 / 6250) (1813331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75038976 :
    ThetaLowerSegment 75038976 75055360 (1875697020847 / 25000) (3752223649319 / 50000) := by
  exact
    packedTile16384 75038976 75055360 11 915 8662 26 _ _ (36267 / 2000) (1813353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75055360 :
    ThetaLowerSegment 75055360 75071744 (3752223649319 / 50000) (3753051453637 / 50000) := by
  exact
    packedTile16384 75055360 75071744 11 913 8663 26 _ _ (453343 / 25000) (14507 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75071744 :
    ThetaLowerSegment 75071744 75088128 (3753051453637 / 50000) (1876941447393 / 25000) := by
  exact
    packedTile16384 75071744 75088128 11 917 8664 26 _ _ (906697 / 50000) (1813397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75088128 :
    ThetaLowerSegment 75088128 75120896 (1876941447393 / 25000) (1877769271797 / 25000) := by
  exact
    packedTile16384 75088128 75120896 12 1826 8665 26 _ _ (226677 / 12500) (1813419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75120896 :
    ThetaLowerSegment 75120896 75153664 (1877769271797 / 25000) (3757154335563 / 50000) := by
  exact
    packedTile16384 75120896 75153664 12 1782 8667 26 _ _ (1813459 / 100000) (906731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75153664 :
    ThetaLowerSegment 75153664 75170048 (3757154335563 / 50000) (939498496863 / 12500) := by
  exact
    packedTile16384 75153664 75170048 11 926 8669 26 _ _ (1813503 / 100000) (906753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75170048 :
    ThetaLowerSegment 75170048 75202816 (939498496863 / 12500) (7519286776879 / 100000) := by
  exact
    packedTile16384 75170048 75202816 12 1819 8670 26 _ _ (72541 / 4000) (226691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75202816 :
    ThetaLowerSegment 75202816 75235584 (7519286776879 / 100000) (1504520033123 / 20000) := by
  exact
    packedTile16384 75202816 75235584 12 1827 8671 26 _ _ (56674 / 3125) (1813571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75235584 :
    ThetaLowerSegment 75235584 75268352 (1504520033123 / 20000) (7525893685007 / 100000) := by
  exact
    packedTile16384 75235584 75268352 12 1816 8673 26 _ _ (453403 / 25000) (362723 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75268352 :
    ThetaLowerSegment 75268352 75301120 (7525893685007 / 100000) (7529169147743 / 100000) := by
  exact
    packedTile16384 75268352 75301120 12 1806 8675 26 _ _ (226707 / 12500) (1813659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75301120 :
    ThetaLowerSegment 75301120 75333888 (7529169147743 / 100000) (3766239574209 / 50000) := by
  exact
    packedTile16384 75301120 75333888 12 1825 8677 26 _ _ (1813699 / 100000) (906851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75333888 :
    ThetaLowerSegment 75333888 75366656 (3766239574209 / 50000) (1883938692069 / 25000) := by
  exact
    packedTile16384 75333888 75366656 12 1806 8679 26 _ _ (1813743 / 100000) (906873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75366656 :
    ThetaLowerSegment 75366656 75399424 (1883938692069 / 25000) (753905404501 / 10000) := by
  exact
    packedTile16384 75366656 75399424 12 1819 8681 26 _ _ (906893 / 50000) (1813789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75399424 :
    ThetaLowerSegment 75399424 75432192 (753905404501 / 10000) (754237335391 / 10000) := by
  exact
    packedTile16384 75399424 75432192 12 1830 8683 26 _ _ (181383 / 10000) (1813833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75432192 :
    ThetaLowerSegment 75432192 75464960 (754237335391 / 10000) (7545676416643 / 100000) := by
  exact
    packedTile16384 75432192 75464960 12 1821 8685 26 _ _ (1813873 / 100000) (453469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75464960 :
    ThetaLowerSegment 75464960 75497728 (7545676416643 / 100000) (7548901559291 / 100000) := by
  exact
    packedTile16384 75464960 75497728 12 1778 8687 26 _ _ (453479 / 25000) (1813919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75497728 :
    ThetaLowerSegment 75497728 75530496 (7548901559291 / 100000) (7552221106091 / 100000) := by
  exact
    packedTile16384 75497728 75530496 12 1830 8688 26 _ _ (45349 / 2500) (1813963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75530496 :
    ThetaLowerSegment 75530496 75563264 (7552221106091 / 100000) (7555453659437 / 100000) := by
  exact
    packedTile16384 75530496 75563264 12 1782 8690 26 _ _ (1814003 / 100000) (907003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75563264 :
    ThetaLowerSegment 75563264 75596032 (7555453659437 / 100000) (7558715315943 / 100000) := by
  exact
    packedTile16384 75563264 75596032 12 1798 8692 26 _ _ (1814047 / 100000) (36281 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75596032 :
    ThetaLowerSegment 75596032 75628800 (7558715315943 / 100000) (7561962537043 / 100000) := by
  exact
    packedTile16384 75596032 75628800 12 1790 8694 26 _ _ (181409 / 10000) (1814093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75628800 :
    ThetaLowerSegment 75628800 75661568 (7561962537043 / 100000) (7565293285231 / 100000) := by
  exact
    packedTile16384 75628800 75661568 12 1836 8696 26 _ _ (1814133 / 100000) (226767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75661568 :
    ThetaLowerSegment 75661568 75694336 (7565293285231 / 100000) (7568540662061 / 100000) := by
  exact
    packedTile16384 75661568 75694336 12 1790 8698 26 _ _ (1814177 / 100000) (90709 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75694336 :
    ThetaLowerSegment 75694336 75727104 (7568540662061 / 100000) (7571822586041 / 100000) := by
  exact
    packedTile16384 75694336 75727104 12 1809 8700 26 _ _ (90711 / 5000) (1814223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75727104 :
    ThetaLowerSegment 75727104 75759872 (7571822586041 / 100000) (7575113659123 / 100000) := by
  exact
    packedTile16384 75727104 75759872 12 1814 8702 26 _ _ (1814263 / 100000) (907133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75759872 :
    ThetaLowerSegment 75759872 75792640 (7575113659123 / 100000) (7578432024797 / 100000) := by
  exact
    packedTile16384 75759872 75792640 12 1829 8704 26 _ _ (907153 / 50000) (1814309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75792640 :
    ThetaLowerSegment 75792640 75825408 (7578432024797 / 100000) (7581690597397 / 100000) := by
  exact
    packedTile16384 75792640 75825408 12 1796 8705 26 _ _ (36287 / 2000) (1814353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75825408 :
    ThetaLowerSegment 75825408 75858176 (7581690597397 / 100000) (1896249558959 / 25000) := by
  exact
    packedTile16384 75825408 75858176 12 1823 8707 26 _ _ (1814393 / 100000) (453599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75858176 :
    ThetaLowerSegment 75858176 75890944 (1896249558959 / 25000) (75883077671 / 1000) := by
  exact
    packedTile16384 75858176 75890944 12 1824 8709 26 _ _ (453609 / 25000) (1814439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75890944 :
    ThetaLowerSegment 75890944 75923712 (75883077671 / 1000) (759162826367 / 10000) := by
  exact
    packedTile16384 75890944 75923712 12 1830 8711 26 _ _ (1814479 / 100000) (907241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75923712 :
    ThetaLowerSegment 75923712 75956480 (759162826367 / 10000) (1898717703621 / 25000) := by
  exact
    packedTile16384 75923712 75956480 12 1787 8713 26 _ _ (907261 / 50000) (72581 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75956480 :
    ThetaLowerSegment 75956480 75989248 (1898717703621 / 25000) (237444163908 / 3125) := by
  exact
    packedTile16384 75956480 75989248 12 1842 8715 26 _ _ (907283 / 50000) (1814569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell75989248 :
    ThetaLowerSegment 75989248 76022016 (237444163908 / 3125) (7601524906481 / 100000) := by
  exact
    packedTile16384 75989248 76022016 12 1825 8717 26 _ _ (1814609 / 100000) (453653 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76022016 :
    ThetaLowerSegment 76022016 76054784 (7601524906481 / 100000) (7604764060301 / 100000) := by
  exact
    packedTile16384 76022016 76054784 12 1785 8719 26 _ _ (453663 / 25000) (362931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76054784 :
    ThetaLowerSegment 76054784 76087552 (7604764060301 / 100000) (7608019623131 / 100000) := by
  exact
    packedTile16384 76054784 76087552 12 1794 8720 26 _ _ (362939 / 20000) (907349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76087552 :
    ThetaLowerSegment 76087552 76120320 (7608019623131 / 100000) (7611277077841 / 100000) := by
  exact
    packedTile16384 76087552 76120320 12 1795 8722 26 _ _ (907369 / 50000) (1814741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76120320 :
    ThetaLowerSegment 76120320 76153088 (7611277077841 / 100000) (304582763623 / 4000) := by
  exact
    packedTile16384 76120320 76153088 12 1814 8724 26 _ _ (1814781 / 100000) (56712 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76153088 :
    ThetaLowerSegment 76153088 76185856 (304582763623 / 4000) (7617852107191 / 100000) := by
  exact
    packedTile16384 76153088 76185856 12 1809 8726 26 _ _ (226853 / 12500) (1814827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76185856 :
    ThetaLowerSegment 76185856 76218624 (7617852107191 / 100000) (381056578593 / 5000) := by
  exact
    packedTile16384 76185856 76218624 12 1807 8728 26 _ _ (1814867 / 100000) (181487 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76218624 :
    ThetaLowerSegment 76218624 76251392 (381056578593 / 5000) (190608417573 / 2500) := by
  exact
    packedTile16384 76218624 76251392 12 1766 8730 26 _ _ (181491 / 10000) (1814913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76251392 :
    ThetaLowerSegment 76251392 76284160 (190608417573 / 2500) (7627572764119 / 100000) := by
  exact
    packedTile16384 76251392 76284160 12 1783 8732 26 _ _ (1814953 / 100000) (453739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76284160 :
    ThetaLowerSegment 76284160 76316928 (7627572764119 / 100000) (7630847016903 / 100000) := by
  exact
    packedTile16384 76284160 76316928 12 1804 8734 26 _ _ (453749 / 25000) (1814999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76316928 :
    ThetaLowerSegment 76316928 76349696 (7630847016903 / 100000) (3817036170603 / 50000) := by
  exact
    packedTile16384 76316928 76349696 12 1777 8735 26 _ _ (1815039 / 100000) (907521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76349696 :
    ThetaLowerSegment 76349696 76382464 (3817036170603 / 50000) (3818724196863 / 50000) := by
  exact
    packedTile16384 76349696 76382464 12 1860 8737 26 _ _ (907541 / 50000) (363017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76382464 :
    ThetaLowerSegment 76382464 76415232 (3818724196863 / 50000) (3820336027863 / 50000) := by
  exact
    packedTile16384 76382464 76415232 12 1776 8739 26 _ _ (14521 / 800) (226891 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76415232 :
    ThetaLowerSegment 76415232 76448000 (3820336027863 / 50000) (3821974216983 / 50000) := by
  exact
    packedTile16384 76415232 76448000 12 1805 8741 26 _ _ (56724 / 3125) (1815171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76448000 :
    ThetaLowerSegment 76448000 76480768 (3821974216983 / 50000) (3823586124351 / 50000) := by
  exact
    packedTile16384 76448000 76480768 12 1776 8743 26 _ _ (1815211 / 100000) (907607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76480768 :
    ThetaLowerSegment 76480768 76513536 (3823586124351 / 50000) (7650372539741 / 100000) := by
  exact
    packedTile16384 76480768 76513536 12 1763 8745 26 _ _ (1815253 / 100000) (226907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76513536 :
    ThetaLowerSegment 76513536 76546304 (7650372539741 / 100000) (1530743989113 / 20000) := by
  exact
    packedTile16384 76513536 76546304 12 1844 8747 26 _ _ (56728 / 3125) (1815299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76546304 :
    ThetaLowerSegment 76546304 76579072 (1530743989113 / 20000) (3828503762247 / 50000) := by
  exact
    packedTile16384 76546304 76579072 12 1811 8749 26 _ _ (1815339 / 100000) (907671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76579072 :
    ThetaLowerSegment 76579072 76611840 (3828503762247 / 50000) (3830104929171 / 50000) := by
  exact
    packedTile16384 76579072 76611840 12 1764 8750 26 _ _ (907691 / 50000) (363077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76611840 :
    ThetaLowerSegment 76611840 76644608 (3830104929171 / 50000) (7663486700467 / 100000) := by
  exact
    packedTile16384 76611840 76644608 12 1805 8752 26 _ _ (72617 / 4000) (453857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76644608 :
    ThetaLowerSegment 76644608 76677376 (7663486700467 / 100000) (1916671842197 / 25000) := by
  exact
    packedTile16384 76644608 76677376 12 1763 8754 26 _ _ (1815467 / 100000) (181547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76677376 :
    ThetaLowerSegment 76677376 76710144 (1916671842197 / 25000) (958749403501 / 12500) := by
  exact
    packedTile16384 76677376 76710144 12 1822 8756 26 _ _ (181551 / 10000) (1815513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76710144 :
    ThetaLowerSegment 76710144 76742912 (958749403501 / 12500) (1534641388253 / 20000) := by
  exact
    packedTile16384 76710144 76742912 12 1769 8758 26 _ _ (1815553 / 100000) (453889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76742912 :
    ThetaLowerSegment 76742912 76775680 (1534641388253 / 20000) (7676444148933 / 100000) := by
  exact
    packedTile16384 76742912 76775680 12 1783 8760 26 _ _ (453899 / 25000) (1815599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76775680 :
    ThetaLowerSegment 76775680 76792064 (7676444148933 / 100000) (7678109088979 / 100000) := by
  exact
    packedTile16384 76775680 76792064 11 917 8762 26 _ _ (907819 / 50000) (1815641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76792064 :
    ThetaLowerSegment 76792064 76824832 (7678109088979 / 100000) (7681457166019 / 100000) := by
  exact
    packedTile16384 76792064 76824832 12 1844 8763 26 _ _ (90783 / 5000) (1815663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76824832 :
    ThetaLowerSegment 76824832 76857600 (7681457166019 / 100000) (7684705456897 / 100000) := by
  exact
    packedTile16384 76824832 76857600 12 1789 8764 26 _ _ (907851 / 50000) (363141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76857600 :
    ThetaLowerSegment 76857600 76890368 (7684705456897 / 100000) (1921998442773 / 25000) := by
  exact
    packedTile16384 76857600 76890368 12 1811 8766 26 _ _ (363149 / 20000) (453937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76890368 :
    ThetaLowerSegment 76890368 76923136 (1921998442773 / 25000) (1922815547373 / 25000) := by
  exact
    packedTile16384 76890368 76923136 12 1800 8768 26 _ _ (453947 / 25000) (1815791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76923136 :
    ThetaLowerSegment 76923136 76955904 (1922815547373 / 25000) (1923643565853 / 25000) := by
  exact
    packedTile16384 76923136 76955904 12 1824 8770 26 _ _ (181583 / 10000) (1815833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76955904 :
    ThetaLowerSegment 76955904 76988672 (1923643565853 / 25000) (1924460708703 / 25000) := by
  exact
    packedTile16384 76955904 76988672 12 1800 8772 26 _ _ (1815873 / 100000) (453969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell76988672 :
    ThetaLowerSegment 76988672 77021440 (1924460708703 / 25000) (481325369337 / 6250) := by
  exact
    packedTile16384 76988672 77021440 12 1852 8774 26 _ _ (363183 / 20000) (907959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77021440 :
    ThetaLowerSegment 77021440 77054208 (481325369337 / 6250) (481528756633 / 6250) := by
  exact
    packedTile16384 77021440 77054208 12 1792 8776 26 _ _ (907979 / 50000) (1815961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77054208 :
    ThetaLowerSegment 77054208 77086976 (481528756633 / 6250) (481730786633 / 6250) := by
  exact
    packedTile16384 77054208 77086976 12 1780 8778 26 _ _ (454 / 25) (1816003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77086976 :
    ThetaLowerSegment 77086976 77119744 (481730786633 / 6250) (7710970543743 / 100000) := by
  exact
    packedTile16384 77086976 77119744 12 1805 8779 26 _ _ (1816043 / 100000) (908023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77119744 :
    ThetaLowerSegment 77119744 77152512 (7710970543743 / 100000) (964282888231 / 12500) := by
  exact
    packedTile16384 77119744 77152512 12 1813 8781 26 _ _ (363217 / 20000) (227011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77152512 :
    ThetaLowerSegment 77152512 77185280 (964282888231 / 12500) (964697873479 / 12500) := by
  exact
    packedTile16384 77152512 77185280 12 1828 8783 26 _ _ (56754 / 3125) (1816131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77185280 :
    ThetaLowerSegment 77185280 77218048 (964697873479 / 12500) (1930217563883 / 25000) := by
  exact
    packedTile16384 77185280 77218048 12 1810 8785 26 _ _ (181617 / 10000) (1816173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77218048 :
    ThetaLowerSegment 77218048 77250816 (1930217563883 / 25000) (7724126725441 / 100000) := by
  exact
    packedTile16384 77218048 77250816 12 1793 8787 26 _ _ (1816213 / 100000) (227027 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77250816 :
    ThetaLowerSegment 77250816 77283584 (7724126725441 / 100000) (1931847633919 / 25000) := by
  exact
    packedTile16384 77250816 77283584 12 1797 8789 26 _ _ (363251 / 20000) (908129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77283584 :
    ThetaLowerSegment 77283584 77316352 (1931847633919 / 25000) (3865309048611 / 50000) := by
  exact
    packedTile16384 77283584 77316352 12 1777 8791 26 _ _ (908149 / 50000) (1816301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77316352 :
    ThetaLowerSegment 77316352 77349120 (3865309048611 / 50000) (3866970091541 / 50000) := by
  exact
    packedTile16384 77316352 77349120 12 1829 8792 26 _ _ (90817 / 5000) (1816343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77349120 :
    ThetaLowerSegment 77349120 77381888 (3866970091541 / 50000) (3868604835341 / 50000) := by
  exact
    packedTile16384 77349120 77381888 12 1800 8794 26 _ _ (908191 / 50000) (363277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77381888 :
    ThetaLowerSegment 77381888 77414656 (3868604835341 / 50000) (7740459255007 / 100000) := by
  exact
    packedTile16384 77381888 77414656 12 1789 8796 26 _ _ (72657 / 4000) (454107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77414656 :
    ThetaLowerSegment 77414656 77447424 (7740459255007 / 100000) (7743757959079 / 100000) := by
  exact
    packedTile16384 77414656 77447424 12 1816 8798 26 _ _ (1816467 / 100000) (181647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77447424 :
    ThetaLowerSegment 77447424 77480192 (7743757959079 / 100000) (7746984079063 / 100000) := by
  exact
    packedTile16384 77447424 77480192 12 1776 8800 26 _ _ (1816509 / 100000) (56766 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77480192 :
    ThetaLowerSegment 77480192 77512960 (7746984079063 / 100000) (7750253872663 / 100000) := by
  exact
    packedTile16384 77480192 77512960 12 1800 8802 26 _ _ (227069 / 12500) (363311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77512960 :
    ThetaLowerSegment 77512960 77545728 (7750253872663 / 100000) (7753550990773 / 100000) := by
  exact
    packedTile16384 77512960 77545728 12 1815 8804 26 _ _ (908297 / 50000) (1816597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77545728 :
    ThetaLowerSegment 77545728 77578496 (7753550990773 / 100000) (7756795502669 / 100000) := by
  exact
    packedTile16384 77545728 77578496 12 1786 8806 26 _ _ (454159 / 25000) (1816639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77578496 :
    ThetaLowerSegment 77578496 77611264 (7756795502669 / 100000) (1940024102103 / 25000) := by
  exact
    packedTile16384 77578496 77611264 12 1817 8807 26 _ _ (1816679 / 100000) (908341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77611264 :
    ThetaLowerSegment 77611264 77644032 (1940024102103 / 25000) (194083617639 / 2500) := by
  exact
    packedTile16384 77611264 77644032 12 1788 8809 26 _ _ (1816721 / 100000) (454181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77644032 :
    ThetaLowerSegment 77644032 77676800 (194083617639 / 2500) (485409796409 / 6250) := by
  exact
    packedTile16384 77644032 77676800 12 1768 8811 26 _ _ (1816763 / 100000) (908383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77676800 :
    ThetaLowerSegment 77676800 77709568 (485409796409 / 6250) (3884904411747 / 50000) := by
  exact
    packedTile16384 77676800 77709568 12 1790 8813 26 _ _ (363361 / 20000) (227101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77709568 :
    ThetaLowerSegment 77709568 77725952 (3884904411747 / 50000) (1554304422043 / 20000) := by
  exact
    packedTile16384 77709568 77725952 11 943 8815 26 _ _ (1816847 / 100000) (36337 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77725952 :
    ThetaLowerSegment 77725952 77758720 (1554304422043 / 20000) (7774776120803 / 100000) := by
  exact
    packedTile16384 77725952 77758720 12 1791 8816 26 _ _ (454217 / 25000) (1816871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77758720 :
    ThetaLowerSegment 77758720 77791488 (7774776120803 / 100000) (972256501417 / 12500) := by
  exact
    packedTile16384 77758720 77791488 12 1803 8818 26 _ _ (1816911 / 100000) (908457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77791488 :
    ThetaLowerSegment 77791488 77824256 (972256501417 / 12500) (7781331611501 / 100000) := by
  exact
    packedTile16384 77791488 77824256 12 1805 8819 26 _ _ (1816953 / 100000) (454239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77824256 :
    ThetaLowerSegment 77824256 77857024 (7781331611501 / 100000) (486536842721 / 6250) := by
  exact
    packedTile16384 77824256 77857024 12 1793 8821 26 _ _ (363399 / 20000) (908499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77857024 :
    ThetaLowerSegment 77857024 77889792 (486536842721 / 6250) (7787894673839 / 100000) := by
  exact
    packedTile16384 77857024 77889792 12 1819 8823 26 _ _ (1817037 / 100000) (22713 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77889792 :
    ThetaLowerSegment 77889792 77922560 (7787894673839 / 100000) (486951359093 / 6250) := by
  exact
    packedTile16384 77889792 77922560 12 1831 8825 26 _ _ (1817079 / 100000) (908541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77922560 :
    ThetaLowerSegment 77922560 77955328 (486951359093 / 6250) (7794501648893 / 100000) := by
  exact
    packedTile16384 77922560 77955328 12 1805 8827 26 _ _ (1817121 / 100000) (454281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77955328 :
    ThetaLowerSegment 77955328 77988096 (7794501648893 / 100000) (7797750736337 / 100000) := by
  exact
    packedTile16384 77955328 77988096 12 1788 8829 26 _ _ (1817163 / 100000) (908583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell77988096 :
    ThetaLowerSegment 77988096 78020864 (7797750736337 / 100000) (7801039877387 / 100000) := by
  exact
    packedTile16384 77988096 78020864 12 1810 8831 26 _ _ (363441 / 20000) (227151 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78020864 :
    ThetaLowerSegment 78020864 78053632 (7801039877387 / 100000) (7804339997939 / 100000) := by
  exact
    packedTile16384 78020864 78053632 12 1816 8832 26 _ _ (1817247 / 100000) (7269 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78053632 :
    ThetaLowerSegment 78053632 78086400 (7804339997939 / 100000) (7807592945249 / 100000) := by
  exact
    packedTile16384 78053632 78086400 12 1790 8834 26 _ _ (1817289 / 100000) (454323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78086400 :
    ThetaLowerSegment 78086400 78119168 (7807592945249 / 100000) (1952720124257 / 25000) := by
  exact
    packedTile16384 78086400 78119168 12 1809 8836 26 _ _ (1817331 / 100000) (908667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78119168 :
    ThetaLowerSegment 78119168 78151936 (1952720124257 / 25000) (7814142681563 / 100000) := by
  exact
    packedTile16384 78119168 78151936 12 1795 8838 26 _ _ (1817373 / 100000) (56793 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78151936 :
    ThetaLowerSegment 78151936 78184704 (7814142681563 / 100000) (7817483090333 / 100000) := by
  exact
    packedTile16384 78151936 78184704 12 1838 8840 26 _ _ (363483 / 20000) (908709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78184704 :
    ThetaLowerSegment 78184704 78217472 (7817483090333 / 100000) (7820707259051 / 100000) := by
  exact
    packedTile16384 78184704 78217472 12 1774 8842 26 _ _ (1817457 / 100000) (90873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78217472 :
    ThetaLowerSegment 78217472 78250240 (7820707259051 / 100000) (3911983017379 / 50000) := by
  exact
    packedTile16384 78217472 78250240 12 1793 8844 26 _ _ (1817499 / 100000) (908751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78250240 :
    ThetaLowerSegment 78250240 78283008 (3911983017379 / 50000) (7827173994623 / 100000) := by
  exact
    packedTile16384 78250240 78283008 12 1765 8845 26 _ _ (1817541 / 100000) (227193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78283008 :
    ThetaLowerSegment 78283008 78315776 (7827173994623 / 100000) (3915220095637 / 50000) := by
  exact
    packedTile16384 78283008 78315776 12 1797 8847 26 _ _ (1817583 / 100000) (908793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78315776 :
    ThetaLowerSegment 78315776 78348544 (3915220095637 / 50000) (3916828692877 / 50000) := by
  exact
    packedTile16384 78315776 78348544 12 1770 8849 26 _ _ (227203 / 12500) (1817627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78348544 :
    ThetaLowerSegment 78348544 78364928 (3916828692877 / 50000) (3917663001571 / 50000) := by
  exact
    packedTile16384 78348544 78364928 11 918 8851 26 _ _ (908833 / 50000) (1817669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78364928 :
    ThetaLowerSegment 78364928 78381312 (3917663001571 / 50000) (1959243206891 / 25000) := by
  exact
    packedTile16384 78364928 78381312 11 906 8852 26 _ _ (1817687 / 100000) (181769 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78381312 :
    ThetaLowerSegment 78381312 78397696 (1959243206891 / 25000) (1959660370877 / 25000) := by
  exact
    packedTile16384 78381312 78397696 11 918 8853 26 _ _ (454427 / 25000) (1817711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78397696 :
    ThetaLowerSegment 78397696 78430464 (1959660370877 / 25000) (245056385374 / 3125) := by
  exact
    packedTile16384 78397696 78430464 12 1740 8854 26 _ _ (1817729 / 100000) (454433 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78430464 :
    ThetaLowerSegment 78430464 78446848 (245056385374 / 3125) (7843449414723 / 100000) := by
  exact
    packedTile16384 78430464 78446848 11 905 8856 26 _ _ (1817771 / 100000) (908887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78446848 :
    ThetaLowerSegment 78446848 78463232 (7843449414723 / 100000) (7845089063107 / 100000) := by
  exact
    packedTile16384 78446848 78463232 11 902 8857 26 _ _ (56806 / 3125) (363559 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78463232 :
    ThetaLowerSegment 78463232 78479616 (7845089063107 / 100000) (313867985817 / 4000) := by
  exact
    packedTile16384 78463232 78479616 11 886 8857 26 _ _ (1817813 / 100000) (227227 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78479616 :
    ThetaLowerSegment 78479616 78496000 (313867985817 / 4000) (1569659867693 / 20000) := by
  exact
    packedTile16384 78479616 78496000 11 880 8858 26 _ _ (1817833 / 100000) (454459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78496000 :
    ThetaLowerSegment 78496000 78512384 (1569659867693 / 20000) (7849997214101 / 100000) := by
  exact
    packedTile16384 78496000 78512384 11 934 8859 26 _ _ (908927 / 50000) (1817857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78512384 :
    ThetaLowerSegment 78512384 78528768 (7849997214101 / 100000) (1962901508369 / 25000) := by
  exact
    packedTile16384 78512384 78528768 11 885 8860 26 _ _ (14543 / 800) (908939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78528768 :
    ThetaLowerSegment 78528768 78545152 (1962901508369 / 25000) (1963321896819 / 25000) := by
  exact
    packedTile16384 78528768 78545152 11 925 8861 26 _ _ (227237 / 12500) (1817899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78545152 :
    ThetaLowerSegment 78545152 78561536 (1963321896819 / 25000) (7854932802161 / 100000) := by
  exact
    packedTile16384 78545152 78561536 11 905 8862 26 _ _ (1817917 / 100000) (11362 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78561536 :
    ThetaLowerSegment 78561536 78577920 (7854932802161 / 100000) (7856636210067 / 100000) := by
  exact
    packedTile16384 78561536 78577920 11 937 8863 26 _ _ (908969 / 50000) (1817941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78577920 :
    ThetaLowerSegment 78577920 78594304 (7856636210067 / 100000) (7858261465413 / 100000) := by
  exact
    packedTile16384 78577920 78594304 11 894 8864 26 _ _ (1817959 / 100000) (908981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78594304 :
    ThetaLowerSegment 78594304 78610688 (7858261465413 / 100000) (7859864922891 / 100000) := by
  exact
    packedTile16384 78594304 78610688 11 882 8865 26 _ _ (1817979 / 100000) (908991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78610688 :
    ThetaLowerSegment 78610688 78627072 (7859864922891 / 100000) (7861506576891 / 100000) := by
  exact
    packedTile16384 78610688 78627072 11 903 8866 26 _ _ (909 / 50) (1818003 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78627072 :
    ThetaLowerSegment 78627072 78643456 (7861506576891 / 100000) (1572619105449 / 20000) := by
  exact
    packedTile16384 78627072 78643456 11 874 8867 26 _ _ (1818021 / 100000) (227253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78643456 :
    ThetaLowerSegment 78643456 78659840 (1572619105449 / 20000) (7864782670221 / 100000) := by
  exact
    packedTile16384 78643456 78659840 11 928 8868 26 _ _ (909021 / 50000) (363609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78659840 :
    ThetaLowerSegment 78659840 78676224 (7864782670221 / 100000) (3933219462807 / 50000) := by
  exact
    packedTile16384 78659840 78676224 11 911 8869 26 _ _ (1818063 / 100000) (909033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78676224 :
    ThetaLowerSegment 78676224 78692608 (3933219462807 / 50000) (3934012147431 / 50000) := by
  exact
    packedTile16384 78676224 78692608 11 872 8869 26 _ _ (454521 / 25000) (1818087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78692608 :
    ThetaLowerSegment 78692608 78708992 (3934012147431 / 50000) (3934830294231 / 50000) := by
  exact
    packedTile16384 78692608 78708992 11 900 8870 26 _ _ (227263 / 12500) (1818107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78708992 :
    ThetaLowerSegment 78708992 78725376 (3934830294231 / 50000) (3935655722981 / 50000) := by
  exact
    packedTile16384 78708992 78725376 11 908 8871 26 _ _ (2909 / 160) (113633 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78725376 :
    ThetaLowerSegment 78725376 78741760 (3935655722981 / 50000) (157459973709 / 2000) := by
  exact
    packedTile16384 78725376 78741760 11 928 8872 26 _ _ (909073 / 50000) (1818149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78741760 :
    ThetaLowerSegment 78741760 78758144 (157459973709 / 2000) (3937321154209 / 50000) := by
  exact
    packedTile16384 78741760 78758144 11 904 8873 26 _ _ (1818167 / 100000) (181817 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78758144 :
    ThetaLowerSegment 78758144 78774528 (3937321154209 / 50000) (3938132975151 / 50000) := by
  exact
    packedTile16384 78758144 78774528 11 893 8874 26 _ _ (454547 / 25000) (1818191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78774528 :
    ThetaLowerSegment 78774528 78790912 (3938132975151 / 50000) (1575590286009 / 20000) := by
  exact
    packedTile16384 78774528 78790912 11 927 8875 26 _ _ (1818209 / 100000) (454553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78790912 :
    ThetaLowerSegment 78790912 78823680 (1575590286009 / 20000) (985150984773 / 12500) := by
  exact
    packedTile16384 78790912 78823680 12 1791 8876 26 _ _ (1818229 / 100000) (227279 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78823680 :
    ThetaLowerSegment 78823680 78856448 (985150984773 / 12500) (394220038103 / 5000) := by
  exact
    packedTile16384 78823680 78856448 12 1756 8878 26 _ _ (1818271 / 100000) (909137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78856448 :
    ThetaLowerSegment 78856448 78872832 (394220038103 / 5000) (1971506128669 / 25000) := by
  exact
    packedTile16384 78856448 78872832 11 893 8880 26 _ _ (227289 / 12500) (363663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78872832 :
    ThetaLowerSegment 78872832 78889216 (1971506128669 / 25000) (3943850508851 / 50000) := by
  exact
    packedTile16384 78872832 78889216 11 922 8881 26 _ _ (1818333 / 100000) (56823 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78889216 :
    ThetaLowerSegment 78889216 78905600 (3943850508851 / 50000) (788932298947 / 10000) := by
  exact
    packedTile16384 78889216 78905600 11 892 8881 26 _ _ (909177 / 50000) (1818357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78905600 :
    ThetaLowerSegment 78905600 78921984 (788932298947 / 10000) (1578191541719 / 20000) := by
  exact
    packedTile16384 78905600 78921984 11 899 8882 26 _ _ (14547 / 800) (909189 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78921984 :
    ThetaLowerSegment 78921984 78938368 (1578191541719 / 20000) (7892563352263 / 100000) := by
  exact
    packedTile16384 78921984 78938368 11 883 8883 26 _ _ (454599 / 25000) (1818399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78938368 :
    ThetaLowerSegment 78938368 78954752 (7892563352263 / 100000) (7894243568647 / 100000) := by
  exact
    packedTile16384 78938368 78954752 11 924 8884 26 _ _ (113651 / 6250) (1818419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78954752 :
    ThetaLowerSegment 78954752 78971136 (7894243568647 / 100000) (3947953719251 / 50000) := by
  exact
    packedTile16384 78954752 78971136 11 915 8885 26 _ _ (1818437 / 100000) (45461 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78971136 :
    ThetaLowerSegment 78971136 78987520 (3947953719251 / 50000) (3948761114603 / 50000) := by
  exact
    packedTile16384 78971136 78987520 11 888 8886 26 _ _ (909229 / 50000) (1818461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell78987520 :
    ThetaLowerSegment 78987520 79003904 (3948761114603 / 50000) (789911521681 / 10000) := by
  exact
    packedTile16384 78987520 79003904 11 876 8887 26 _ _ (1818479 / 100000) (909241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79003904 :
    ThetaLowerSegment 79003904 79020288 (789911521681 / 10000) (3950372295957 / 50000) := by
  exact
    packedTile16384 79003904 79020288 11 896 8888 26 _ _ (1818499 / 100000) (909251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79020288 :
    ThetaLowerSegment 79020288 79036672 (3950372295957 / 50000) (3951205178117 / 50000) := by
  exact
    packedTile16384 79020288 79036672 11 916 8889 26 _ _ (45463 / 2500) (1818523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79036672 :
    ThetaLowerSegment 79036672 79053056 (3951205178117 / 50000) (1976010851513 / 25000) := by
  exact
    packedTile16384 79036672 79053056 11 898 8890 26 _ _ (1818541 / 100000) (113659 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79053056 :
    ThetaLowerSegment 79053056 79069440 (1976010851513 / 25000) (988213650991 / 12500) := by
  exact
    packedTile16384 79053056 79069440 11 916 8891 26 _ _ (1818561 / 100000) (454641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79069440 :
    ThetaLowerSegment 79069440 79085824 (988213650991 / 12500) (3953693879557 / 50000) := by
  exact
    packedTile16384 79069440 79085824 11 923 8892 26 _ _ (909291 / 50000) (363717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79085824 :
    ThetaLowerSegment 79085824 79102208 (3953693879557 / 50000) (7909062692477 / 100000) := by
  exact
    packedTile16384 79085824 79102208 11 921 8893 26 _ _ (1818603 / 100000) (909303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79102208 :
    ThetaLowerSegment 79102208 79134976 (7909062692477 / 100000) (316491775493 / 4000) := by
  exact
    packedTile16384 79102208 79134976 12 1777 8893 26 _ _ (56832 / 3125) (1818627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79134976 :
    ThetaLowerSegment 79134976 79151360 (316491775493 / 4000) (39569792329 / 500) := by
  exact
    packedTile16384 79134976 79151360 11 915 8895 26 _ _ (363733 / 20000) (454667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79151360 :
    ThetaLowerSegment 79151360 79167744 (39569792329 / 500) (247361443257 / 3125) := by
  exact
    packedTile16384 79151360 79167744 11 884 8896 26 _ _ (909343 / 50000) (1818689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79167744 :
    ThetaLowerSegment 79167744 79184128 (247361443257 / 3125) (1979299845553 / 25000) := by
  exact
    packedTile16384 79167744 79184128 11 898 8897 26 _ _ (909353 / 50000) (1818709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79184128 :
    ThetaLowerSegment 79184128 79200512 (1979299845553 / 25000) (7918841692693 / 100000) := by
  exact
    packedTile16384 79184128 79200512 11 903 8898 26 _ _ (1818727 / 100000) (181873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79200512 :
    ThetaLowerSegment 79200512 79216896 (7918841692693 / 100000) (1584097168177 / 20000) := by
  exact
    packedTile16384 79200512 79216896 11 904 8899 26 _ _ (454687 / 25000) (1818751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79216896 :
    ThetaLowerSegment 79216896 79233280 (1584097168177 / 20000) (7922137283137 / 100000) := by
  exact
    packedTile16384 79216896 79233280 11 908 8900 26 _ _ (1818769 / 100000) (454693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79233280 :
    ThetaLowerSegment 79233280 79249664 (7922137283137 / 100000) (198094673119 / 2500) := by
  exact
    packedTile16384 79233280 79249664 11 907 8901 26 _ _ (1818789 / 100000) (227349 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79249664 :
    ThetaLowerSegment 79249664 79266048 (198094673119 / 2500) (198134686939 / 2500) := by
  exact
    packedTile16384 79249664 79266048 11 880 8902 26 _ _ (181881 / 10000) (1818813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79266048 :
    ThetaLowerSegment 79266048 79282432 (198134686939 / 2500) (1981745193379 / 25000) := by
  exact
    packedTile16384 79266048 79282432 11 876 8903 26 _ _ (1818831 / 100000) (909417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79282432 :
    ThetaLowerSegment 79282432 79298816 (1981745193379 / 25000) (7928568630439 / 100000) := by
  exact
    packedTile16384 79282432 79298816 11 873 8904 26 _ _ (1818851 / 100000) (909427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79298816 :
    ThetaLowerSegment 79298816 79315200 (7928568630439 / 100000) (7930249268167 / 100000) := by
  exact
    packedTile16384 79298816 79315200 11 924 8904 26 _ _ (227359 / 12500) (14551 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79315200 :
    ThetaLowerSegment 79315200 79331584 (7930249268167 / 100000) (7931838980649 / 100000) := by
  exact
    packedTile16384 79315200 79331584 11 874 8905 26 _ _ (1818893 / 100000) (113681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79331584 :
    ThetaLowerSegment 79331584 79347968 (7931838980649 / 100000) (3966738910631 / 50000) := by
  exact
    packedTile16384 79331584 79347968 11 901 8906 26 _ _ (1818913 / 100000) (454729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79347968 :
    ThetaLowerSegment 79347968 79364352 (3966738910631 / 50000) (3967562887733 / 50000) := by
  exact
    packedTile16384 79347968 79364352 11 906 8907 26 _ _ (909467 / 50000) (1818937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79364352 :
    ThetaLowerSegment 79364352 79380736 (3967562887733 / 50000) (3968388692849 / 50000) := by
  exact
    packedTile16384 79364352 79380736 11 908 8908 26 _ _ (909477 / 50000) (1818957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79380736 :
    ThetaLowerSegment 79380736 79397120 (3968388692849 / 50000) (992303172131 / 12500) := by
  exact
    packedTile16384 79380736 79397120 11 906 8909 26 _ _ (72759 / 4000) (909489 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79397120 :
    ThetaLowerSegment 79397120 79413504 (992303172131 / 12500) (496256860459 / 6250) := by
  exact
    packedTile16384 79397120 79413504 11 926 8910 26 _ _ (454749 / 25000) (1818999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79413504 :
    ThetaLowerSegment 79413504 79429888 (496256860459 / 6250) (49636213601 / 625) := by
  exact
    packedTile16384 79413504 79429888 11 926 8911 26 _ _ (227377 / 12500) (1819019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79429888 :
    ThetaLowerSegment 79429888 79446272 (49636213601 / 625) (7943378557387 / 100000) := by
  exact
    packedTile16384 79429888 79446272 11 871 8912 26 _ _ (1819037 / 100000) (11369 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79446272 :
    ThetaLowerSegment 79446272 79462656 (7943378557387 / 100000) (7945028442993 / 100000) := by
  exact
    packedTile16384 79446272 79462656 11 907 8913 26 _ _ (909529 / 50000) (1819061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79462656 :
    ThetaLowerSegment 79462656 79479040 (7945028442993 / 100000) (7946674708583 / 100000) := by
  exact
    packedTile16384 79462656 79479040 11 905 8914 26 _ _ (909539 / 50000) (1819081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79479040 :
    ThetaLowerSegment 79479040 79495424 (7946674708583 / 100000) (3974145943797 / 50000) := by
  exact
    packedTile16384 79479040 79495424 11 889 8915 26 _ _ (1819099 / 100000) (909551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79495424 :
    ThetaLowerSegment 79495424 79511808 (3974145943797 / 50000) (3974992744157 / 50000) := by
  exact
    packedTile16384 79495424 79511808 11 931 8916 26 _ _ (22739 / 1250) (1819123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79511808 :
    ThetaLowerSegment 79511808 79528192 (3974992744157 / 50000) (3975780431777 / 50000) := by
  exact
    packedTile16384 79511808 79528192 11 866 8916 26 _ _ (90957 / 5000) (1819143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79528192 :
    ThetaLowerSegment 79528192 79544576 (3975780431777 / 50000) (795322721503 / 10000) := by
  exact
    packedTile16384 79528192 79544576 11 916 8917 26 _ _ (1819161 / 100000) (454791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79544576 :
    ThetaLowerSegment 79544576 79560960 (795322721503 / 10000) (3977417685517 / 50000) := by
  exact
    packedTile16384 79544576 79560960 11 884 8918 26 _ _ (1819181 / 100000) (113699 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79560960 :
    ThetaLowerSegment 79560960 79577344 (3977417685517 / 50000) (497280336703 / 6250) := by
  exact
    packedTile16384 79560960 79577344 11 907 8919 26 _ _ (909601 / 50000) (363841 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79577344 :
    ThetaLowerSegment 79577344 79593728 (497280336703 / 6250) (1989529762151 / 25000) := by
  exact
    packedTile16384 79577344 79593728 11 898 8920 26 _ _ (909611 / 50000) (72769 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79593728 :
    ThetaLowerSegment 79593728 79610112 (1989529762151 / 25000) (99496772667 / 1250) := by
  exact
    packedTile16384 79593728 79610112 11 892 8921 26 _ _ (1819243 / 100000) (909623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79610112 :
    ThetaLowerSegment 79610112 79626496 (99496772667 / 1250) (497586992863 / 6250) := by
  exact
    packedTile16384 79610112 79626496 11 907 8922 26 _ _ (56852 / 3125) (1819267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79626496 :
    ThetaLowerSegment 79626496 79642880 (497586992863 / 6250) (995386387133 / 12500) := by
  exact
    packedTile16384 79626496 79642880 11 934 8923 26 _ _ (454821 / 25000) (1819287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79642880 :
    ThetaLowerSegment 79642880 79659264 (995386387133 / 12500) (7964759399749 / 100000) := by
  exact
    packedTile16384 79642880 79659264 11 917 8924 26 _ _ (363861 / 20000) (454827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79659264 :
    ThetaLowerSegment 79659264 79692032 (7964759399749 / 100000) (7967954134449 / 100000) := by
  exact
    packedTile16384 79659264 79692032 12 1756 8925 26 _ _ (72773 / 4000) (56854 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79692032 :
    ThetaLowerSegment 79692032 79708416 (7967954134449 / 100000) (1992398346029 / 25000) := by
  exact
    packedTile16384 79692032 79708416 11 901 8927 26 _ _ (1819367 / 100000) (181937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79708416 :
    ThetaLowerSegment 79708416 79724800 (1992398346029 / 25000) (3985646345787 / 50000) := by
  exact
    packedTile16384 79708416 79724800 11 934 8927 26 _ _ (1819387 / 100000) (181939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79724800 :
    ThetaLowerSegment 79724800 79741184 (3985646345787 / 50000) (3986455072643 / 50000) := by
  exact
    packedTile16384 79724800 79741184 11 889 8928 26 _ _ (113713 / 6250) (1819411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79741184 :
    ThetaLowerSegment 79741184 79757568 (3986455072643 / 50000) (797449850593 / 10000) := by
  exact
    packedTile16384 79741184 79757568 11 873 8929 26 _ _ (454857 / 25000) (1819431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79757568 :
    ThetaLowerSegment 79757568 79773952 (797449850593 / 10000) (7976115996091 / 100000) := by
  exact
    packedTile16384 79757568 79773952 11 889 8930 26 _ _ (1819449 / 100000) (454863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79773952 :
    ThetaLowerSegment 79773952 79790336 (7976115996091 / 100000) (3988879488299 / 50000) := by
  exact
    packedTile16384 79773952 79790336 11 903 8931 26 _ _ (1819469 / 100000) (113717 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79790336 :
    ThetaLowerSegment 79790336 79806720 (3988879488299 / 50000) (997425701881 / 12500) := by
  exact
    packedTile16384 79790336 79806720 11 905 8932 26 _ _ (181949 / 10000) (1819493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79806720 :
    ThetaLowerSegment 79806720 79823104 (997425701881 / 12500) (997629487001 / 12500) := by
  exact
    packedTile16384 79806720 79823104 11 896 8933 26 _ _ (181951 / 10000) (1819513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79823104 :
    ThetaLowerSegment 79823104 79839488 (997629487001 / 12500) (1995672007539 / 25000) := by
  exact
    packedTile16384 79823104 79839488 11 908 8934 26 _ _ (1819531 / 100000) (909767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79839488 :
    ThetaLowerSegment 79839488 79855872 (1995672007539 / 25000) (7984283776383 / 100000) := by
  exact
    packedTile16384 79839488 79855872 11 877 8935 26 _ _ (1819551 / 100000) (909777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79855872 :
    ThetaLowerSegment 79855872 79872256 (7984283776383 / 100000) (319439475831 / 4000) := by
  exact
    packedTile16384 79855872 79872256 11 936 8936 26 _ _ (454893 / 25000) (72783 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79872256 :
    ThetaLowerSegment 79872256 79888640 (319439475831 / 4000) (7987650002863 / 100000) := by
  exact
    packedTile16384 79872256 79888640 11 914 8937 26 _ _ (227449 / 12500) (363919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79888640 :
    ThetaLowerSegment 79888640 79905024 (7987650002863 / 100000) (3994621082119 / 50000) := by
  exact
    packedTile16384 79888640 79905024 11 875 8938 26 _ _ (1819613 / 100000) (56863 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79905024 :
    ThetaLowerSegment 79905024 79921408 (3994621082119 / 50000) (399543445807 / 5000) := by
  exact
    packedTile16384 79905024 79921408 11 894 8938 26 _ _ (1819633 / 100000) (454909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79921408 :
    ThetaLowerSegment 79921408 79937792 (399543445807 / 5000) (3996241474619 / 50000) := by
  exact
    packedTile16384 79921408 79937792 11 887 8939 26 _ _ (909827 / 50000) (1819657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79937792 :
    ThetaLowerSegment 79937792 79954176 (3996241474619 / 50000) (3997091262377 / 50000) := by
  exact
    packedTile16384 79937792 79954176 11 934 8940 26 _ _ (909837 / 50000) (1819677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79954176 :
    ThetaLowerSegment 79954176 79970560 (3997091262377 / 50000) (3997902846347 / 50000) := by
  exact
    packedTile16384 79954176 79970560 11 892 8941 26 _ _ (363939 / 20000) (909849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79970560 :
    ThetaLowerSegment 79970560 79986944 (3997902846347 / 50000) (7997427058759 / 100000) := by
  exact
    packedTile16384 79970560 79986944 11 891 8942 26 _ _ (363943 / 20000) (909859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell79986944 :
    ThetaLowerSegment 79986944 80003328 (7997427058759 / 100000) (7998972014623 / 100000) := by
  exact
    packedTile16384 79986944 80003328 11 849 8943 26 _ _ (227467 / 12500) (1819739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80003328 :
    ThetaLowerSegment 80003328 80019712 (7998972014623 / 100000) (8000566120879 / 100000) := by
  exact
    packedTile16384 80003328 80019712 11 876 8944 26 _ _ (454939 / 25000) (1819759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80019712 :
    ThetaLowerSegment 80019712 80036096 (8000566120879 / 100000) (8002167524639 / 100000) := by
  exact
    packedTile16384 80019712 80036096 11 880 8945 26 _ _ (1819777 / 100000) (90989 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80036096 :
    ThetaLowerSegment 80036096 80052480 (8002167524639 / 100000) (8003863575443 / 100000) := by
  exact
    packedTile16384 80036096 80052480 11 932 8946 26 _ _ (1819797 / 100000) (9099 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80052480 :
    ThetaLowerSegment 80052480 80068864 (8003863575443 / 100000) (8005446817103 / 100000) := by
  exact
    packedTile16384 80052480 80068864 11 870 8947 26 _ _ (909909 / 50000) (1819821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80068864 :
    ThetaLowerSegment 80068864 80085248 (8005446817103 / 100000) (1601429309159 / 20000) := by
  exact
    packedTile16384 80068864 80085248 11 934 8948 26 _ _ (909919 / 50000) (1819841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80085248 :
    ThetaLowerSegment 80085248 80101632 (1601429309159 / 20000) (8008824455793 / 100000) := by
  exact
    packedTile16384 80085248 80101632 11 922 8949 26 _ _ (1819859 / 100000) (909931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80101632 :
    ThetaLowerSegment 80101632 80118016 (8008824455793 / 100000) (500654465393 / 6250) := by
  exact
    packedTile16384 80101632 80118016 11 905 8949 26 _ _ (1819879 / 100000) (909941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80118016 :
    ThetaLowerSegment 80118016 80134400 (500654465393 / 6250) (2003024154247 / 25000) := by
  exact
    packedTile16384 80118016 80134400 11 893 8950 26 _ _ (18199 / 1000) (1819903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80134400 :
    ThetaLowerSegment 80134400 80150784 (2003024154247 / 25000) (2003431361347 / 25000) := by
  exact
    packedTile16384 80134400 80150784 11 895 8951 26 _ _ (22749 / 1250) (1819923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80150784 :
    ThetaLowerSegment 80150784 80167168 (2003431361347 / 25000) (8015332453291 / 100000) := by
  exact
    packedTile16384 80150784 80167168 11 883 8952 26 _ _ (1819941 / 100000) (227493 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80167168 :
    ThetaLowerSegment 80167168 80183552 (8015332453291 / 100000) (1002121529769 / 12500) := by
  exact
    packedTile16384 80167168 80183552 11 901 8953 26 _ _ (1819961 / 100000) (454991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80183552 :
    ThetaLowerSegment 80183552 80199936 (1002121529769 / 12500) (8018557441603 / 100000) := by
  exact
    packedTile16384 80183552 80199936 11 871 8954 26 _ _ (1819981 / 100000) (113749 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80199936 :
    ThetaLowerSegment 80199936 80216320 (8018557441603 / 100000) (1604037632679 / 20000) := by
  exact
    packedTile16384 80199936 80216320 11 896 8955 26 _ _ (910001 / 50000) (364001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80216320 :
    ThetaLowerSegment 80216320 80232704 (1604037632679 / 20000) (1604367056661 / 20000) := by
  exact
    packedTile16384 80216320 80232704 11 905 8956 26 _ _ (910011 / 50000) (72801 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80232704 :
    ThetaLowerSegment 80232704 80249088 (1604367056661 / 20000) (4011772151841 / 50000) := by
  exact
    packedTile16384 80232704 80249088 11 939 8957 26 _ _ (1820043 / 100000) (910023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80249088 :
    ThetaLowerSegment 80249088 80265472 (4011772151841 / 50000) (250786835008 / 3125) := by
  exact
    packedTile16384 80249088 80265472 11 898 8958 26 _ _ (1820063 / 100000) (910033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80265472 :
    ThetaLowerSegment 80265472 80281856 (250786835008 / 3125) (2006717394573 / 25000) := by
  exact
    packedTile16384 80265472 80281856 11 929 8959 26 _ _ (455021 / 25000) (1820087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80281856 :
    ThetaLowerSegment 80281856 80298240 (2006717394573 / 25000) (2007133743363 / 25000) := by
  exact
    packedTile16384 80281856 80298240 11 915 8960 26 _ _ (227513 / 12500) (1820107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80298240 :
    ThetaLowerSegment 80298240 80314624 (2007133743363 / 25000) (501886159089 / 6250) := by
  exact
    packedTile16384 80298240 80314624 11 903 8960 26 _ _ (455031 / 25000) (1820127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80314624 :
    ThetaLowerSegment 80314624 80331008 (501886159089 / 6250) (501988087209 / 6250) := by
  exact
    packedTile16384 80314624 80331008 11 896 8961 26 _ _ (364029 / 20000) (455037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80331008 :
    ThetaLowerSegment 80331008 80347392 (501988087209 / 6250) (4016718311427 / 50000) := by
  exact
    packedTile16384 80331008 80347392 11 894 8962 26 _ _ (364033 / 20000) (227521 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80347392 :
    ThetaLowerSegment 80347392 80363776 (4016718311427 / 50000) (160700986153 / 2000) := by
  exact
    packedTile16384 80347392 80363776 11 886 8963 26 _ _ (910093 / 50000) (1820189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80363776 :
    ThetaLowerSegment 80363776 80380160 (160700986153 / 2000) (4018329184877 / 50000) := by
  exact
    packedTile16384 80363776 80380160 11 884 8964 26 _ _ (910103 / 50000) (1820209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80380160 :
    ThetaLowerSegment 80380160 80396544 (4018329184877 / 50000) (1004793214907 / 12500) := by
  exact
    packedTile16384 80380160 80396544 11 927 8965 26 _ _ (910113 / 50000) (1820229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80396544 :
    ThetaLowerSegment 80396544 80412928 (1004793214907 / 12500) (402002109473 / 5000) := by
  exact
    packedTile16384 80396544 80412928 11 932 8966 26 _ _ (1820247 / 100000) (7281 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80412928 :
    ThetaLowerSegment 80412928 80429312 (402002109473 / 5000) (1608330625151 / 20000) := by
  exact
    packedTile16384 80412928 80429312 11 885 8967 26 _ _ (1820267 / 100000) (182027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80429312 :
    ThetaLowerSegment 80429312 80445696 (1608330625151 / 20000) (32173056319 / 400) := by
  exact
    packedTile16384 80429312 80445696 11 885 8968 26 _ _ (1820287 / 100000) (182029 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80445696 :
    ThetaLowerSegment 80445696 80462080 (32173056319 / 400) (4022479393249 / 50000) := by
  exact
    packedTile16384 80445696 80462080 11 931 8969 26 _ _ (455077 / 25000) (1820311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80462080 :
    ThetaLowerSegment 80462080 80478464 (4022479393249 / 50000) (4023298540849 / 50000) := by
  exact
    packedTile16384 80462080 80478464 11 900 8970 26 _ _ (227541 / 12500) (1820331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80478464 :
    ThetaLowerSegment 80478464 80494848 (4023298540849 / 50000) (4024114057201 / 50000) := by
  exact
    packedTile16384 80478464 80494848 11 896 8970 26 _ _ (1820349 / 100000) (56886 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80494848 :
    ThetaLowerSegment 80494848 80511232 (4024114057201 / 50000) (4024955067679 / 50000) := by
  exact
    packedTile16384 80494848 80511232 11 924 8971 26 _ _ (1820369 / 100000) (455093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80511232 :
    ThetaLowerSegment 80511232 80527616 (4024955067679 / 50000) (1610307148547 / 20000) := by
  exact
    packedTile16384 80511232 80527616 11 893 8972 26 _ _ (1820389 / 100000) (227549 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80527616 :
    ThetaLowerSegment 80527616 80544000 (1610307148547 / 20000) (1610622079477 / 20000) := by
  exact
    packedTile16384 80527616 80544000 11 865 8973 26 _ _ (182041 / 10000) (1820413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80544000 :
    ThetaLowerSegment 80544000 80560384 (1610622079477 / 20000) (64438252417 / 800) := by
  exact
    packedTile16384 80544000 80560384 11 918 8974 26 _ _ (182043 / 10000) (1820433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80560384 :
    ThetaLowerSegment 80560384 80576768 (64438252417 / 800) (322257016739 / 4000) := by
  exact
    packedTile16384 80560384 80576768 11 903 8975 26 _ _ (36409 / 2000) (1820453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80576768 :
    ThetaLowerSegment 80576768 80593152 (322257016739 / 4000) (8058034714839 / 100000) := by
  exact
    packedTile16384 80576768 80593152 11 884 8976 26 _ _ (1820471 / 100000) (910237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80593152 :
    ThetaLowerSegment 80593152 80609536 (8058034714839 / 100000) (1007455276049 / 12500) := by
  exact
    packedTile16384 80593152 80609536 11 883 8977 26 _ _ (1820491 / 100000) (910247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80609536 :
    ThetaLowerSegment 80609536 80625920 (1007455276049 / 12500) (4030631231591 / 50000) := by
  exact
    packedTile16384 80609536 80625920 11 890 8978 26 _ _ (1820511 / 100000) (910257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80625920 :
    ThetaLowerSegment 80625920 80642304 (4030631231591 / 50000) (4031468676311 / 50000) := by
  exact
    packedTile16384 80625920 80642304 11 920 8979 26 _ _ (455133 / 25000) (364107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80642304 :
    ThetaLowerSegment 80642304 80658688 (4031468676311 / 50000) (4032275180847 / 50000) := by
  exact
    packedTile16384 80642304 80658688 11 886 8980 26 _ _ (227569 / 12500) (364111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80658688 :
    ThetaLowerSegment 80658688 80675072 (4032275180847 / 50000) (4033093527961 / 50000) := by
  exact
    packedTile16384 80658688 80675072 11 899 8981 26 _ _ (455143 / 25000) (72823 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80675072 :
    ThetaLowerSegment 80675072 80691456 (4033093527961 / 50000) (8067801921913 / 100000) := by
  exact
    packedTile16384 80675072 80691456 11 887 8981 26 _ _ (1820593 / 100000) (455149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80691456 :
    ThetaLowerSegment 80691456 80707840 (8067801921913 / 100000) (8069469603421 / 100000) := by
  exact
    packedTile16384 80691456 80707840 11 916 8982 26 _ _ (1820613 / 100000) (227577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80707840 :
    ThetaLowerSegment 80707840 80724224 (8069469603421 / 100000) (2017771126223 / 25000) := by
  exact
    packedTile16384 80707840 80724224 11 887 8983 26 _ _ (1820633 / 100000) (455159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80724224 :
    ThetaLowerSegment 80724224 80740608 (2017771126223 / 25000) (2018186235107 / 25000) := by
  exact
    packedTile16384 80724224 80740608 11 912 8984 26 _ _ (1820653 / 100000) (113791 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80740608 :
    ThetaLowerSegment 80740608 80756992 (2018186235107 / 25000) (807442542253 / 10000) := by
  exact
    packedTile16384 80740608 80756992 11 923 8985 26 _ _ (910337 / 50000) (1820677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80756992 :
    ThetaLowerSegment 80756992 80773376 (807442542253 / 10000) (2019019197997 / 25000) := by
  exact
    packedTile16384 80756992 80773376 11 907 8986 26 _ _ (910347 / 50000) (1820697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80773376 :
    ThetaLowerSegment 80773376 80789760 (2019019197997 / 25000) (807772089673 / 10000) := by
  exact
    packedTile16384 80773376 80789760 11 903 8987 26 _ _ (910357 / 50000) (1820717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80789760 :
    ThetaLowerSegment 80789760 80806144 (807772089673 / 10000) (1615869362617 / 20000) := by
  exact
    packedTile16384 80789760 80806144 11 893 8988 26 _ _ (364147 / 20000) (910369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80806144 :
    ThetaLowerSegment 80806144 80822528 (1615869362617 / 20000) (808099823787 / 10000) := by
  exact
    packedTile16384 80806144 80822528 11 907 8989 26 _ _ (364151 / 20000) (910379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80822528 :
    ThetaLowerSegment 80822528 80838912 (808099823787 / 10000) (1616522653059 / 20000) := by
  exact
    packedTile16384 80822528 80838912 11 887 8990 26 _ _ (72831 / 4000) (910389 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80838912 :
    ThetaLowerSegment 80838912 80855296 (1616522653059 / 20000) (1616856951021 / 20000) := by
  exact
    packedTile16384 80838912 80855296 11 918 8991 26 _ _ (364159 / 20000) (910399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80855296 :
    ThetaLowerSegment 80855296 80871680 (1616856951021 / 20000) (8085989038881 / 100000) := by
  exact
    packedTile16384 80855296 80871680 11 936 8991 26 _ _ (113801 / 6250) (1820819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80871680 :
    ThetaLowerSegment 80871680 80904448 (8085989038881 / 100000) (8089244693649 / 100000) := by
  exact
    packedTile16384 80871680 80904448 12 1788 8992 26 _ _ (455209 / 25000) (1820839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80904448 :
    ThetaLowerSegment 80904448 80937216 (8089244693649 / 100000) (8092527733077 / 100000) := by
  exact
    packedTile16384 80904448 80937216 12 1803 8994 26 _ _ (455219 / 25000) (1820879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80937216 :
    ThetaLowerSegment 80937216 80969984 (8092527733077 / 100000) (1619162533469 / 20000) := by
  exact
    packedTile16384 80937216 80969984 12 1804 8996 26 _ _ (1820917 / 100000) (45523 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell80969984 :
    ThetaLowerSegment 80969984 81002752 (1619162533469 / 20000) (8099119525257 / 100000) := by
  exact
    packedTile16384 80969984 81002752 12 1816 8998 26 _ _ (1820957 / 100000) (11381 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81002752 :
    ThetaLowerSegment 81002752 81035520 (8099119525257 / 100000) (8102521149521 / 100000) := by
  exact
    packedTile16384 81002752 81035520 12 1868 9000 26 _ _ (910499 / 50000) (1821001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81035520 :
    ThetaLowerSegment 81035520 81068288 (8102521149521 / 100000) (8105793554807 / 100000) := by
  exact
    packedTile16384 81035520 81068288 12 1797 9001 26 _ _ (910519 / 50000) (1821041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81068288 :
    ThetaLowerSegment 81068288 81101056 (8105793554807 / 100000) (1013640993807 / 12500) := by
  exact
    packedTile16384 81068288 81101056 12 1831 9003 26 _ _ (1821079 / 100000) (910541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81101056 :
    ThetaLowerSegment 81101056 81133824 (1013640993807 / 12500) (1014056208939 / 12500) := by
  exact
    packedTile16384 81101056 81133824 12 1824 9005 26 _ _ (1821119 / 100000) (910561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81133824 :
    ThetaLowerSegment 81133824 81166592 (1014056208939 / 12500) (1014472343999 / 12500) := by
  exact
    packedTile16384 81133824 81166592 12 1828 9007 26 _ _ (45529 / 2500) (1821163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81166592 :
    ThetaLowerSegment 81166592 81199360 (1014472343999 / 12500) (1014876422749 / 12500) := by
  exact
    packedTile16384 81166592 81199360 12 1775 9009 26 _ _ (4553 / 250) (1821203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81199360 :
    ThetaLowerSegment 81199360 81232128 (1014876422749 / 12500) (1015281193339 / 12500) := by
  exact
    packedTile16384 81199360 81232128 12 1778 9011 26 _ _ (45531 / 2500) (1821243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81232128 :
    ThetaLowerSegment 81232128 81264896 (1015281193339 / 12500) (8125577027099 / 100000) := by
  exact
    packedTile16384 81232128 81264896 12 1827 9012 26 _ _ (1821281 / 100000) (455321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81264896 :
    ThetaLowerSegment 81264896 81297664 (8125577027099 / 100000) (8128789837343 / 100000) := by
  exact
    packedTile16384 81264896 81297664 12 1764 9014 26 _ _ (1821321 / 100000) (455331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81297664 :
    ThetaLowerSegment 81297664 81330432 (8128789837343 / 100000) (50825164974 / 625) := by
  exact
    packedTile16384 81297664 81330432 12 1777 9016 26 _ _ (1821361 / 100000) (455341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81330432 :
    ThetaLowerSegment 81330432 81363200 (50825164974 / 625) (4067669763039 / 50000) := by
  exact
    packedTile16384 81330432 81363200 12 1819 9018 26 _ _ (910701 / 50000) (364281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81363200 :
    ThetaLowerSegment 81363200 81395968 (4067669763039 / 50000) (4069301775071 / 50000) := by
  exact
    packedTile16384 81363200 81395968 12 1792 9020 26 _ _ (910721 / 50000) (364289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81395968 :
    ThetaLowerSegment 81395968 81428736 (4069301775071 / 50000) (814192593331 / 10000) := by
  exact
    packedTile16384 81395968 81428736 12 1824 9021 26 _ _ (910741 / 50000) (364297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81428736 :
    ThetaLowerSegment 81428736 81461504 (814192593331 / 10000) (4072631480807 / 50000) := by
  exact
    packedTile16384 81428736 81461504 12 1832 9023 26 _ _ (910761 / 50000) (72861 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81461504 :
    ThetaLowerSegment 81461504 81494272 (4072631480807 / 50000) (4074285460011 / 50000) := by
  exact
    packedTile16384 81461504 81494272 12 1816 9025 26 _ _ (1821563 / 100000) (910783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81494272 :
    ThetaLowerSegment 81494272 81527040 (4074285460011 / 50000) (8151749617257 / 100000) := by
  exact
    packedTile16384 81494272 81527040 12 1745 9027 26 _ _ (1821603 / 100000) (910803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81527040 :
    ThetaLowerSegment 81527040 81559808 (8151749617257 / 100000) (1631004257617 / 20000) := by
  exact
    packedTile16384 81527040 81559808 12 1796 9029 26 _ _ (1821643 / 100000) (910823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81559808 :
    ThetaLowerSegment 81559808 81592576 (1631004257617 / 20000) (81583094259 / 1000) := by
  exact
    packedTile16384 81559808 81592576 12 1805 9031 26 _ _ (1821683 / 100000) (910843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81592576 :
    ThetaLowerSegment 81592576 81625344 (81583094259 / 1000) (81615885273 / 1000) := by
  exact
    packedTile16384 81592576 81625344 12 1800 9032 26 _ _ (1821723 / 100000) (910863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81625344 :
    ThetaLowerSegment 81625344 81658112 (81615885273 / 1000) (2041209638569 / 25000) := by
  exact
    packedTile16384 81625344 81658112 12 1784 9034 26 _ _ (455441 / 25000) (1821767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81658112 :
    ThetaLowerSegment 81658112 81690880 (2041209638569 / 25000) (2042043113899 / 25000) := by
  exact
    packedTile16384 81658112 81690880 12 1830 9036 26 _ _ (455451 / 25000) (1821807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81690880 :
    ThetaLowerSegment 81690880 81723648 (2042043113899 / 25000) (255355192129 / 3125) := by
  exact
    packedTile16384 81690880 81723648 12 1753 9038 26 _ _ (455461 / 25000) (1821847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81723648 :
    ThetaLowerSegment 81723648 81756416 (255355192129 / 3125) (2043665484071 / 25000) := by
  exact
    packedTile16384 81723648 81756416 12 1809 9040 26 _ _ (455471 / 25000) (1821887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81756416 :
    ThetaLowerSegment 81756416 81789184 (2043665484071 / 25000) (511119173933 / 6250) := by
  exact
    packedTile16384 81756416 81789184 12 1781 9041 26 _ _ (455481 / 25000) (1821927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81789184 :
    ThetaLowerSegment 81789184 81821952 (511119173933 / 6250) (2045291569131 / 25000) := by
  exact
    packedTile16384 81789184 81821952 12 1789 9043 26 _ _ (455491 / 25000) (1821967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81821952 :
    ThetaLowerSegment 81821952 81854720 (2045291569131 / 25000) (2046120580951 / 25000) := by
  exact
    packedTile16384 81821952 81854720 12 1820 9045 26 _ _ (455501 / 25000) (1822007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81854720 :
    ThetaLowerSegment 81854720 81887488 (2046120580951 / 25000) (255866594633 / 3125) := by
  exact
    packedTile16384 81854720 81887488 12 1783 9047 26 _ _ (455511 / 25000) (1822047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81887488 :
    ThetaLowerSegment 81887488 81920256 (255866594633 / 3125) (2047752239343 / 25000) := by
  exact
    packedTile16384 81887488 81920256 12 1799 9049 26 _ _ (455521 / 25000) (1822087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81920256 :
    ThetaLowerSegment 81920256 81953024 (2047752239343 / 25000) (2048574017267 / 25000) := by
  exact
    packedTile16384 81920256 81953024 12 1804 9050 26 _ _ (455531 / 25000) (1822127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81953024 :
    ThetaLowerSegment 81953024 81985792 (2048574017267 / 25000) (204939535769 / 2500) := by
  exact
    packedTile16384 81953024 81985792 12 1803 9052 26 _ _ (455541 / 25000) (1822167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell81985792 :
    ThetaLowerSegment 81985792 82018560 (204939535769 / 2500) (512559076209 / 6250) := by
  exact
    packedTile16384 81985792 82018560 12 1846 9054 26 _ _ (455551 / 25000) (1822207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82018560 :
    ThetaLowerSegment 82018560 82051328 (512559076209 / 6250) (2051054947953 / 25000) := by
  exact
    packedTile16384 82018560 82051328 12 1797 9056 26 _ _ (455561 / 25000) (1822247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82051328 :
    ThetaLowerSegment 82051328 82084096 (2051054947953 / 25000) (2051890465167 / 25000) := by
  exact
    packedTile16384 82051328 82084096 12 1834 9058 26 _ _ (455571 / 25000) (1822287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82084096 :
    ThetaLowerSegment 82084096 82116864 (2051890465167 / 25000) (256586365123 / 3125) := by
  exact
    packedTile16384 82084096 82116864 12 1757 9060 26 _ _ (455581 / 25000) (1822327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82116864 :
    ThetaLowerSegment 82116864 82149632 (256586365123 / 3125) (1026760503893 / 12500) := by
  exact
    packedTile16384 82116864 82149632 12 1822 9061 26 _ _ (455591 / 25000) (1822367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82149632 :
    ThetaLowerSegment 82149632 82182400 (1026760503893 / 12500) (1027165988783 / 12500) := by
  exact
    packedTile16384 82149632 82182400 12 1780 9063 26 _ _ (455601 / 25000) (1822407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82182400 :
    ThetaLowerSegment 82182400 82215168 (1027165988783 / 12500) (1027564192797 / 12500) := by
  exact
    packedTile16384 82182400 82215168 12 1748 9065 26 _ _ (455611 / 25000) (1822447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82215168 :
    ThetaLowerSegment 82215168 82247936 (1027564192797 / 12500) (2055938024111 / 25000) := by
  exact
    packedTile16384 82215168 82247936 12 1777 9067 26 _ _ (455621 / 25000) (1822487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82247936 :
    ThetaLowerSegment 82247936 82280704 (2055938024111 / 25000) (4113496271169 / 50000) := by
  exact
    packedTile16384 82247936 82280704 12 1778 9069 26 _ _ (1822523 / 100000) (911263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82280704 :
    ThetaLowerSegment 82280704 82313472 (4113496271169 / 50000) (8230245817293 / 100000) := by
  exact
    packedTile16384 82280704 82313472 12 1785 9070 26 _ _ (1822563 / 100000) (911283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82313472 :
    ThetaLowerSegment 82313472 82346240 (8230245817293 / 100000) (164671222643 / 2000) := by
  exact
    packedTile16384 82313472 82346240 12 1819 9072 26 _ _ (1822603 / 100000) (911303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82346240 :
    ThetaLowerSegment 82346240 82379008 (164671222643 / 2000) (8236825485763 / 100000) := by
  exact
    packedTile16384 82346240 82379008 12 1791 9074 26 _ _ (1822643 / 100000) (911323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82379008 :
    ThetaLowerSegment 82379008 82411776 (8236825485763 / 100000) (8240091733699 / 100000) := by
  exact
    packedTile16384 82379008 82411776 12 1792 9076 26 _ _ (1822683 / 100000) (911343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82411776 :
    ThetaLowerSegment 82411776 82444544 (8240091733699 / 100000) (8243425492237 / 100000) := by
  exact
    packedTile16384 82411776 82444544 12 1829 9078 26 _ _ (911361 / 50000) (72909 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82444544 :
    ThetaLowerSegment 82444544 82477312 (8243425492237 / 100000) (1649344573739 / 20000) := by
  exact
    packedTile16384 82444544 82477312 12 1809 9079 26 _ _ (911381 / 50000) (364553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82477312 :
    ThetaLowerSegment 82477312 82510080 (1649344573739 / 20000) (329995781767 / 4000) := by
  exact
    packedTile16384 82477312 82510080 12 1740 9081 26 _ _ (911401 / 50000) (364561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82510080 :
    ThetaLowerSegment 82510080 82542848 (329995781767 / 4000) (8253223053667 / 100000) := by
  exact
    packedTile16384 82510080 82542848 12 1826 9083 26 _ _ (911421 / 50000) (364569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82542848 :
    ThetaLowerSegment 82542848 82575616 (8253223053667 / 100000) (825650970811 / 10000) := by
  exact
    packedTile16384 82542848 82575616 12 1803 9085 26 _ _ (1822881 / 100000) (455721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82575616 :
    ThetaLowerSegment 82575616 82608384 (825650970811 / 10000) (4129888191271 / 50000) := by
  exact
    packedTile16384 82575616 82608384 12 1792 9087 26 _ _ (1822921 / 100000) (455731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82608384 :
    ThetaLowerSegment 82608384 82641152 (4129888191271 / 50000) (8263023076083 / 100000) := by
  exact
    packedTile16384 82608384 82641152 12 1781 9088 26 _ _ (1822961 / 100000) (455741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82641152 :
    ThetaLowerSegment 82641152 82673920 (8263023076083 / 100000) (8266313591083 / 100000) := by
  exact
    packedTile16384 82641152 82673920 12 1805 9090 26 _ _ (1823 / 100) (1823003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82673920 :
    ThetaLowerSegment 82673920 82706688 (8266313591083 / 100000) (8269673453803 / 100000) := by
  exact
    packedTile16384 82673920 82706688 12 1843 9092 26 _ _ (11394 / 625) (1823043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82706688 :
    ThetaLowerSegment 82706688 82739456 (8269673453803 / 100000) (8272938590083 / 100000) := by
  exact
    packedTile16384 82706688 82739456 12 1791 9094 26 _ _ (45577 / 2500) (1823083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82739456 :
    ThetaLowerSegment 82739456 82772224 (8272938590083 / 100000) (2069032717863 / 25000) := by
  exact
    packedTile16384 82739456 82772224 12 1751 9096 26 _ _ (1823119 / 100000) (911561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82772224 :
    ThetaLowerSegment 82772224 82804992 (2069032717863 / 25000) (8279545648259 / 100000) := by
  exact
    packedTile16384 82772224 82804992 12 1873 9097 26 _ _ (1823159 / 100000) (911581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82804992 :
    ThetaLowerSegment 82804992 82837760 (8279545648259 / 100000) (8282838343847 / 100000) := by
  exact
    packedTile16384 82804992 82837760 12 1806 9099 26 _ _ (911599 / 50000) (1823201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82837760 :
    ThetaLowerSegment 82837760 82870528 (8282838343847 / 100000) (8286171222911 / 100000) := by
  exact
    packedTile16384 82837760 82870528 12 1828 9101 26 _ _ (911619 / 50000) (1823241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82870528 :
    ThetaLowerSegment 82870528 82903296 (8286171222911 / 100000) (8289434890531 / 100000) := by
  exact
    packedTile16384 82870528 82903296 12 1790 9103 26 _ _ (911639 / 50000) (1823281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82903296 :
    ThetaLowerSegment 82903296 82936064 (8289434890531 / 100000) (8292713214497 / 100000) := by
  exact
    packedTile16384 82903296 82936064 12 1798 9105 26 _ _ (1823317 / 100000) (45583 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82936064 :
    ThetaLowerSegment 82936064 82968832 (8292713214497 / 100000) (4147998540227 / 50000) := by
  exact
    packedTile16384 82936064 82968832 12 1801 9106 26 _ _ (1823357 / 100000) (11396 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell82968832 :
    ThetaLowerSegment 82968832 83001600 (4147998540227 / 50000) (4149629567949 / 50000) := by
  exact
    packedTile16384 82968832 83001600 12 1789 9108 26 _ _ (455849 / 25000) (1823399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83001600 :
    ThetaLowerSegment 83001600 83034368 (4149629567949 / 50000) (4151298923607 / 50000) := by
  exact
    packedTile16384 83001600 83034368 12 1831 9110 26 _ _ (455859 / 25000) (1823439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83034368 :
    ThetaLowerSegment 83034368 83067136 (4151298923607 / 50000) (2076449055591 / 25000) := by
  exact
    packedTile16384 83034368 83067136 12 1754 9112 26 _ _ (72939 / 4000) (911739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83067136 :
    ThetaLowerSegment 83067136 83099904 (2076449055591 / 25000) (830902201863 / 10000) := by
  exact
    packedTile16384 83067136 83099904 12 1769 9114 26 _ _ (911757 / 50000) (1823517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83099904 :
    ThetaLowerSegment 83099904 83132672 (830902201863 / 10000) (2078068353853 / 25000) := by
  exact
    packedTile16384 83099904 83132672 12 1783 9115 26 _ _ (911777 / 50000) (1823557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83132672 :
    ThetaLowerSegment 83132672 83165440 (2078068353853 / 25000) (332621578819 / 4000) := by
  exact
    packedTile16384 83132672 83165440 12 1791 9117 26 _ _ (1823593 / 100000) (455899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83165440 :
    ThetaLowerSegment 83165440 83198208 (332621578819 / 4000) (4159380914993 / 50000) := by
  exact
    packedTile16384 83165440 83198208 12 1767 9119 26 _ _ (1823633 / 100000) (455909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83198208 :
    ThetaLowerSegment 83198208 83230976 (4159380914993 / 50000) (4160997600221 / 50000) := by
  exact
    packedTile16384 83198208 83230976 12 1773 9121 26 _ _ (227959 / 12500) (72947 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83230976 :
    ThetaLowerSegment 83230976 83263744 (4160997600221 / 50000) (4162621615757 / 50000) := by
  exact
    packedTile16384 83230976 83263744 12 1781 9123 26 _ _ (56991 / 3125) (364743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83263744 :
    ThetaLowerSegment 83263744 83296512 (4162621615757 / 50000) (260268374714 / 3125) := by
  exact
    packedTile16384 83263744 83296512 12 1834 9124 26 _ _ (1823751 / 100000) (911877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83296512 :
    ThetaLowerSegment 83296512 83329280 (260268374714 / 3125) (2082959496157 / 25000) := by
  exact
    packedTile16384 83296512 83329280 12 1782 9126 26 _ _ (182379 / 10000) (1823793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83329280 :
    ThetaLowerSegment 83329280 83362048 (2082959496157 / 25000) (1041886006211 / 12500) := by
  exact
    packedTile16384 83329280 83362048 12 1782 9128 26 _ _ (182383 / 10000) (1823833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83362048 :
    ThetaLowerSegment 83362048 83394816 (1041886006211 / 12500) (8338343655853 / 100000) := by
  exact
    packedTile16384 83362048 83394816 12 1785 9130 26 _ _ (1823869 / 100000) (56996 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83394816 :
    ThetaLowerSegment 83394816 83427584 (8338343655853 / 100000) (8341641281517 / 100000) := by
  exact
    packedTile16384 83394816 83427584 12 1808 9132 26 _ _ (455977 / 25000) (1823911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83427584 :
    ThetaLowerSegment 83427584 83460352 (8341641281517 / 100000) (8344909794541 / 100000) := by
  exact
    packedTile16384 83427584 83460352 12 1792 9133 26 _ _ (1823947 / 100000) (36479 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83460352 :
    ThetaLowerSegment 83460352 83493120 (8344909794541 / 100000) (1669642971797 / 20000) := by
  exact
    packedTile16384 83460352 83493120 12 1812 9135 26 _ _ (1823987 / 100000) (182399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83493120 :
    ThetaLowerSegment 83493120 83525888 (1669642971797 / 20000) (8351490809681 / 100000) := by
  exact
    packedTile16384 83493120 83525888 12 1796 9137 26 _ _ (912013 / 50000) (1824029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83525888 :
    ThetaLowerSegment 83525888 83558656 (8351490809681 / 100000) (8354755886031 / 100000) := by
  exact
    packedTile16384 83525888 83558656 12 1790 9139 26 _ _ (364813 / 20000) (456017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83558656 :
    ThetaLowerSegment 83558656 83591424 (8354755886031 / 100000) (8358024680399 / 100000) := by
  exact
    packedTile16384 83558656 83591424 12 1792 9141 26 _ _ (228013 / 12500) (1824107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83591424 :
    ThetaLowerSegment 83591424 83624192 (8358024680399 / 100000) (8361330029327 / 100000) := by
  exact
    packedTile16384 83591424 83624192 12 1812 9142 26 _ _ (114009 / 6250) (1824147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83624192 :
    ThetaLowerSegment 83624192 83656960 (8361330029327 / 100000) (8364500459381 / 100000) := by
  exact
    packedTile16384 83624192 83656960 12 1738 9144 26 _ _ (1824183 / 100000) (912093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83656960 :
    ThetaLowerSegment 83656960 83689728 (8364500459381 / 100000) (8367762168317 / 100000) := by
  exact
    packedTile16384 83656960 83689728 12 1788 9146 26 _ _ (912111 / 50000) (72969 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83689728 :
    ThetaLowerSegment 83689728 83722496 (8367762168317 / 100000) (4185520182667 / 50000) := by
  exact
    packedTile16384 83689728 83722496 12 1797 9148 26 _ _ (1824261 / 100000) (228033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83722496 :
    ThetaLowerSegment 83722496 83755264 (4185520182667 / 50000) (4187198538667 / 50000) := by
  exact
    packedTile16384 83722496 83755264 12 1840 9149 26 _ _ (18243 / 1000) (1824303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83755264 :
    ThetaLowerSegment 83755264 83788032 (4187198538667 / 50000) (1675532163961 / 20000) := by
  exact
    packedTile16384 83755264 83788032 12 1789 9151 26 _ _ (1824339 / 100000) (912171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83788032 :
    ThetaLowerSegment 83788032 83820800 (1675532163961 / 20000) (523809157899 / 6250) := by
  exact
    packedTile16384 83788032 83820800 12 1801 9153 26 _ _ (1824379 / 100000) (912191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83820800 :
    ThetaLowerSegment 83820800 83853568 (523809157899 / 6250) (4192145342289 / 50000) := by
  exact
    packedTile16384 83820800 83853568 12 1833 9155 26 _ _ (912209 / 50000) (1824421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83853568 :
    ThetaLowerSegment 83853568 83886336 (4192145342289 / 50000) (4193794651417 / 50000) := by
  exact
    packedTile16384 83853568 83886336 12 1808 9157 26 _ _ (1824457 / 100000) (91223 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83886336 :
    ThetaLowerSegment 83886336 83919104 (4193794651417 / 50000) (4195440346809 / 50000) := by
  exact
    packedTile16384 83886336 83919104 12 1804 9158 26 _ _ (114031 / 6250) (1824499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83919104 :
    ThetaLowerSegment 83919104 83951872 (4195440346809 / 50000) (8394268855113 / 100000) := by
  exact
    packedTile16384 83919104 83951872 12 1857 9160 26 _ _ (364907 / 20000) (912269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83951872 :
    ThetaLowerSegment 83951872 83984640 (8394268855113 / 100000) (8397562211183 / 100000) := by
  exact
    packedTile16384 83951872 83984640 12 1805 9162 26 _ _ (912287 / 50000) (1824577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell83984640 :
    ThetaLowerSegment 83984640 84017408 (8397562211183 / 100000) (8400813671549 / 100000) := by
  exact
    packedTile16384 83984640 84017408 12 1782 9164 26 _ _ (1824613 / 100000) (228077 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84017408 :
    ThetaLowerSegment 84017408 84050176 (8400813671549 / 100000) (8404074324673 / 100000) := by
  exact
    packedTile16384 84017408 84050176 12 1787 9166 26 _ _ (456163 / 25000) (364931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84050176 :
    ThetaLowerSegment 84050176 84082944 (8404074324673 / 100000) (8407249287013 / 100000) := by
  exact
    packedTile16384 84050176 84082944 12 1740 9167 26 _ _ (1824691 / 100000) (912347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84082944 :
    ThetaLowerSegment 84082944 84115712 (8407249287013 / 100000) (8410508254793 / 100000) := by
  exact
    packedTile16384 84082944 84115712 12 1786 9169 26 _ _ (182473 / 10000) (1824733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84115712 :
    ThetaLowerSegment 84115712 84148480 (8410508254793 / 100000) (4206897331881 / 50000) := by
  exact
    packedTile16384 84115712 84148480 12 1801 9171 26 _ _ (1824769 / 100000) (456193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84148480 :
    ThetaLowerSegment 84148480 84181248 (4206897331881 / 50000) (4208511374557 / 50000) := by
  exact
    packedTile16384 84148480 84181248 12 1769 9173 26 _ _ (228101 / 12500) (1824811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84181248 :
    ThetaLowerSegment 84181248 84214016 (4208511374557 / 50000) (8420254553151 / 100000) := by
  exact
    packedTile16384 84181248 84214016 12 1771 9175 26 _ _ (1824847 / 100000) (36497 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84214016 :
    ThetaLowerSegment 84214016 84246784 (8420254553151 / 100000) (8423521099091 / 100000) := by
  exact
    packedTile16384 84214016 84246784 12 1790 9176 26 _ _ (912443 / 50000) (1824889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84246784 :
    ThetaLowerSegment 84246784 84279552 (8423521099091 / 100000) (2106696472479 / 25000) := by
  exact
    packedTile16384 84246784 84279552 12 1789 9178 26 _ _ (72997 / 4000) (57029 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84279552 :
    ThetaLowerSegment 84279552 84312320 (2106696472479 / 25000) (4215044536473 / 50000) := by
  exact
    packedTile16384 84279552 84312320 12 1810 9180 26 _ _ (1824963 / 100000) (912483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84312320 :
    ThetaLowerSegment 84312320 84345088 (4215044536473 / 50000) (4216690688277 / 50000) := by
  exact
    packedTile16384 84312320 84345088 12 1804 9182 26 _ _ (912501 / 50000) (365001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84345088 :
    ThetaLowerSegment 84345088 84377856 (4216690688277 / 50000) (8436653675067 / 100000) := by
  exact
    packedTile16384 84345088 84377856 12 1793 9183 26 _ _ (1825041 / 100000) (456261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84377856 :
    ThetaLowerSegment 84377856 84410624 (8436653675067 / 100000) (8439880416507 / 100000) := by
  exact
    packedTile16384 84377856 84410624 12 1768 9185 26 _ _ (45627 / 2500) (1825083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84410624 :
    ThetaLowerSegment 84410624 84443392 (8439880416507 / 100000) (8443165630707 / 100000) := by
  exact
    packedTile16384 84410624 84443392 12 1800 9187 26 _ _ (1825119 / 100000) (912561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84443392 :
    ThetaLowerSegment 84443392 84476160 (8443165630707 / 100000) (8446511145321 / 100000) := by
  exact
    packedTile16384 84443392 84476160 12 1833 9189 26 _ _ (912579 / 50000) (1825161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84476160 :
    ThetaLowerSegment 84476160 84508928 (8446511145321 / 100000) (8449845778413 / 100000) := by
  exact
    packedTile16384 84476160 84508928 12 1827 9191 26 _ _ (456299 / 25000) (1825199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84508928 :
    ThetaLowerSegment 84508928 84541696 (8449845778413 / 100000) (528318076313 / 6250) := by
  exact
    packedTile16384 84508928 84541696 12 1777 9192 26 _ _ (365047 / 20000) (912619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84541696 :
    ThetaLowerSegment 84541696 84574464 (528318076313 / 6250) (4228179143371 / 50000) := by
  exact
    packedTile16384 84541696 84574464 12 1791 9194 26 _ _ (912637 / 50000) (1825277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84574464 :
    ThetaLowerSegment 84574464 84607232 (4228179143371 / 50000) (8459594566691 / 100000) := by
  exact
    packedTile16384 84574464 84607232 12 1773 9196 26 _ _ (1825313 / 100000) (456329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84607232 :
    ThetaLowerSegment 84607232 84640000 (8459594566691 / 100000) (1692562167383 / 20000) := by
  exact
    packedTile16384 84607232 84640000 12 1762 9198 26 _ _ (228169 / 12500) (365071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84640000 :
    ThetaLowerSegment 84640000 84672768 (1692562167383 / 20000) (67728611677 / 800) := by
  exact
    packedTile16384 84640000 84672768 12 1789 9200 26 _ _ (182539 / 10000) (1825393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84672768 :
    ThetaLowerSegment 84672768 84705536 (67728611677 / 800) (4234689330343 / 50000) := by
  exact
    packedTile16384 84672768 84705536 12 1809 9201 26 _ _ (1825429 / 100000) (228179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84705536 :
    ThetaLowerSegment 84705536 84738304 (4234689330343 / 50000) (4236322211469 / 50000) := by
  exact
    packedTile16384 84705536 84738304 12 1789 9203 26 _ _ (456367 / 25000) (1825471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84738304 :
    ThetaLowerSegment 84738304 84771072 (4236322211469 / 50000) (1059489238023 / 12500) := by
  exact
    packedTile16384 84738304 84771072 12 1791 9205 26 _ _ (912753 / 50000) (1825509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84771072 :
    ThetaLowerSegment 84771072 84803840 (1059489238023 / 12500) (4239605419227 / 50000) := by
  exact
    packedTile16384 84771072 84803840 12 1806 9207 26 _ _ (365109 / 20000) (456387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84803840 :
    ThetaLowerSegment 84803840 84836608 (4239605419227 / 50000) (4241231101779 / 50000) := by
  exact
    packedTile16384 84803840 84836608 12 1781 9208 26 _ _ (114099 / 6250) (1825587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84836608 :
    ThetaLowerSegment 84836608 84869376 (4241231101779 / 50000) (424287507439 / 5000) := by
  exact
    packedTile16384 84836608 84869376 12 1801 9210 26 _ _ (912811 / 50000) (2921 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84869376 :
    ThetaLowerSegment 84869376 84902144 (424287507439 / 5000) (2122244479357 / 25000) := by
  exact
    packedTile16384 84869376 84902144 12 1768 9212 26 _ _ (1825661 / 100000) (57052 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84902144 :
    ThetaLowerSegment 84902144 84934912 (2122244479357 / 25000) (8492167413581 / 100000) := by
  exact
    packedTile16384 84902144 84934912 12 1747 9214 26 _ _ (1825699 / 100000) (912851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84934912 :
    ThetaLowerSegment 84934912 84967680 (8492167413581 / 100000) (8495534074453 / 100000) := by
  exact
    packedTile16384 84934912 84967680 12 1844 9216 26 _ _ (912869 / 50000) (1825741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell84967680 :
    ThetaLowerSegment 84967680 85000448 (8495534074453 / 100000) (8498809518391 / 100000) := by
  exact
    packedTile16384 84967680 85000448 12 1794 9217 26 _ _ (1825777 / 100000) (91289 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85000448 :
    ThetaLowerSegment 85000448 85033216 (8498809518391 / 100000) (8501953571821 / 100000) := by
  exact
    packedTile16384 85000448 85033216 12 1722 9219 26 _ _ (365163 / 20000) (912909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85033216 :
    ThetaLowerSegment 85033216 85049600 (8501953571821 / 100000) (8503582233589 / 100000) := by
  exact
    packedTile16384 85033216 85049600 11 892 9221 26 _ _ (912927 / 50000) (1825857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85049600 :
    ThetaLowerSegment 85049600 85065984 (8503582233589 / 100000) (8505258385003 / 100000) := by
  exact
    packedTile16384 85049600 85065984 11 918 9222 26 _ _ (1825873 / 100000) (456469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85065984 :
    ThetaLowerSegment 85065984 85082368 (8505258385003 / 100000) (8506881602991 / 100000) := by
  exact
    packedTile16384 85065984 85082368 11 889 9223 26 _ _ (456473 / 25000) (365179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85082368 :
    ThetaLowerSegment 85082368 85098752 (8506881602991 / 100000) (8508581527063 / 100000) := by
  exact
    packedTile16384 85082368 85098752 11 931 9224 26 _ _ (228239 / 12500) (365183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85098752 :
    ThetaLowerSegment 85098752 85131520 (8508581527063 / 100000) (4255898495777 / 50000) := by
  exact
    packedTile16384 85098752 85131520 12 1761 9224 26 _ _ (1825931 / 100000) (912967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85131520 :
    ThetaLowerSegment 85131520 85147904 (4255898495777 / 50000) (851348418691 / 10000) := by
  exact
    packedTile16384 85131520 85147904 11 924 9226 26 _ _ (1825969 / 100000) (456493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85147904 :
    ThetaLowerSegment 85147904 85180672 (851348418691 / 10000) (8516721665407 / 100000) := by
  exact
    packedTile16384 85147904 85180672 12 1773 9227 26 _ _ (1825989 / 100000) (228249 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85180672 :
    ThetaLowerSegment 85180672 85197056 (8516721665407 / 100000) (8518328569167 / 100000) := by
  exact
    packedTile16384 85180672 85197056 11 880 9229 26 _ _ (1826027 / 100000) (182603 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85197056 :
    ThetaLowerSegment 85197056 85213440 (8518328569167 / 100000) (340798734339 / 4000) := by
  exact
    packedTile16384 85197056 85213440 11 898 9230 26 _ _ (913023 / 50000) (1826049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85213440 :
    ThetaLowerSegment 85213440 85229824 (340798734339 / 4000) (170431323307 / 2000) := by
  exact
    packedTile16384 85213440 85229824 11 875 9231 26 _ _ (365213 / 20000) (456517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85229824 :
    ThetaLowerSegment 85229824 85246208 (170431323307 / 2000) (1704644484889 / 20000) := by
  exact
    packedTile16384 85229824 85246208 11 907 9232 26 _ _ (365217 / 20000) (228261 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85246208 :
    ThetaLowerSegment 85246208 85262592 (1704644484889 / 20000) (8524937136101 / 100000) := by
  exact
    packedTile16384 85246208 85262592 11 939 9232 26 _ _ (228263 / 12500) (1826107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85262592 :
    ThetaLowerSegment 85262592 85295360 (8524937136101 / 100000) (8528125546859 / 100000) := by
  exact
    packedTile16384 85262592 85295360 12 1746 9233 26 _ _ (1826123 / 100000) (913063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85295360 :
    ThetaLowerSegment 85295360 85311744 (8528125546859 / 100000) (8529791006603 / 100000) := by
  exact
    packedTile16384 85295360 85311744 11 912 9235 26 _ _ (913081 / 50000) (365233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85311744 :
    ThetaLowerSegment 85311744 85328128 (8529791006603 / 100000) (1706294949097 / 20000) := by
  exact
    packedTile16384 85311744 85328128 11 922 9236 26 _ _ (1826181 / 100000) (228273 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85328128 :
    ThetaLowerSegment 85328128 85360896 (1706294949097 / 20000) (1706943615337 / 20000) := by
  exact
    packedTile16384 85328128 85360896 12 1776 9237 26 _ _ (9131 / 500) (1826203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85360896 :
    ThetaLowerSegment 85360896 85377280 (1706943615337 / 20000) (1707275990653 / 20000) := by
  exact
    packedTile16384 85360896 85377280 11 910 9239 26 _ _ (913119 / 50000) (1826241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85377280 :
    ThetaLowerSegment 85377280 85393664 (1707275990653 / 20000) (8538043674303 / 100000) := by
  exact
    packedTile16384 85377280 85393664 11 911 9239 26 _ _ (913129 / 50000) (1826261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85393664 :
    ThetaLowerSegment 85393664 85426432 (8538043674303 / 100000) (1067672991867 / 12500) := by
  exact
    packedTile16384 85393664 85426432 12 1829 9240 26 _ _ (1826277 / 100000) (45657 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85426432 :
    ThetaLowerSegment 85426432 85459200 (1067672991867 / 12500) (534041956371 / 6250) := by
  exact
    packedTile16384 85426432 85459200 12 1800 9242 26 _ _ (365263 / 20000) (913159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85459200 :
    ThetaLowerSegment 85459200 85491968 (534041956371 / 6250) (2136980552569 / 25000) := by
  exact
    packedTile16384 85459200 85491968 12 1780 9244 26 _ _ (1826353 / 100000) (456589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85491968 :
    ThetaLowerSegment 85491968 85524736 (2136980552569 / 25000) (2137822062683 / 25000) := by
  exact
    packedTile16384 85491968 85524736 12 1843 9246 26 _ _ (228299 / 12500) (365279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85524736 :
    ThetaLowerSegment 85524736 85557504 (2137822062683 / 25000) (4277281519861 / 50000) := by
  exact
    packedTile16384 85524736 85557504 12 1793 9247 26 _ _ (182643 / 10000) (1826433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85557504 :
    ThetaLowerSegment 85557504 85590272 (4277281519861 / 50000) (4278886985233 / 50000) := by
  exact
    packedTile16384 85557504 85590272 12 1758 9249 26 _ _ (456617 / 25000) (1826471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85590272 :
    ThetaLowerSegment 85590272 85623040 (4278886985233 / 50000) (342441517539 / 4000) := by
  exact
    packedTile16384 85590272 85623040 12 1787 9251 26 _ _ (1826507 / 100000) (182651 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85623040 :
    ThetaLowerSegment 85623040 85655808 (342441517539 / 4000) (428217107919 / 5000) := by
  exact
    packedTile16384 85623040 85655808 12 1809 9253 26 _ _ (365309 / 20000) (456637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85655808 :
    ThetaLowerSegment 85655808 85688576 (428217107919 / 5000) (171352234839 / 2000) := by
  exact
    packedTile16384 85655808 85688576 12 1790 9255 26 _ _ (1826583 / 100000) (913293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85688576 :
    ThetaLowerSegment 85688576 85721344 (171352234839 / 2000) (4285407818469 / 50000) := by
  exact
    packedTile16384 85688576 85721344 12 1754 9256 26 _ _ (913311 / 50000) (14613 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85721344 :
    ThetaLowerSegment 85721344 85754112 (4285407818469 / 50000) (4287062772429 / 50000) := by
  exact
    packedTile16384 85721344 85754112 12 1812 9258 26 _ _ (91333 / 5000) (1826663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85754112 :
    ThetaLowerSegment 85754112 85786880 (4287062772429 / 50000) (4288694013743 / 50000) := by
  exact
    packedTile16384 85754112 85786880 12 1786 9260 26 _ _ (913349 / 50000) (1826701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85786880 :
    ThetaLowerSegment 85786880 85819648 (4288694013743 / 50000) (4290330769199 / 50000) := by
  exact
    packedTile16384 85786880 85819648 12 1792 9262 26 _ _ (114171 / 6250) (1826739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85819648 :
    ThetaLowerSegment 85819648 85852416 (4290330769199 / 50000) (2145998850237 / 25000) := by
  exact
    packedTile16384 85819648 85852416 12 1825 9263 26 _ _ (913387 / 50000) (1826777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85852416 :
    ThetaLowerSegment 85852416 85885184 (2145998850237 / 25000) (8587252608527 / 100000) := by
  exact
    packedTile16384 85852416 85885184 12 1783 9265 26 _ _ (1826813 / 100000) (57088 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85885184 :
    ThetaLowerSegment 85885184 85917952 (8587252608527 / 100000) (2147642085773 / 25000) := by
  exact
    packedTile16384 85885184 85917952 12 1815 9267 26 _ _ (1826851 / 100000) (913427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85917952 :
    ThetaLowerSegment 85917952 85950720 (2147642085773 / 25000) (4296886353199 / 50000) := by
  exact
    packedTile16384 85917952 85950720 12 1754 9269 26 _ _ (1826889 / 100000) (456723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85950720 :
    ThetaLowerSegment 85950720 85983488 (4296886353199 / 50000) (8597092232757 / 100000) := by
  exact
    packedTile16384 85950720 85983488 12 1817 9270 26 _ _ (1826927 / 100000) (182693 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell85983488 :
    ThetaLowerSegment 85983488 86016256 (8597092232757 / 100000) (4300169374781 / 50000) := by
  exact
    packedTile16384 85983488 86016256 12 1777 9272 26 _ _ (365393 / 20000) (228371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86016256 :
    ThetaLowerSegment 86016256 86049024 (4300169374781 / 50000) (2150913233251 / 25000) := by
  exact
    packedTile16384 86016256 86049024 12 1814 9274 26 _ _ (1827003 / 100000) (913503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86049024 :
    ThetaLowerSegment 86049024 86081792 (2150913233251 / 25000) (4303490900853 / 50000) := by
  exact
    packedTile16384 86049024 86081792 12 1822 9276 26 _ _ (1827041 / 100000) (456761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86081792 :
    ThetaLowerSegment 86081792 86114560 (4303490900853 / 50000) (10762806206 / 125) := by
  exact
    packedTile16384 86081792 86114560 12 1786 9278 26 _ _ (1827079 / 100000) (913541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86114560 :
    ThetaLowerSegment 86114560 86147328 (10762806206 / 125) (8613462517837 / 100000) := by
  exact
    packedTile16384 86114560 86147328 12 1761 9279 26 _ _ (1827117 / 100000) (22839 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86147328 :
    ThetaLowerSegment 86147328 86180096 (8613462517837 / 100000) (8616707545117 / 100000) := by
  exact
    packedTile16384 86147328 86180096 12 1776 9281 26 _ _ (365431 / 20000) (913579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86180096 :
    ThetaLowerSegment 86180096 86212864 (8616707545117 / 100000) (8620022073219 / 100000) := by
  exact
    packedTile16384 86180096 86212864 12 1814 9283 26 _ _ (1827193 / 100000) (456799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86212864 :
    ThetaLowerSegment 86212864 86245632 (8620022073219 / 100000) (2155809043137 / 25000) := by
  exact
    packedTile16384 86212864 86245632 12 1759 9285 26 _ _ (1827231 / 100000) (913617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86245632 :
    ThetaLowerSegment 86245632 86278400 (2155809043137 / 25000) (1725302493173 / 20000) := by
  exact
    packedTile16384 86245632 86278400 12 1793 9286 26 _ _ (1827269 / 100000) (228409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86278400 :
    ThetaLowerSegment 86278400 86311168 (1725302493173 / 20000) (8629827200763 / 100000) := by
  exact
    packedTile16384 86278400 86311168 12 1814 9288 26 _ _ (1827307 / 100000) (182731 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86311168 :
    ThetaLowerSegment 86311168 86343936 (8629827200763 / 100000) (4316531714379 / 50000) := by
  exact
    packedTile16384 86311168 86343936 12 1771 9290 26 _ _ (365469 / 20000) (456837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86343936 :
    ThetaLowerSegment 86343936 86376704 (4316531714379 / 50000) (539769989079 / 6250) := by
  exact
    packedTile16384 86343936 86376704 12 1782 9292 26 _ _ (1827383 / 100000) (913693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86376704 :
    ThetaLowerSegment 86376704 86409472 (539769989079 / 6250) (863962014759 / 10000) := by
  exact
    packedTile16384 86376704 86409472 12 1806 9293 26 _ _ (1827421 / 100000) (57107 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86409472 :
    ThetaLowerSegment 86409472 86442240 (863962014759 / 10000) (8642958915183 / 100000) := by
  exact
    packedTile16384 86409472 86442240 12 1827 9295 26 _ _ (1827459 / 100000) (913731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86442240 :
    ThetaLowerSegment 86442240 86475008 (8642958915183 / 100000) (4323112326161 / 50000) := by
  exact
    packedTile16384 86442240 86475008 12 1787 9297 26 _ _ (1827497 / 100000) (731 / 40) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86475008 :
    ThetaLowerSegment 86475008 86507776 (4323112326161 / 50000) (8649497767507 / 100000) := by
  exact
    packedTile16384 86475008 86507776 12 1791 9299 26 _ _ (365507 / 20000) (913769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86507776 :
    ThetaLowerSegment 86507776 86540544 (8649497767507 / 100000) (540802981801 / 6250) := by
  exact
    packedTile16384 86507776 86540544 12 1833 9300 26 _ _ (1827573 / 100000) (228447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86540544 :
    ThetaLowerSegment 86540544 86573312 (540802981801 / 6250) (8656113649673 / 100000) := by
  exact
    packedTile16384 86540544 86573312 12 1787 9302 26 _ _ (1827611 / 100000) (913807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86573312 :
    ThetaLowerSegment 86573312 86606080 (8656113649673 / 100000) (8659333967211 / 100000) := by
  exact
    packedTile16384 86573312 86606080 12 1762 9304 26 _ _ (1827649 / 100000) (456913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86606080 :
    ThetaLowerSegment 86606080 86638848 (8659333967211 / 100000) (8662711532787 / 100000) := by
  exact
    packedTile16384 86606080 86638848 12 1848 9306 26 _ _ (1827687 / 100000) (182769 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86638848 :
    ThetaLowerSegment 86638848 86671616 (8662711532787 / 100000) (8665891772547 / 100000) := by
  exact
    packedTile16384 86638848 86671616 12 1740 9307 26 _ _ (456931 / 25000) (1827727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86671616 :
    ThetaLowerSegment 86671616 86704384 (8665891772547 / 100000) (8669163466527 / 100000) := by
  exact
    packedTile16384 86671616 86704384 12 1790 9309 26 _ _ (913881 / 50000) (365553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86704384 :
    ThetaLowerSegment 86704384 86737152 (8669163466527 / 100000) (8672458989927 / 100000) := by
  exact
    packedTile16384 86704384 86737152 12 1803 9311 26 _ _ (9139 / 500) (1827803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86737152 :
    ThetaLowerSegment 86737152 86769920 (8672458989927 / 100000) (8675734475623 / 100000) := by
  exact
    packedTile16384 86737152 86769920 12 1792 9313 26 _ _ (913919 / 50000) (1827841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86769920 :
    ThetaLowerSegment 86769920 86802688 (8675734475623 / 100000) (8679041103307 / 100000) := by
  exact
    packedTile16384 86769920 86802688 12 1809 9315 26 _ _ (456969 / 25000) (1827879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86802688 :
    ThetaLowerSegment 86802688 86835456 (8679041103307 / 100000) (4341135512789 / 50000) := by
  exact
    packedTile16384 86802688 86835456 12 1767 9316 26 _ _ (1827913 / 100000) (456979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86835456 :
    ThetaLowerSegment 86835456 86868224 (4341135512789 / 50000) (347422234141 / 4000) := by
  exact
    packedTile16384 86835456 86868224 12 1797 9318 26 _ _ (1827951 / 100000) (913977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86868224 :
    ThetaLowerSegment 86868224 86900992 (347422234141 / 4000) (8688904729373 / 100000) := by
  exact
    packedTile16384 86868224 86900992 12 1832 9320 26 _ _ (1827989 / 100000) (228499 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86900992 :
    ThetaLowerSegment 86900992 86933760 (8688904729373 / 100000) (1738426605011 / 20000) := by
  exact
    packedTile16384 86900992 86933760 12 1766 9322 26 _ _ (1828027 / 100000) (182803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86933760 :
    ThetaLowerSegment 86933760 86966528 (1738426605011 / 20000) (8695348589631 / 100000) := by
  exact
    packedTile16384 86933760 86966528 12 1759 9323 26 _ _ (57127 / 3125) (1828067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86966528 :
    ThetaLowerSegment 86966528 86999296 (8695348589631 / 100000) (1739728565887 / 20000) := by
  exact
    packedTile16384 86966528 86999296 12 1802 9325 26 _ _ (914051 / 50000) (365621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell86999296 :
    ThetaLowerSegment 86999296 87032064 (1739728565887 / 20000) (1740395836987 / 20000) := by
  exact
    packedTile16384 86999296 87032064 12 1825 9327 26 _ _ (91407 / 5000) (1828143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87032064 :
    ThetaLowerSegment 87032064 87064832 (1740395836987 / 20000) (4352615755909 / 50000) := by
  exact
    packedTile16384 87032064 87064832 12 1779 9329 26 _ _ (1828177 / 100000) (91409 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87064832 :
    ThetaLowerSegment 87064832 87097600 (4352615755909 / 50000) (8708546065613 / 100000) := by
  exact
    packedTile16384 87064832 87097600 12 1813 9330 26 _ _ (365643 / 20000) (914109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87097600 :
    ThetaLowerSegment 87097600 87130368 (8708546065613 / 100000) (8711721739337 / 100000) := by
  exact
    packedTile16384 87097600 87130368 12 1737 9332 26 _ _ (457063 / 25000) (365651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87130368 :
    ThetaLowerSegment 87130368 87163136 (8711721739337 / 100000) (8715014489627 / 100000) := by
  exact
    packedTile16384 87130368 87163136 12 1801 9334 26 _ _ (182829 / 10000) (1828293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87163136 :
    ThetaLowerSegment 87163136 87195904 (8715014489627 / 100000) (8718294510059 / 100000) := by
  exact
    packedTile16384 87163136 87195904 12 1794 9336 26 _ _ (228541 / 12500) (1828331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87195904 :
    ThetaLowerSegment 87195904 87228672 (8718294510059 / 100000) (8721640418009 / 100000) := by
  exact
    packedTile16384 87195904 87228672 12 1830 9337 26 _ _ (365673 / 20000) (114273 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87228672 :
    ThetaLowerSegment 87228672 87261440 (8721640418009 / 100000) (8724905945767 / 100000) := by
  exact
    packedTile16384 87228672 87261440 12 1786 9339 26 _ _ (1828403 / 100000) (914203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87261440 :
    ThetaLowerSegment 87261440 87294208 (8724905945767 / 100000) (8728200794647 / 100000) := by
  exact
    packedTile16384 87261440 87294208 12 1802 9341 26 _ _ (45711 / 2500) (1828443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87294208 :
    ThetaLowerSegment 87294208 87326976 (8728200794647 / 100000) (1746293291271 / 20000) := by
  exact
    packedTile16384 87294208 87326976 12 1786 9343 26 _ _ (914239 / 50000) (1828481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87326976 :
    ThetaLowerSegment 87326976 87359744 (1746293291271 / 20000) (43673633493 / 500) := by
  exact
    packedTile16384 87326976 87359744 12 1783 9344 26 _ _ (365703 / 20000) (914259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87359744 :
    ThetaLowerSegment 87359744 87392512 (43673633493 / 500) (8737943123327 / 100000) := by
  exact
    packedTile16384 87359744 87392512 12 1759 9346 26 _ _ (1828553 / 100000) (457139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87392512 :
    ThetaLowerSegment 87392512 87425280 (8737943123327 / 100000) (1092639466089 / 12500) := by
  exact
    packedTile16384 87392512 87425280 12 1735 9348 26 _ _ (1828591 / 100000) (914297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87425280 :
    ThetaLowerSegment 87425280 87441664 (1092639466089 / 12500) (2185692659263 / 25000) := by
  exact
    packedTile16384 87425280 87441664 11 905 9350 26 _ _ (457157 / 25000) (1828631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87441664 :
    ThetaLowerSegment 87441664 87474432 (2185692659263 / 25000) (8746056715711 / 100000) := by
  exact
    packedTile16384 87441664 87474432 12 1797 9351 26 _ _ (1828647 / 100000) (36573 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87474432 :
    ThetaLowerSegment 87474432 87507200 (8746056715711 / 100000) (8749311773231 / 100000) := by
  exact
    packedTile16384 87474432 87507200 12 1780 9352 26 _ _ (457171 / 25000) (1828687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87507200 :
    ThetaLowerSegment 87507200 87523584 (8749311773231 / 100000) (8751001512359 / 100000) := by
  exact
    packedTile16384 87507200 87523584 11 924 9354 26 _ _ (914361 / 50000) (73149 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87523584 :
    ThetaLowerSegment 87523584 87556352 (8751001512359 / 100000) (8754287758139 / 100000) := by
  exact
    packedTile16384 87523584 87556352 12 1797 9355 26 _ _ (91437 / 5000) (1828743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87556352 :
    ThetaLowerSegment 87556352 87589120 (8754287758139 / 100000) (8757550298091 / 100000) := by
  exact
    packedTile16384 87556352 87589120 12 1784 9357 26 _ _ (914389 / 50000) (1828781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87589120 :
    ThetaLowerSegment 87589120 87621888 (8757550298091 / 100000) (4380436627473 / 50000) := by
  exact
    packedTile16384 87589120 87621888 12 1817 9358 26 _ _ (365763 / 20000) (914409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87621888 :
    ThetaLowerSegment 87621888 87654656 (4380436627473 / 50000) (4382067964349 / 50000) := by
  exact
    packedTile16384 87621888 87654656 12 1784 9360 26 _ _ (1828853 / 100000) (228607 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87654656 :
    ThetaLowerSegment 87654656 87687424 (4382067964349 / 50000) (4383688360889 / 50000) := by
  exact
    packedTile16384 87654656 87687424 12 1772 9362 26 _ _ (182889 / 10000) (1828893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87687424 :
    ThetaLowerSegment 87687424 87720192 (4383688360889 / 50000) (4385297816649 / 50000) := by
  exact
    packedTile16384 87687424 87720192 12 1760 9364 26 _ _ (1828927 / 100000) (182893 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87720192 :
    ThetaLowerSegment 87720192 87736576 (4385297816649 / 50000) (4386117192969 / 50000) := by
  exact
    packedTile16384 87720192 87736576 11 896 9365 26 _ _ (365793 / 20000) (228621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87736576 :
    ThetaLowerSegment 87736576 87752960 (4386117192969 / 50000) (8773871325723 / 100000) := by
  exact
    packedTile16384 87736576 87752960 11 895 9366 26 _ _ (1828983 / 100000) (914493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87752960 :
    ThetaLowerSegment 87752960 87769344 (8773871325723 / 100000) (8775479018481 / 100000) := by
  exact
    packedTile16384 87752960 87769344 11 879 9367 26 _ _ (914501 / 50000) (365801 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87769344 :
    ThetaLowerSegment 87769344 87785728 (8775479018481 / 100000) (8777121479339 / 100000) := by
  exact
    packedTile16384 87769344 87785728 11 898 9368 26 _ _ (1829021 / 100000) (57157 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87785728 :
    ThetaLowerSegment 87785728 87802112 (8777121479339 / 100000) (43893828927 / 500) := by
  exact
    packedTile16384 87785728 87802112 11 899 9369 26 _ _ (1829039 / 100000) (914521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87802112 :
    ThetaLowerSegment 87802112 87818496 (43893828927 / 500) (1097552406729 / 12500) := by
  exact
    packedTile16384 87802112 87818496 11 904 9370 26 _ _ (914529 / 50000) (1829061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87818496 :
    ThetaLowerSegment 87818496 87834880 (1097552406729 / 12500) (2195512697629 / 25000) := by
  exact
    packedTile16384 87818496 87834880 11 892 9371 26 _ _ (1829077 / 100000) (45727 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87834880 :
    ThetaLowerSegment 87834880 87851264 (2195512697629 / 25000) (8783698805111 / 100000) := by
  exact
    packedTile16384 87834880 87851264 11 901 9372 26 _ _ (365819 / 20000) (914549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87851264 :
    ThetaLowerSegment 87851264 87867648 (8783698805111 / 100000) (1757062050909 / 20000) := by
  exact
    packedTile16384 87851264 87867648 11 881 9372 26 _ _ (914557 / 50000) (1829117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87867648 :
    ThetaLowerSegment 87867648 87884032 (1757062050909 / 20000) (8786989398639 / 100000) := by
  exact
    packedTile16384 87867648 87884032 11 918 9373 26 _ _ (1829133 / 100000) (114321 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87884032 :
    ThetaLowerSegment 87884032 87900416 (8786989398639 / 100000) (8788661242653 / 100000) := by
  exact
    packedTile16384 87884032 87900416 11 914 9374 26 _ _ (1829151 / 100000) (914577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87900416 :
    ThetaLowerSegment 87900416 87933184 (8788661242653 / 100000) (8791931798613 / 100000) := by
  exact
    packedTile16384 87900416 87933184 12 1788 9375 26 _ _ (182917 / 10000) (1829173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87933184 :
    ThetaLowerSegment 87933184 87965952 (8791931798613 / 100000) (8795191445487 / 100000) := by
  exact
    packedTile16384 87933184 87965952 12 1782 9377 26 _ _ (1829207 / 100000) (182921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87965952 :
    ThetaLowerSegment 87965952 87998720 (8795191445487 / 100000) (2199628795913 / 25000) := by
  exact
    packedTile16384 87965952 87998720 12 1817 9379 26 _ _ (365849 / 20000) (57164 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell87998720 :
    ThetaLowerSegment 87998720 88031488 (2199628795913 / 25000) (4400914006677 / 50000) := by
  exact
    packedTile16384 87998720 88031488 12 1811 9380 26 _ _ (914641 / 50000) (365857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88031488 :
    ThetaLowerSegment 88031488 88064256 (4400914006677 / 50000) (8805162861891 / 100000) := by
  exact
    packedTile16384 88031488 88064256 12 1823 9382 26 _ _ (1829319 / 100000) (914661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88064256 :
    ThetaLowerSegment 88064256 88097024 (8805162861891 / 100000) (8808459361403 / 100000) := by
  exact
    packedTile16384 88064256 88097024 12 1802 9384 26 _ _ (457339 / 25000) (1829359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88097024 :
    ThetaLowerSegment 88097024 88129792 (8808459361403 / 100000) (440584777881 / 5000) := by
  exact
    packedTile16384 88097024 88129792 12 1769 9386 26 _ _ (1829393 / 100000) (457349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88129792 :
    ThetaLowerSegment 88129792 88162560 (440584777881 / 5000) (8814975727403 / 100000) := by
  exact
    packedTile16384 88129792 88162560 12 1793 9387 26 _ _ (1829431 / 100000) (914717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88162560 :
    ThetaLowerSegment 88162560 88195328 (8814975727403 / 100000) (1763644240727 / 20000) := by
  exact
    packedTile16384 88162560 88195328 12 1774 9389 26 _ _ (457367 / 25000) (1829471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88195328 :
    ThetaLowerSegment 88195328 88228096 (1763644240727 / 20000) (352862621551 / 4000) := by
  exact
    packedTile16384 88195328 88228096 12 1828 9391 26 _ _ (365901 / 20000) (457377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88228096 :
    ThetaLowerSegment 88228096 88260864 (352862621551 / 4000) (8824983123231 / 100000) := by
  exact
    packedTile16384 88228096 88260864 12 1868 9392 26 _ _ (914771 / 50000) (365909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88260864 :
    ThetaLowerSegment 88260864 88293632 (8824983123231 / 100000) (1103531572613 / 12500) := by
  exact
    packedTile16384 88260864 88293632 12 1787 9394 26 _ _ (1829579 / 100000) (914791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88293632 :
    ThetaLowerSegment 88293632 88326400 (1103531572613 / 12500) (8831511127 / 100) := by
  exact
    packedTile16384 88293632 88326400 12 1781 9396 26 _ _ (114351 / 6250) (1829619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88326400 :
    ThetaLowerSegment 88326400 88359168 (8831511127 / 100) (4417378465711 / 50000) := by
  exact
    packedTile16384 88326400 88359168 12 1774 9398 26 _ _ (1829653 / 100000) (228707 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88359168 :
    ThetaLowerSegment 88359168 88391936 (4417378465711 / 50000) (1767600194713 / 20000) := by
  exact
    packedTile16384 88359168 88391936 12 1773 9399 26 _ _ (1829691 / 100000) (914847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88391936 :
    ThetaLowerSegment 88391936 88408320 (1767600194713 / 20000) (8839651388221 / 100000) := by
  exact
    packedTile16384 88391936 88408320 11 902 9401 26 _ _ (57179 / 3125) (1829731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell88408320 :
    ThetaLowerSegment 88408320 88412416 (8839651388221 / 100000) (1768014080011 / 20000) := by
  exact
    packedTile16384 88408320 88412416 9 229 9402 26 _ _ (914873 / 50000) (1829749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_71139584_88412416 :
    ThetaLowerSegment 71139584 88412416 (7112973541849 / 100000) (1768014080011 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71139584 cell71155968)
                      (ThetaLowerSegment.join cell71172352 cell71188736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71205120 cell71221504)
                      (ThetaLowerSegment.join cell71237888 cell71254272)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71270656 cell71287040)
                      (ThetaLowerSegment.join cell71303424 cell71319808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71336192 cell71352576)
                      (ThetaLowerSegment.join cell71368960 cell71385344))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71401728 cell71418112)
                      (ThetaLowerSegment.join cell71434496 cell71467264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71500032 cell71532800)
                      (ThetaLowerSegment.join cell71565568 cell71598336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71631104 cell71663872)
                      (ThetaLowerSegment.join cell71696640 cell71729408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71762176 cell71794944)
                      (ThetaLowerSegment.join cell71811328 cell71827712)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71844096 cell71860480)
                      (ThetaLowerSegment.join cell71876864 cell71893248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71909632 cell71926016)
                      (ThetaLowerSegment.join cell71942400 cell71958784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell71975168 cell71991552)
                      (ThetaLowerSegment.join cell72007936 cell72024320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72040704 cell72057088)
                      (ThetaLowerSegment.join cell72073472 cell72089856))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72106240 cell72139008)
                      (ThetaLowerSegment.join cell72171776 cell72204544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72237312 cell72270080)
                      (ThetaLowerSegment.join cell72302848 cell72335616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72368384 cell72401152)
                      (ThetaLowerSegment.join cell72433920 cell72466688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72499456 cell72532224)
                      (ThetaLowerSegment.join cell72564992 cell72597760))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72630528 cell72663296)
                      (ThetaLowerSegment.join cell72696064 cell72728832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72761600 cell72794368)
                      (ThetaLowerSegment.join cell72827136 cell72859904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell72892672 cell72925440)
                      (ThetaLowerSegment.join cell72958208 cell72990976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73023744 cell73056512)
                      (ThetaLowerSegment.join cell73089280 cell73122048))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73154816 cell73187584)
                      (ThetaLowerSegment.join cell73220352 cell73253120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73285888 cell73318656)
                      (ThetaLowerSegment.join cell73351424 cell73384192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73416960 cell73449728)
                      (ThetaLowerSegment.join cell73482496 cell73515264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73548032 cell73580800)
                      (ThetaLowerSegment.join cell73613568 cell73646336)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73679104 cell73711872)
                      (ThetaLowerSegment.join cell73744640 cell73777408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73810176 cell73842944)
                      (ThetaLowerSegment.join cell73875712 cell73908480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell73941248 cell73974016)
                      (ThetaLowerSegment.join cell74006784 cell74039552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74072320 cell74105088)
                      (ThetaLowerSegment.join cell74137856 cell74170624))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74203392 cell74236160)
                      (ThetaLowerSegment.join cell74268928 cell74301696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74334464 cell74367232)
                      (ThetaLowerSegment.join cell74400000 cell74432768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74465536 cell74498304)
                      (ThetaLowerSegment.join cell74514688 cell74547456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74563840 cell74580224)
                      (ThetaLowerSegment.join cell74596608 cell74629376)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74662144 cell74694912)
                      (ThetaLowerSegment.join cell74711296 cell74727680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74760448 cell74793216)
                      (ThetaLowerSegment.join cell74825984 cell74858752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell74891520 cell74924288)
                      (ThetaLowerSegment.join cell74957056 cell74989824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75022592 cell75038976)
                      (ThetaLowerSegment.join cell75055360 cell75071744))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75088128 cell75120896)
                      (ThetaLowerSegment.join cell75153664 cell75170048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75202816 cell75235584)
                      (ThetaLowerSegment.join cell75268352 cell75301120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75333888 cell75366656)
                      (ThetaLowerSegment.join cell75399424 cell75432192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75464960 cell75497728)
                      (ThetaLowerSegment.join cell75530496 cell75563264)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75596032 cell75628800)
                      (ThetaLowerSegment.join cell75661568 cell75694336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75727104 cell75759872)
                      (ThetaLowerSegment.join cell75792640 cell75825408)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75858176 cell75890944)
                      (ThetaLowerSegment.join cell75923712 cell75956480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell75989248 cell76022016)
                      (ThetaLowerSegment.join cell76054784 cell76087552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76120320 cell76153088)
                      (ThetaLowerSegment.join cell76185856 cell76218624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76251392 cell76284160)
                      (ThetaLowerSegment.join cell76316928 cell76349696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76382464 cell76415232)
                      (ThetaLowerSegment.join cell76448000 cell76480768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76513536 cell76546304)
                      (ThetaLowerSegment.join cell76579072 cell76611840))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76644608 cell76677376)
                      (ThetaLowerSegment.join cell76710144 cell76742912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76775680 cell76792064)
                      (ThetaLowerSegment.join cell76824832 cell76857600)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell76890368 cell76923136)
                      (ThetaLowerSegment.join cell76955904 cell76988672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77021440 cell77054208)
                      (ThetaLowerSegment.join cell77086976 cell77119744))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77152512 cell77185280)
                      (ThetaLowerSegment.join cell77218048 cell77250816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77283584 cell77316352)
                      (ThetaLowerSegment.join cell77349120 cell77381888)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77414656 cell77447424)
                      (ThetaLowerSegment.join cell77480192 cell77512960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77545728 cell77578496)
                      (ThetaLowerSegment.join cell77611264 cell77644032)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77676800 cell77709568)
                      (ThetaLowerSegment.join cell77725952 cell77758720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77791488 cell77824256)
                      (ThetaLowerSegment.join cell77857024 cell77889792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell77922560 cell77955328)
                      (ThetaLowerSegment.join cell77988096 cell78020864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78053632 cell78086400)
                      (ThetaLowerSegment.join cell78119168 cell78151936))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78184704 cell78217472)
                      (ThetaLowerSegment.join cell78250240 cell78283008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78315776 cell78348544)
                      (ThetaLowerSegment.join cell78364928 cell78381312)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78397696 cell78430464)
                      (ThetaLowerSegment.join cell78446848 cell78463232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78479616 cell78496000)
                      (ThetaLowerSegment.join cell78512384 cell78528768))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78545152 cell78561536)
                      (ThetaLowerSegment.join cell78577920 cell78594304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78610688 cell78627072)
                      (ThetaLowerSegment.join cell78643456 cell78659840)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78676224 cell78692608)
                      (ThetaLowerSegment.join cell78708992 cell78725376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78741760 cell78758144)
                      (ThetaLowerSegment.join cell78774528 cell78790912))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78823680 cell78856448)
                      (ThetaLowerSegment.join cell78872832 cell78889216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78905600 cell78921984)
                      (ThetaLowerSegment.join cell78938368 cell78954752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell78971136 cell78987520)
                      (ThetaLowerSegment.join cell79003904 cell79020288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79036672 cell79053056)
                      (ThetaLowerSegment.join cell79069440 cell79085824)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79102208 cell79134976)
                      (ThetaLowerSegment.join cell79151360 cell79167744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79184128 cell79200512)
                      (ThetaLowerSegment.join cell79216896 cell79233280)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79249664 cell79266048)
                      (ThetaLowerSegment.join cell79282432 cell79298816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79315200 cell79331584)
                      (ThetaLowerSegment.join cell79347968 cell79364352))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79380736 cell79397120)
                      (ThetaLowerSegment.join cell79413504 cell79429888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79446272 cell79462656)
                      (ThetaLowerSegment.join cell79479040 cell79495424)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79511808 cell79528192)
                      (ThetaLowerSegment.join cell79544576 cell79560960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79577344 cell79593728)
                      (ThetaLowerSegment.join cell79610112 cell79626496))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79642880 cell79659264)
                      (ThetaLowerSegment.join cell79692032 cell79708416))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79724800 cell79741184)
                      (ThetaLowerSegment.join cell79757568 cell79773952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79790336 cell79806720)
                      (ThetaLowerSegment.join cell79823104 cell79839488))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79855872 cell79872256)
                      (ThetaLowerSegment.join cell79888640 cell79905024))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79921408 cell79937792)
                      (ThetaLowerSegment.join cell79954176 cell79970560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell79986944 cell80003328)
                      (ThetaLowerSegment.join cell80019712 cell80036096)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80052480 cell80068864)
                      (ThetaLowerSegment.join cell80085248 cell80101632))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80118016 cell80134400)
                      (ThetaLowerSegment.join cell80150784 cell80167168)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80183552 cell80199936)
                      (ThetaLowerSegment.join cell80216320 cell80232704))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80249088 cell80265472)
                      (ThetaLowerSegment.join cell80281856 cell80298240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80314624 cell80331008)
                      (ThetaLowerSegment.join cell80347392 cell80363776))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80380160 cell80396544)
                      (ThetaLowerSegment.join cell80412928 cell80429312))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80445696 cell80462080)
                      (ThetaLowerSegment.join cell80478464 cell80494848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80511232 cell80527616)
                      (ThetaLowerSegment.join cell80544000 cell80560384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80576768 cell80593152)
                      (ThetaLowerSegment.join cell80609536 cell80625920))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80642304 cell80658688)
                      (ThetaLowerSegment.join cell80675072 cell80691456)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80707840 cell80724224)
                      (ThetaLowerSegment.join cell80740608 cell80756992))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80773376 cell80789760)
                      (ThetaLowerSegment.join cell80806144 cell80822528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80838912 cell80855296)
                      (ThetaLowerSegment.join cell80871680 cell80904448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell80937216 cell80969984)
                      (ThetaLowerSegment.join cell81002752 cell81035520))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81068288 cell81101056)
                      (ThetaLowerSegment.join cell81133824 cell81166592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81199360 cell81232128)
                      (ThetaLowerSegment.join cell81264896 cell81297664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81330432 cell81363200)
                      (ThetaLowerSegment.join cell81395968 cell81428736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81461504 cell81494272)
                      (ThetaLowerSegment.join cell81527040 cell81559808)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81592576 cell81625344)
                      (ThetaLowerSegment.join cell81658112 cell81690880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81723648 cell81756416)
                      (ThetaLowerSegment.join cell81789184 cell81821952)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81854720 cell81887488)
                      (ThetaLowerSegment.join cell81920256 cell81953024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell81985792 cell82018560)
                      (ThetaLowerSegment.join cell82051328 cell82084096))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82116864 cell82149632)
                      (ThetaLowerSegment.join cell82182400 cell82215168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82247936 cell82280704)
                      (ThetaLowerSegment.join cell82313472 cell82346240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82379008 cell82411776)
                      (ThetaLowerSegment.join cell82444544 cell82477312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82510080 cell82542848)
                      (ThetaLowerSegment.join cell82575616 cell82608384))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82641152 cell82673920)
                      (ThetaLowerSegment.join cell82706688 cell82739456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82772224 cell82804992)
                      (ThetaLowerSegment.join cell82837760 cell82870528)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell82903296 cell82936064)
                      (ThetaLowerSegment.join cell82968832 cell83001600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83034368 cell83067136)
                      (ThetaLowerSegment.join cell83099904 cell83132672))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83165440 cell83198208)
                      (ThetaLowerSegment.join cell83230976 cell83263744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83296512 cell83329280)
                      (ThetaLowerSegment.join cell83362048 cell83394816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83427584 cell83460352)
                      (ThetaLowerSegment.join cell83493120 cell83525888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83558656 cell83591424)
                      (ThetaLowerSegment.join cell83624192 cell83656960)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83689728 cell83722496)
                      (ThetaLowerSegment.join cell83755264 cell83788032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83820800 cell83853568)
                      (ThetaLowerSegment.join cell83886336 cell83919104)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell83951872 cell83984640)
                      (ThetaLowerSegment.join cell84017408 cell84050176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell84082944 cell84115712)
                      (ThetaLowerSegment.join cell84148480 cell84181248))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell84214016 cell84246784)
                      (ThetaLowerSegment.join cell84279552 cell84312320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell84345088 cell84377856)
                      (ThetaLowerSegment.join cell84410624 cell84443392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell84476160 cell84508928)
                      (ThetaLowerSegment.join cell84541696 cell84574464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell84607232 cell84640000)
                      (ThetaLowerSegment.join cell84672768 cell84705536)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell84738304 cell84771072)
                  (ThetaLowerSegment.join cell84803840 cell84836608))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell84869376 cell84902144)
                  (ThetaLowerSegment.join cell84934912 cell84967680)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85000448 cell85033216)
                  (ThetaLowerSegment.join cell85049600 cell85065984))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85082368 cell85098752)
                  (ThetaLowerSegment.join cell85131520 cell85147904))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85180672 cell85197056)
                  (ThetaLowerSegment.join cell85213440 cell85229824))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85246208 cell85262592)
                  (ThetaLowerSegment.join cell85295360 cell85311744)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85328128 cell85360896)
                  (ThetaLowerSegment.join cell85377280 cell85393664))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85426432 cell85459200)
                  (ThetaLowerSegment.join cell85491968 cell85524736)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85557504 cell85590272)
                  (ThetaLowerSegment.join cell85623040 cell85655808))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85688576 cell85721344)
                  (ThetaLowerSegment.join cell85754112 cell85786880)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85819648 cell85852416)
                  (ThetaLowerSegment.join cell85885184 cell85917952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell85950720 cell85983488)
                  (ThetaLowerSegment.join cell86016256 cell86049024))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86081792 cell86114560)
                  (ThetaLowerSegment.join cell86147328 cell86180096))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86212864 cell86245632)
                  (ThetaLowerSegment.join cell86278400 cell86311168)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86343936 cell86376704)
                  (ThetaLowerSegment.join cell86409472 cell86442240))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86475008 cell86507776)
                  (ThetaLowerSegment.join cell86540544 cell86573312))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86606080 cell86638848)
                  (ThetaLowerSegment.join cell86671616 cell86704384))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86737152 cell86769920)
                  (ThetaLowerSegment.join cell86802688 cell86835456)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86868224 cell86900992)
                  (ThetaLowerSegment.join cell86933760 cell86966528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell86999296 cell87032064)
                  (ThetaLowerSegment.join cell87064832 cell87097600))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87130368 cell87163136)
                  (ThetaLowerSegment.join cell87195904 cell87228672))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87261440 cell87294208)
                  (ThetaLowerSegment.join cell87326976 cell87359744)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87392512 cell87425280)
                  (ThetaLowerSegment.join cell87441664 cell87474432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87507200 cell87523584)
                  (ThetaLowerSegment.join cell87556352 cell87589120)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87621888 cell87654656)
                  (ThetaLowerSegment.join cell87687424 cell87720192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87736576 cell87752960)
                  (ThetaLowerSegment.join cell87769344 cell87785728)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87802112 cell87818496)
                  (ThetaLowerSegment.join cell87834880 cell87851264))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87867648 cell87884032)
                  (ThetaLowerSegment.join cell87900416 cell87933184))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell87965952 cell87998720)
                  (ThetaLowerSegment.join cell88031488 cell88064256))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell88097024 cell88129792)
                  (ThetaLowerSegment.join cell88162560 cell88195328)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell88228096 cell88260864)
                  (ThetaLowerSegment.join cell88293632 cell88326400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell88359168 cell88391936)
                  cell88408320)))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
