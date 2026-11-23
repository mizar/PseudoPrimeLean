/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2217341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2185341184 :
    ThetaLowerSegment 2185341184 2185472256 (218527790796803 / 100000)
      (43708167148387 / 20000) := by
  exact
    packedTile65536 2185341184 2185472256 14 6066 46747 31 _ _ (1075251 / 50000) (430101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185472256 :
    ThetaLowerSegment 2185472256 2185603328 (43708167148387 / 20000)
      (218553859218383 / 100000) := by
  exact
    packedTile65536 2185472256 2185603328 14 6056 46749 31 _ _ (537627 / 25000) (2150511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185603328 :
    ThetaLowerSegment 2185603328 2185734400 (218553859218383 / 100000)
      (43713405363121 / 20000) := by
  exact
    packedTile65536 2185603328 2185734400 14 6123 46750 31 _ _ (1075257 / 50000) (2150517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185734400 :
    ThetaLowerSegment 2185734400 2185865472 (43713405363121 / 20000) (43716034588873 / 20000) := by
  exact
    packedTile65536 2185734400 2185865472 14 6113 46751 31 _ _ (53763 / 2500) (2150523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185865472 :
    ThetaLowerSegment 2185865472 2185996544 (43716034588873 / 20000)
      (218593278249809 / 100000) := by
  exact
    packedTile65536 2185865472 2185996544 14 6094 46753 31 _ _ (1075263 / 50000) (2150529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2185996544 :
    ThetaLowerSegment 2185996544 2186127616 (218593278249809 / 100000)
      (218606224452449 / 100000) := by
  exact
    packedTile65536 2185996544 2186127616 14 6020 46754 31 _ _ (537633 / 25000) (430107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186127616 :
    ThetaLowerSegment 2186127616 2186258688 (218606224452449 / 100000)
      (218619334132097 / 100000) := by
  exact
    packedTile65536 2186127616 2186258688 14 6096 46756 31 _ _ (1075269 / 50000) (2150541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186258688 :
    ThetaLowerSegment 2186258688 2186389760 (218619334132097 / 100000)
      (218632430945057 / 100000) := by
  exact
    packedTile65536 2186258688 2186389760 14 6090 46757 31 _ _ (134409 / 6250) (2150547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186389760 :
    ThetaLowerSegment 2186389760 2186520832 (218632430945057 / 100000)
      (218645598762707 / 100000) := by
  exact
    packedTile65536 2186389760 2186520832 14 6123 46758 31 _ _ (43011 / 2000) (2150553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186520832 :
    ThetaLowerSegment 2186520832 2186651904 (218645598762707 / 100000)
      (218658921457127 / 100000) := by
  exact
    packedTile65536 2186520832 2186651904 14 6195 46760 31 _ _ (537639 / 25000) (2150559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186651904 :
    ThetaLowerSegment 2186651904 2186782976 (218658921457127 / 100000)
      (218672044186451 / 100000) := by
  exact
    packedTile65536 2186651904 2186782976 14 6102 46761 31 _ _ (1075281 / 50000) (430113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186782976 :
    ThetaLowerSegment 2186782976 2186914048 (218672044186451 / 100000)
      (218685283083059 / 100000) := by
  exact
    packedTile65536 2186782976 2186914048 14 6156 46763 31 _ _ (268821 / 12500) (2150571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2186914048 :
    ThetaLowerSegment 2186914048 2187045120 (218685283083059 / 100000)
      (218698300507481 / 100000) := by
  exact
    packedTile65536 2186914048 2187045120 14 6053 46764 31 _ _ (1075287 / 50000) (2150577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187045120 :
    ThetaLowerSegment 2187045120 2187176192 (218698300507481 / 100000)
      (218711662061021 / 100000) := by
  exact
    packedTile65536 2187045120 2187176192 14 6213 46765 31 _ _ (107529 / 5000) (2150583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187176192 :
    ThetaLowerSegment 2187176192 2187307264 (218711662061021 / 100000)
      (218724651600461 / 100000) := by
  exact
    packedTile65536 2187176192 2187307264 14 6040 46767 31 _ _ (1075293 / 50000) (2150589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187307264 :
    ThetaLowerSegment 2187307264 2187438336 (218724651600461 / 100000)
      (218737937957837 / 100000) := by
  exact
    packedTile65536 2187307264 2187438336 14 6178 46768 31 _ _ (67206 / 3125) (430119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187438336 :
    ThetaLowerSegment 2187438336 2187569408 (218737937957837 / 100000)
      (218750815738661 / 100000) := by
  exact
    packedTile65536 2187438336 2187569408 14 5988 46770 31 _ _ (1075299 / 50000) (2150601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187569408 :
    ThetaLowerSegment 2187569408 2187700480 (218750815738661 / 100000)
      (218764046254469 / 100000) := by
  exact
    packedTile65536 2187569408 2187700480 14 6152 46771 31 _ _ (537651 / 25000) (2150607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187700480 :
    ThetaLowerSegment 2187700480 2187831552 (218764046254469 / 100000)
      (218777111210219 / 100000) := by
  exact
    packedTile65536 2187700480 2187831552 14 6075 46772 31 _ _ (215061 / 10000) (2150613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187831552 :
    ThetaLowerSegment 2187831552 2187962624 (218777111210219 / 100000)
      (218790208461659 / 100000) := by
  exact
    packedTile65536 2187831552 2187962624 14 6090 46774 31 _ _ (268827 / 12500) (2150619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2187962624 :
    ThetaLowerSegment 2187962624 2188093696 (218790208461659 / 100000)
      (218803219724759 / 100000) := by
  exact
    packedTile65536 2187962624 2188093696 14 6050 46775 31 _ _ (1075311 / 50000) (3441 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188093696 :
    ThetaLowerSegment 2188093696 2188224768 (218803219724759 / 100000)
      (218816297693627 / 100000) := by
  exact
    packedTile65536 2188093696 2188224768 14 6081 46777 31 _ _ (537657 / 25000) (2150631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188224768 :
    ThetaLowerSegment 2188224768 2188355840 (218816297693627 / 100000)
      (218829364945811 / 100000) := by
  exact
    packedTile65536 2188224768 2188355840 14 6076 46778 31 _ _ (1075317 / 50000) (2150637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188355840 :
    ThetaLowerSegment 2188355840 2188486912 (218829364945811 / 100000)
      (218842688160611 / 100000) := by
  exact
    packedTile65536 2188355840 2188486912 14 6195 46779 31 _ _ (26883 / 1250) (2150643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188486912 :
    ThetaLowerSegment 2188486912 2188617984 (218842688160611 / 100000)
      (218855908181573 / 100000) := by
  exact
    packedTile65536 2188486912 2188617984 14 6147 46781 31 _ _ (1075323 / 50000) (2150649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188617984 :
    ThetaLowerSegment 2188617984 2188749056 (218855908181573 / 100000)
      (43773801560581 / 20000) := by
  exact
    packedTile65536 2188617984 2188749056 14 6091 46782 31 _ _ (537663 / 25000) (430131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188749056 :
    ThetaLowerSegment 2188749056 2188880128 (43773801560581 / 20000)
      (218882085954203 / 100000) := by
  exact
    packedTile65536 2188749056 2188880128 14 6081 46784 31 _ _ (1075329 / 50000) (2150661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2188880128 :
    ThetaLowerSegment 2188880128 2189011200 (218882085954203 / 100000)
      (218895138334019 / 100000) := by
  exact
    packedTile65536 2188880128 2189011200 14 6069 46785 31 _ _ (268833 / 12500) (2150667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189011200 :
    ThetaLowerSegment 2189011200 2189142272 (218895138334019 / 100000)
      (218908274626379 / 100000) := by
  exact
    packedTile65536 2189011200 2189142272 14 6108 46786 31 _ _ (215067 / 10000) (2150673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189142272 :
    ThetaLowerSegment 2189142272 2189273344 (218908274626379 / 100000)
      (43784229714583 / 20000) := by
  exact
    packedTile65536 2189142272 2189273344 14 5986 46788 31 _ _ (537669 / 25000) (2150679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189273344 :
    ThetaLowerSegment 2189273344 2189404416 (43784229714583 / 20000)
      (218934276335843 / 100000) := by
  exact
    packedTile65536 2189273344 2189404416 14 6104 46789 31 _ _ (1075341 / 50000) (430137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189404416 :
    ThetaLowerSegment 2189404416 2189535488 (218934276335843 / 100000)
      (218947335313379 / 100000) := by
  exact
    packedTile65536 2189404416 2189535488 14 6072 46791 31 _ _ (67209 / 3125) (2150691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189535488 :
    ThetaLowerSegment 2189535488 2189666560 (218947335313379 / 100000)
      (218960437341227 / 100000) := by
  exact
    packedTile65536 2189535488 2189666560 14 6092 46792 31 _ _ (1075347 / 50000) (2150697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189666560 :
    ThetaLowerSegment 2189666560 2189797632 (218960437341227 / 100000)
      (218973573816827 / 100000) := by
  exact
    packedTile65536 2189666560 2189797632 14 6108 46793 31 _ _ (21507 / 1000) (2150703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189797632 :
    ThetaLowerSegment 2189797632 2189928704 (218973573816827 / 100000)
      (218986684520603 / 100000) := by
  exact
    packedTile65536 2189797632 2189928704 14 6096 46795 31 _ _ (1075353 / 50000) (2150709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2189928704 :
    ThetaLowerSegment 2189928704 2190059776 (218986684520603 / 100000)
      (218999786658107 / 100000) := by
  exact
    packedTile65536 2189928704 2190059776 14 6092 46796 31 _ _ (268839 / 12500) (430143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190059776 :
    ThetaLowerSegment 2190059776 2190190848 (218999786658107 / 100000)
      (219012942600113 / 100000) := by
  exact
    packedTile65536 2190059776 2190190848 14 6117 46798 31 _ _ (1075359 / 50000) (2150721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190190848 :
    ThetaLowerSegment 2190190848 2190321920 (219012942600113 / 100000)
      (219025969535381 / 100000) := by
  exact
    packedTile65536 2190190848 2190321920 14 6057 46799 31 _ _ (537681 / 25000) (2150727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190321920 :
    ThetaLowerSegment 2190321920 2190452992 (219025969535381 / 100000)
      (219039020165021 / 100000) := by
  exact
    packedTile65536 2190321920 2190452992 14 6068 46800 31 _ _ (215073 / 10000) (2150733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190452992 :
    ThetaLowerSegment 2190452992 2190584064 (219039020165021 / 100000)
      (219052088036957 / 100000) := by
  exact
    packedTile65536 2190452992 2190584064 14 6076 46802 31 _ _ (134421 / 6250) (2150739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190584064 :
    ThetaLowerSegment 2190584064 2190715136 (219052088036957 / 100000)
      (219065149493123 / 100000) := by
  exact
    packedTile65536 2190584064 2190715136 14 6073 46803 31 _ _ (1075371 / 50000) (430149 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190715136 :
    ThetaLowerSegment 2190715136 2190846208 (219065149493123 / 100000)
      (219078324975371 / 100000) := by
  exact
    packedTile65536 2190715136 2190846208 14 6126 46805 31 _ _ (537687 / 25000) (2150751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190846208 :
    ThetaLowerSegment 2190846208 2190977280 (219078324975371 / 100000)
      (219091395107429 / 100000) := by
  exact
    packedTile65536 2190846208 2190977280 14 6077 46806 31 _ _ (1075377 / 50000) (2150757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2190977280 :
    ThetaLowerSegment 2190977280 2191108352 (219091395107429 / 100000)
      (219104617979909 / 100000) := by
  exact
    packedTile65536 2190977280 2191108352 14 6148 46807 31 _ _ (53769 / 2500) (2150763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191108352 :
    ThetaLowerSegment 2191108352 2191239424 (219104617979909 / 100000)
      (219117800024723 / 100000) := by
  exact
    packedTile65536 2191108352 2191239424 14 6129 46809 31 _ _ (1075383 / 50000) (2150769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191239424 :
    ThetaLowerSegment 2191239424 2191370496 (219117800024723 / 100000)
      (219130898226203 / 100000) := by
  exact
    packedTile65536 2191239424 2191370496 14 6090 46810 31 _ _ (537693 / 25000) (86031 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191370496 :
    ThetaLowerSegment 2191370496 2191501568 (219130898226203 / 100000) (8765762783627 / 4000) := by
  exact
    packedTile65536 2191370496 2191501568 14 6124 46812 31 _ _ (1075389 / 50000) (2150781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191501568 :
    ThetaLowerSegment 2191501568 2191632640 (8765762783627 / 4000) (219157015159571 / 100000) := by
  exact
    packedTile65536 2191501568 2191632640 14 6019 46813 31 _ _ (67212 / 3125) (2150787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191632640 :
    ThetaLowerSegment 2191632640 2191763712 (219157015159571 / 100000)
      (219170020986701 / 100000) := by
  exact
    packedTile65536 2191632640 2191763712 14 6047 46814 31 _ _ (215079 / 10000) (2150793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191763712 :
    ThetaLowerSegment 2191763712 2191894784 (219170020986701 / 100000)
      (43836660000241 / 20000) := by
  exact
    packedTile65536 2191763712 2191894784 14 6174 46816 31 _ _ (537699 / 25000) (2150799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2191894784 :
    ThetaLowerSegment 2191894784 2192025856 (43836660000241 / 20000) (43839279677077 / 20000) := by
  exact
    packedTile65536 2191894784 2192025856 14 6090 46817 31 _ _ (1075401 / 50000) (430161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192025856 :
    ThetaLowerSegment 2192025856 2192156928 (43839279677077 / 20000)
      (219209462393177 / 100000) := by
  exact
    packedTile65536 2192025856 2192156928 14 6074 46819 31 _ _ (268851 / 12500) (2150811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192156928 :
    ThetaLowerSegment 2192156928 2192288000 (219209462393177 / 100000)
      (219222578056949 / 100000) := by
  exact
    packedTile65536 2192156928 2192288000 14 6098 46820 31 _ _ (1075407 / 50000) (2150817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192288000 :
    ThetaLowerSegment 2192288000 2192419072 (219222578056949 / 100000)
      (219235683003209 / 100000) := by
  exact
    packedTile65536 2192288000 2192419072 14 6093 46821 31 _ _ (107541 / 5000) (2150823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192419072 :
    ThetaLowerSegment 2192419072 2192550144 (219235683003209 / 100000)
      (219248710556291 / 100000) := by
  exact
    packedTile65536 2192419072 2192550144 14 6057 46823 31 _ _ (1075413 / 50000) (2150829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192550144 :
    ThetaLowerSegment 2192550144 2192681216 (219248710556291 / 100000)
      (43852420757431 / 20000) := by
  exact
    packedTile65536 2192550144 2192681216 14 6227 46824 31 _ _ (134427 / 6250) (430167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192681216 :
    ThetaLowerSegment 2192681216 2192812288 (43852420757431 / 20000)
      (219275219597279 / 100000) := by
  exact
    packedTile65536 2192681216 2192812288 14 6098 46826 31 _ _ (1075419 / 50000) (2150841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192812288 :
    ThetaLowerSegment 2192812288 2192943360 (219275219597279 / 100000)
      (219288339745679 / 100000) := by
  exact
    packedTile65536 2192812288 2192943360 14 6100 46827 31 _ _ (537711 / 25000) (2150847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2192943360 :
    ThetaLowerSegment 2192943360 2193074432 (219288339745679 / 100000)
      (219301548115529 / 100000) := by
  exact
    packedTile65536 2192943360 2193074432 14 6141 46828 31 _ _ (43017 / 2000) (2150853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193074432 :
    ThetaLowerSegment 2193074432 2193205504 (219301548115529 / 100000)
      (219314414536121 / 100000) := by
  exact
    packedTile65536 2193074432 2193205504 14 5982 46830 31 _ _ (268857 / 12500) (2150859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193205504 :
    ThetaLowerSegment 2193205504 2193336576 (219314414536121 / 100000)
      (219327502531391 / 100000) := by
  exact
    packedTile65536 2193205504 2193336576 14 6085 46831 31 _ _ (1075431 / 50000) (430173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193336576 :
    ThetaLowerSegment 2193336576 2193467648 (219327502531391 / 100000)
      (54835122904301 / 25000) := by
  exact
    packedTile65536 2193336576 2193467648 14 6039 46833 31 _ _ (2150867 / 100000) (215087 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193467648 :
    ThetaLowerSegment 2193467648 2193598720 (54835122904301 / 25000) (109676825329109 / 50000) := by
  exact
    packedTile65536 2193467648 2193598720 14 6118 46834 31 _ _ (2150873 / 100000) (537719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193598720 :
    ThetaLowerSegment 2193598720 2193729792 (109676825329109 / 50000)
      (219366803283303 / 100000) := by
  exact
    packedTile65536 2193598720 2193729792 14 6115 46835 31 _ _ (2150879 / 100000) (1075441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193729792 :
    ThetaLowerSegment 2193729792 2193860864 (219366803283303 / 100000)
      (219379958095963 / 100000) := by
  exact
    packedTile65536 2193729792 2193860864 14 6116 46837 31 _ _ (430177 / 20000) (268861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193860864 :
    ThetaLowerSegment 2193860864 2193991936 (219379958095963 / 100000)
      (219392945175821 / 100000) := by
  exact
    packedTile65536 2193860864 2193991936 14 6038 46838 31 _ _ (2150891 / 100000) (1075447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2193991936 :
    ThetaLowerSegment 2193991936 2194123008 (219392945175821 / 100000) (6856438408821 / 3125) := by
  exact
    packedTile65536 2193991936 2194123008 14 6083 46840 31 _ _ (2150897 / 100000) (21509 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194123008 :
    ThetaLowerSegment 2194123008 2194254080 (6856438408821 / 3125) (54854821812091 / 25000) := by
  exact
    packedTile65536 2194123008 2194254080 14 6164 46841 31 _ _ (2150903 / 100000) (1075453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194254080 :
    ThetaLowerSegment 2194254080 2194385152 (54854821812091 / 25000)
      (219432401340537 / 100000) := by
  exact
    packedTile65536 2194254080 2194385152 14 6097 46842 31 _ _ (2150909 / 100000) (67216 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194385152 :
    ThetaLowerSegment 2194385152 2194516224 (219432401340537 / 100000)
      (219445491809227 / 100000) := by
  exact
    packedTile65536 2194385152 2194516224 14 6086 46844 31 _ _ (430183 / 20000) (1075459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194516224 :
    ThetaLowerSegment 2194516224 2194647296 (219445491809227 / 100000)
      (54864673002851 / 25000) := by
  exact
    packedTile65536 2194516224 2194647296 14 6137 46845 31 _ _ (2150921 / 100000) (537731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194647296 :
    ThetaLowerSegment 2194647296 2194778368 (54864673002851 / 25000)
      (219471930967089 / 100000) := by
  exact
    packedTile65536 2194647296 2194778368 14 6155 46847 31 _ _ (2150927 / 100000) (215093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194778368 :
    ThetaLowerSegment 2194778368 2194909440 (219471930967089 / 100000)
      (219484935508007 / 100000) := by
  exact
    packedTile65536 2194778368 2194909440 14 6046 46848 31 _ _ (2150933 / 100000) (268867 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2194909440 :
    ThetaLowerSegment 2194909440 2195040512 (219484935508007 / 100000) (13718627304841 / 6250) := by
  exact
    packedTile65536 2194909440 2195040512 14 6091 46849 31 _ _ (2150939 / 100000) (1075471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195040512 :
    ThetaLowerSegment 2195040512 2195171584 (13718627304841 / 6250) (219511194208021 / 100000) := by
  exact
    packedTile65536 2195040512 2195171584 14 6117 46851 31 _ _ (430189 / 20000) (537737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195171584 :
    ThetaLowerSegment 2195171584 2195302656 (219511194208021 / 100000)
      (109762169334791 / 50000) := by
  exact
    packedTile65536 2195171584 2195302656 14 6111 46852 31 _ _ (2150951 / 100000) (1075477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195302656 :
    ThetaLowerSegment 2195302656 2195433728 (109762169334791 / 50000) (21953746811111 / 10000) := by
  exact
    packedTile65536 2195302656 2195433728 14 6104 46854 31 _ _ (2150957 / 100000) (26887 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195433728 :
    ThetaLowerSegment 2195433728 2195564800 (21953746811111 / 10000) (54887646170871 / 25000) := by
  exact
    packedTile65536 2195433728 2195564800 14 6098 46855 31 _ _ (2150963 / 100000) (1075483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195564800 :
    ThetaLowerSegment 2195564800 2195695872 (54887646170871 / 25000)
      (219563578687213 / 100000) := by
  exact
    packedTile65536 2195564800 2195695872 14 6041 46856 31 _ _ (2150969 / 100000) (537743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195695872 :
    ThetaLowerSegment 2195695872 2195826944 (219563578687213 / 100000)
      (54894212012997 / 25000) := by
  exact
    packedTile65536 2195695872 2195826944 14 6169 46858 31 _ _ (86039 / 4000) (1075489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195826944 :
    ThetaLowerSegment 2195826944 2195958016 (54894212012997 / 25000) (2744874397853 / 1250) := by
  exact
    packedTile65536 2195826944 2195958016 14 6092 46859 31 _ _ (2150981 / 100000) (268873 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2195958016 :
    ThetaLowerSegment 2195958016 2196089088 (2744874397853 / 1250) (43920603814853 / 20000) := by
  exact
    packedTile65536 2195958016 2196089088 14 6075 46861 31 _ _ (2150987 / 100000) (215099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196089088 :
    ThetaLowerSegment 2196089088 2196220160 (43920603814853 / 20000) (109808066839293 / 50000) := by
  exact
    packedTile65536 2196089088 2196220160 14 6097 46862 31 _ _ (2150993 / 100000) (537749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196220160 :
    ThetaLowerSegment 2196220160 2196351232 (109808066839293 / 50000)
      (109814657500229 / 50000) := by
  exact
    packedTile65536 2196220160 2196351232 14 6128 46863 31 _ _ (2150999 / 100000) (1075501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196351232 :
    ThetaLowerSegment 2196351232 2196482304 (109814657500229 / 50000)
      (219642300617643 / 100000) := by
  exact
    packedTile65536 2196351232 2196482304 14 6037 46865 31 _ _ (430201 / 20000) (67219 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196482304 :
    ThetaLowerSegment 2196482304 2196613376 (219642300617643 / 100000) (70289743231 / 32) := by
  exact
    packedTile65536 2196482304 2196613376 14 6112 46866 31 _ _ (2151011 / 100000) (1075507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196613376 :
    ThetaLowerSegment 2196613376 2196744448 (70289743231 / 32) (109834266116643 / 50000) := by
  exact
    packedTile65536 2196613376 2196744448 14 6083 46868 31 _ _ (2151017 / 100000) (107551 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196744448 :
    ThetaLowerSegment 2196744448 2196875520 (109834266116643 / 50000)
      (219681565281643 / 100000) := by
  exact
    packedTile65536 2196744448 2196875520 14 6059 46869 31 _ _ (2151023 / 100000) (1075513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2196875520 :
    ThetaLowerSegment 2196875520 2197006592 (219681565281643 / 100000)
      (219694905963501 / 100000) := by
  exact
    packedTile65536 2196875520 2197006592 14 6202 46870 31 _ _ (2151029 / 100000) (268879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197006592 :
    ThetaLowerSegment 2197006592 2197137664 (219694905963501 / 100000)
      (219708001464581 / 100000) := by
  exact
    packedTile65536 2197006592 2197137664 14 6088 46872 31 _ _ (430207 / 20000) (1075519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197137664 :
    ThetaLowerSegment 2197137664 2197268736 (219708001464581 / 100000) (6866279105376 / 3125) := by
  exact
    packedTile65536 2197137664 2197268736 14 6011 46873 31 _ _ (2151041 / 100000) (537761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197268736 :
    ThetaLowerSegment 2197268736 2197399808 (6866279105376 / 3125) (109867032832507 / 50000) := by
  exact
    packedTile65536 2197268736 2197399808 14 6106 46875 31 _ _ (2151047 / 100000) (43021 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197399808 :
    ThetaLowerSegment 2197399808 2197530880 (109867032832507 / 50000) (10987359569521 / 5000) := by
  exact
    packedTile65536 2197399808 2197530880 14 6102 46876 31 _ _ (2151053 / 100000) (134441 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197530880 :
    ThetaLowerSegment 2197530880 2197661952 (10987359569521 / 5000) (219760392439503 / 100000) := by
  exact
    packedTile65536 2197530880 2197661952 14 6137 46877 31 _ _ (2151059 / 100000) (1075531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197661952 :
    ThetaLowerSegment 2197661952 2197793024 (219760392439503 / 100000)
      (219773419283087 / 100000) := by
  exact
    packedTile65536 2197661952 2197793024 14 6056 46879 31 _ _ (268883 / 12500) (2151067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197793024 :
    ThetaLowerSegment 2197793024 2197924096 (219773419283087 / 100000)
      (219786598888977 / 100000) := by
  exact
    packedTile65536 2197793024 2197924096 14 6127 46880 31 _ _ (215107 / 10000) (2151073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2197924096 :
    ThetaLowerSegment 2197924096 2198055168 (219786598888977 / 100000)
      (219799741963337 / 100000) := by
  exact
    packedTile65536 2197924096 2198055168 14 6110 46882 31 _ _ (537769 / 25000) (2151079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198055168 :
    ThetaLowerSegment 2198055168 2198186240 (219799741963337 / 100000)
      (219812820541897 / 100000) := by
  exact
    packedTile65536 2198055168 2198186240 14 6080 46883 31 _ _ (1075541 / 50000) (430217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198186240 :
    ThetaLowerSegment 2198186240 2198317312 (219812820541897 / 100000)
      (219825963689577 / 100000) := by
  exact
    packedTile65536 2198186240 2198317312 14 6110 46884 31 _ _ (134443 / 6250) (2151091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198317312 :
    ThetaLowerSegment 2198317312 2198448384 (219825963689577 / 100000)
      (219838969203901 / 100000) := by
  exact
    packedTile65536 2198317312 2198448384 14 6046 46886 31 _ _ (1075547 / 50000) (2151097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198448384 :
    ThetaLowerSegment 2198448384 2198579456 (219838969203901 / 100000)
      (219851981207801 / 100000) := by
  exact
    packedTile65536 2198448384 2198579456 14 6049 46887 31 _ _ (21511 / 1000) (2151103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198579456 :
    ThetaLowerSegment 2198579456 2198710528 (219851981207801 / 100000)
      (219865210509701 / 100000) := by
  exact
    packedTile65536 2198579456 2198710528 14 6150 46889 31 _ _ (1075553 / 50000) (2151109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198710528 :
    ThetaLowerSegment 2198710528 2198841600 (219865210509701 / 100000)
      (219878302177333 / 100000) := by
  exact
    packedTile65536 2198710528 2198841600 14 6086 46890 31 _ _ (268889 / 12500) (430223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198841600 :
    ThetaLowerSegment 2198841600 2198972672 (219878302177333 / 100000)
      (219891333650177 / 100000) := by
  exact
    packedTile65536 2198841600 2198972672 14 6058 46891 31 _ _ (1075559 / 50000) (2151121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2198972672 :
    ThetaLowerSegment 2198972672 2199103744 (219891333650177 / 100000)
      (219904464111073 / 100000) := by
  exact
    packedTile65536 2198972672 2199103744 14 6104 46893 31 _ _ (537781 / 25000) (2151127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199103744 :
    ThetaLowerSegment 2199103744 2199234816 (219904464111073 / 100000)
      (219917652689103 / 100000) := by
  exact
    packedTile65536 2199103744 2199234816 14 6131 46894 31 _ _ (215113 / 10000) (2151133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199234816 :
    ThetaLowerSegment 2199234816 2199365888 (219917652689103 / 100000)
      (219930738049391 / 100000) := by
  exact
    packedTile65536 2199234816 2199365888 14 6083 46896 31 _ _ (67223 / 3125) (2151139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199365888 :
    ThetaLowerSegment 2199365888 2199496960 (219930738049391 / 100000)
      (219943829899603 / 100000) := by
  exact
    packedTile65536 2199365888 2199496960 14 6086 46897 31 _ _ (1075571 / 50000) (430229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199496960 :
    ThetaLowerSegment 2199496960 2199628032 (219943829899603 / 100000)
      (219956908879443 / 100000) := by
  exact
    packedTile65536 2199496960 2199628032 14 6080 46898 31 _ _ (537787 / 25000) (2151151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199628032 :
    ThetaLowerSegment 2199628032 2199759104 (219956908879443 / 100000) (8798789018199 / 4000) := by
  exact
    packedTile65536 2199628032 2199759104 14 5958 46900 31 _ _ (1075577 / 50000) (2151157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199759104 :
    ThetaLowerSegment 2199759104 2199890176 (8798789018199 / 4000) (8799311750079 / 4000) := by
  exact
    packedTile65536 2199759104 2199890176 14 6075 46901 31 _ _ (53779 / 2500) (2151163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2199890176 :
    ThetaLowerSegment 2199890176 2200021248 (8799311750079 / 4000) (219995939527401 / 100000) := by
  exact
    packedTile65536 2199890176 2200021248 14 6111 46902 31 _ _ (1075583 / 50000) (2151169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200021248 :
    ThetaLowerSegment 2200021248 2200152320 (219995939527401 / 100000)
      (220009074583633 / 100000) := by
  exact
    packedTile65536 2200021248 2200152320 14 6106 46904 31 _ _ (537793 / 25000) (86047 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200152320 :
    ThetaLowerSegment 2200152320 2200283392 (220009074583633 / 100000)
      (220022327991291 / 100000) := by
  exact
    packedTile65536 2200152320 2200283392 14 6161 46905 31 _ _ (1075589 / 50000) (2151181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200283392 :
    ThetaLowerSegment 2200283392 2200414464 (220022327991291 / 100000)
      (220035428701851 / 100000) := by
  exact
    packedTile65536 2200283392 2200414464 14 6090 46907 31 _ _ (134449 / 6250) (2151187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200414464 :
    ThetaLowerSegment 2200414464 2200545536 (220035428701851 / 100000)
      (220048387470411 / 100000) := by
  exact
    packedTile65536 2200414464 2200545536 14 6024 46908 31 _ _ (215119 / 10000) (2151193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200545536 :
    ThetaLowerSegment 2200545536 2200676608 (220048387470411 / 100000)
      (220061337670331 / 100000) := by
  exact
    packedTile65536 2200545536 2200676608 14 6020 46909 31 _ _ (537799 / 25000) (2151199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200676608 :
    ThetaLowerSegment 2200676608 2200807680 (220061337670331 / 100000)
      (44014910070603 / 20000) := by
  exact
    packedTile65536 2200676608 2200807680 14 6142 46911 31 _ _ (1075601 / 50000) (430241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200807680 :
    ThetaLowerSegment 2200807680 2200938752 (44014910070603 / 20000)
      (220087689931479 / 100000) := by
  exact
    packedTile65536 2200807680 2200938752 14 6108 46912 31 _ _ (268901 / 12500) (2151211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2200938752 :
    ThetaLowerSegment 2200938752 2201069824 (220087689931479 / 100000)
      (110050448114043 / 50000) := by
  exact
    packedTile65536 2200938752 2201069824 14 6139 46914 31 _ _ (2151213 / 100000) (134451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201069824 :
    ThetaLowerSegment 2201069824 2201200896 (110050448114043 / 50000) (44022743928909 / 20000) := by
  exact
    packedTile65536 2201069824 2201200896 14 5961 46915 31 _ _ (2151219 / 100000) (1075611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201200896 :
    ThetaLowerSegment 2201200896 2201331968 (44022743928909 / 20000) (22012686147807 / 10000) := by
  exact
    packedTile65536 2201200896 2201331968 14 6109 46916 31 _ _ (86049 / 4000) (537807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201331968 :
    ThetaLowerSegment 2201331968 2201463040 (22012686147807 / 10000) (27517496384973 / 12500) := by
  exact
    packedTile65536 2201331968 2201463040 14 6094 46918 31 _ _ (2151231 / 100000) (1075617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201463040 :
    ThetaLowerSegment 2201463040 2201594112 (27517496384973 / 12500)
      (220153237758363 / 100000) := by
  exact
    packedTile65536 2201463040 2201594112 14 6167 46919 31 _ _ (2151237 / 100000) (53781 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201594112 :
    ThetaLowerSegment 2201594112 2201725184 (220153237758363 / 100000)
      (220166214056139 / 100000) := by
  exact
    packedTile65536 2201594112 2201725184 14 6032 46921 31 _ _ (2151243 / 100000) (1075623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201725184 :
    ThetaLowerSegment 2201725184 2201856256 (220166214056139 / 100000)
      (55044823950327 / 25000) := by
  exact
    packedTile65536 2201725184 2201856256 14 6081 46922 31 _ _ (2151249 / 100000) (537813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201856256 :
    ThetaLowerSegment 2201856256 2201987328 (55044823950327 / 25000) (110096271614799 / 50000) := by
  exact
    packedTile65536 2201856256 2201987328 14 6158 46923 31 _ _ (430251 / 20000) (1075629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2201987328 :
    ThetaLowerSegment 2201987328 2202118400 (110096271614799 / 50000)
      (220205543299821 / 100000) := by
  exact
    packedTile65536 2201987328 2202118400 14 6043 46925 31 _ _ (2151261 / 100000) (67227 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202118400 :
    ThetaLowerSegment 2202118400 2202249472 (220205543299821 / 100000)
      (110109306123423 / 50000) := by
  exact
    packedTile65536 2202118400 2202249472 14 6075 46926 31 _ _ (2151267 / 100000) (215127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202249472 :
    ThetaLowerSegment 2202249472 2202380544 (110109306123423 / 50000) (44046331083009 / 20000) := by
  exact
    packedTile65536 2202249472 2202380544 14 6063 46928 31 _ _ (2151273 / 100000) (537819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202380544 :
    ThetaLowerSegment 2202380544 2202511616 (44046331083009 / 20000) (55061158520313 / 25000) := by
  exact
    packedTile65536 2202380544 2202511616 14 6033 46929 31 _ _ (2151279 / 100000) (1075641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202511616 :
    ThetaLowerSegment 2202511616 2202642688 (55061158520313 / 25000)
      (220257694532487 / 100000) := by
  exact
    packedTile65536 2202511616 2202642688 14 6071 46930 31 _ _ (430257 / 20000) (268911 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202642688 :
    ThetaLowerSegment 2202642688 2202773760 (220257694532487 / 100000)
      (110135233373577 / 50000) := by
  exact
    packedTile65536 2202642688 2202773760 14 5937 46932 31 _ _ (2151291 / 100000) (1075647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202773760 :
    ThetaLowerSegment 2202773760 2202904832 (110135233373577 / 50000)
      (110141794829427 / 50000) := by
  exact
    packedTile65536 2202773760 2202904832 14 6100 46933 31 _ _ (2151297 / 100000) (21513 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2202904832 :
    ThetaLowerSegment 2202904832 2203035904 (110141794829427 / 50000)
      (220296774994941 / 100000) := by
  exact
    packedTile65536 2202904832 2203035904 14 6129 46935 31 _ _ (2151303 / 100000) (1075653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203035904 :
    ThetaLowerSegment 2203035904 2203166976 (220296774994941 / 100000)
      (220309992637437 / 100000) := by
  exact
    packedTile65536 2203035904 2203166976 14 6144 46936 31 _ _ (2151309 / 100000) (134457 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203166976 :
    ThetaLowerSegment 2203166976 2203298048 (220309992637437 / 100000)
      (220323124264197 / 100000) := by
  exact
    packedTile65536 2203166976 2203298048 14 6104 46937 31 _ _ (430263 / 20000) (1075659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203298048 :
    ThetaLowerSegment 2203298048 2203429120 (220323124264197 / 100000)
      (55084037628213 / 25000) := by
  exact
    packedTile65536 2203298048 2203429120 14 6055 46939 31 _ _ (2151321 / 100000) (537831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203429120 :
    ThetaLowerSegment 2203429120 2203560192 (55084037628213 / 25000) (2203491101067 / 1000) := by
  exact
    packedTile65536 2203429120 2203560192 14 6024 46940 31 _ _ (2151327 / 100000) (215133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203560192 :
    ThetaLowerSegment 2203560192 2203691264 (2203491101067 / 1000) (220362188060007 / 100000) := by
  exact
    packedTile65536 2203560192 2203691264 14 6079 46942 31 _ _ (2151333 / 100000) (268917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203691264 :
    ThetaLowerSegment 2203691264 2203822336 (220362188060007 / 100000)
      (220375197200893 / 100000) := by
  exact
    packedTile65536 2203691264 2203822336 14 6047 46943 31 _ _ (1075669 / 50000) (2151341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203822336 :
    ThetaLowerSegment 2203822336 2203953408 (220375197200893 / 100000)
      (44077667522009 / 20000) := by
  exact
    packedTile65536 2203822336 2203953408 14 6108 46944 31 _ _ (134459 / 6250) (2151347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2203953408 :
    ThetaLowerSegment 2203953408 2204084480 (44077667522009 / 20000) (44080241397149 / 20000) := by
  exact
    packedTile65536 2203953408 2204084480 14 5982 46946 31 _ _ (43027 / 2000) (2151353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204084480 :
    ThetaLowerSegment 2204084480 2204215552 (44080241397149 / 20000)
      (220414444279213 / 100000) := by
  exact
    packedTile65536 2204084480 2204215552 14 6153 46947 31 _ _ (537839 / 25000) (2151359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204215552 :
    ThetaLowerSegment 2204215552 2204346624 (220414444279213 / 100000)
      (44085518250479 / 20000) := by
  exact
    packedTile65536 2204215552 2204346624 14 6111 46949 31 _ _ (1075681 / 50000) (430273 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204346624 :
    ThetaLowerSegment 2204346624 2204477696 (44085518250479 / 20000)
      (220440576909643 / 100000) := by
  exact
    packedTile65536 2204346624 2204477696 14 6036 46950 31 _ _ (268921 / 12500) (2151371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204477696 :
    ThetaLowerSegment 2204477696 2204608768 (220440576909643 / 100000)
      (220453721804783 / 100000) := by
  exact
    packedTile65536 2204477696 2204608768 14 6110 46951 31 _ _ (1075687 / 50000) (2151377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204608768 :
    ThetaLowerSegment 2204608768 2204739840 (220453721804783 / 100000)
      (220466802195183 / 100000) := by
  exact
    packedTile65536 2204608768 2204739840 14 6080 46953 31 _ _ (107569 / 5000) (2151383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204739840 :
    ThetaLowerSegment 2204739840 2204870912 (220466802195183 / 100000)
      (220479856805431 / 100000) := by
  exact
    packedTile65536 2204739840 2204870912 14 6068 46954 31 _ _ (1075693 / 50000) (2151389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2204870912 :
    ThetaLowerSegment 2204870912 2205001984 (220479856805431 / 100000)
      (220492971691063 / 100000) := by
  exact
    packedTile65536 2204870912 2205001984 14 6096 46956 31 _ _ (67231 / 3125) (430279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205001984 :
    ThetaLowerSegment 2205001984 2205133056 (220492971691063 / 100000)
      (220505860716481 / 100000) := by
  exact
    packedTile65536 2205001984 2205133056 14 5991 46957 31 _ _ (1075699 / 50000) (2151401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205133056 :
    ThetaLowerSegment 2205133056 2205264128 (220505860716481 / 100000)
      (220519068185637 / 100000) := by
  exact
    packedTile65536 2205133056 2205264128 14 6139 46958 31 _ _ (537851 / 25000) (2151407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205264128 :
    ThetaLowerSegment 2205264128 2205395200 (220519068185637 / 100000)
      (220532301508547 / 100000) := by
  exact
    packedTile65536 2205264128 2205395200 14 6151 46960 31 _ _ (215141 / 10000) (2151413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205395200 :
    ThetaLowerSegment 2205395200 2205526272 (220532301508547 / 100000)
      (220545504748539 / 100000) := by
  exact
    packedTile65536 2205395200 2205526272 14 6137 46961 31 _ _ (268927 / 12500) (2151419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205526272 :
    ThetaLowerSegment 2205526272 2205657344 (220545504748539 / 100000) (8822339801383 / 4000) := by
  exact
    packedTile65536 2205526272 2205657344 14 6038 46963 31 _ _ (1075711 / 50000) (86057 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205657344 :
    ThetaLowerSegment 2205657344 2205788416 (8822339801383 / 4000) (220571745679627 / 100000) := by
  exact
    packedTile65536 2205657344 2205788416 14 6159 46964 31 _ _ (537857 / 25000) (2151431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205788416 :
    ThetaLowerSegment 2205788416 2205919488 (220571745679627 / 100000)
      (220584867275593 / 100000) := by
  exact
    packedTile65536 2205788416 2205919488 14 6099 46965 31 _ _ (1075717 / 50000) (2151437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2205919488 :
    ThetaLowerSegment 2205919488 2206050560 (220584867275593 / 100000)
      (220597920062073 / 100000) := by
  exact
    packedTile65536 2205919488 2206050560 14 6067 46967 31 _ _ (26893 / 1250) (2151443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206050560 :
    ThetaLowerSegment 2206050560 2206181632 (220597920062073 / 100000)
      (110305561740019 / 50000) := by
  exact
    packedTile65536 2206050560 2206181632 14 6137 46968 31 _ _ (430289 / 20000) (268931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206181632 :
    ThetaLowerSegment 2206181632 2206312704 (110305561740019 / 50000)
      (110312037607529 / 50000) := by
  exact
    packedTile65536 2206181632 2206312704 14 6020 46970 31 _ _ (2151451 / 100000) (1075727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206312704 :
    ThetaLowerSegment 2206312704 2206443776 (110312037607529 / 50000) (22063723352607 / 10000) := by
  exact
    packedTile65536 2206312704 2206443776 14 6116 46971 31 _ _ (2151457 / 100000) (107573 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206443776 :
    ThetaLowerSegment 2206443776 2206574848 (22063723352607 / 10000) (4413009730763 / 2000) := by
  exact
    packedTile65536 2206443776 2206574848 14 6160 46972 31 _ _ (2151463 / 100000) (1075733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206574848 :
    ThetaLowerSegment 2206574848 2206705920 (4413009730763 / 2000) (44132707039527 / 20000) := by
  exact
    packedTile65536 2206574848 2206705920 14 6065 46974 31 _ _ (2151469 / 100000) (134467 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206705920 :
    ThetaLowerSegment 2206705920 2206836992 (44132707039527 / 20000) (44135333560207 / 20000) := by
  exact
    packedTile65536 2206705920 2206836992 14 6104 46975 31 _ _ (86059 / 4000) (1075739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206836992 :
    ThetaLowerSegment 2206836992 2206968064 (44135333560207 / 20000) (110344937871447 / 50000) := by
  exact
    packedTile65536 2206836992 2206968064 14 6139 46976 31 _ _ (2151481 / 100000) (537871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2206968064 :
    ThetaLowerSegment 2206968064 2207099136 (110344937871447 / 50000) (55175718756837 / 25000) := by
  exact
    packedTile65536 2206968064 2207099136 14 6042 46978 31 _ _ (2151487 / 100000) (215149 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207099136 :
    ThetaLowerSegment 2207099136 2207230208 (55175718756837 / 25000) (110358010324789 / 50000) := by
  exact
    packedTile65536 2207099136 2207230208 14 6110 46979 31 _ _ (2151493 / 100000) (268937 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207230208 :
    ThetaLowerSegment 2207230208 2207361280 (110358010324789 / 50000)
      (110364555184747 / 50000) := by
  exact
    packedTile65536 2207230208 2207361280 14 6084 46981 31 _ _ (2151499 / 100000) (1075751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207361280 :
    ThetaLowerSegment 2207361280 2207492352 (110364555184747 / 50000)
      (220742357185779 / 100000) := by
  exact
    packedTile65536 2207361280 2207492352 14 6157 46982 31 _ _ (430301 / 20000) (537877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207492352 :
    ThetaLowerSegment 2207492352 2207623424 (220742357185779 / 100000)
      (55188880570397 / 25000) := by
  exact
    packedTile65536 2207492352 2207623424 14 6119 46983 31 _ _ (2151511 / 100000) (1075757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207623424 :
    ThetaLowerSegment 2207623424 2207754496 (55188880570397 / 25000) (13798039332697 / 6250) := by
  exact
    packedTile65536 2207623424 2207754496 14 6092 46985 31 _ _ (2151517 / 100000) (13447 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207754496 :
    ThetaLowerSegment 2207754496 2207885568 (13798039332697 / 6250) (44156342546903 / 20000) := by
  exact
    packedTile65536 2207754496 2207885568 14 6081 46986 31 _ _ (2151523 / 100000) (1075763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2207885568 :
    ThetaLowerSegment 2207885568 2208016640 (44156342546903 / 20000)
      (220794845667531 / 100000) := by
  exact
    packedTile65536 2207885568 2208016640 14 6104 46988 31 _ _ (2151529 / 100000) (537883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208016640 :
    ThetaLowerSegment 2208016640 2208147712 (220794845667531 / 100000)
      (55202019939829 / 25000) := by
  exact
    packedTile65536 2208016640 2208147712 14 6151 46989 31 _ _ (430307 / 20000) (1075769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208147712 :
    ThetaLowerSegment 2208147712 2208278784 (55202019939829 / 25000) (55205325781039 / 25000) := by
  exact
    packedTile65536 2208147712 2208278784 14 6146 46990 31 _ _ (107577 / 5000) (2151543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208278784 :
    ThetaLowerSegment 2208278784 2208409856 (55205325781039 / 25000) (110417193337691 / 50000) := by
  exact
    packedTile65536 2208278784 2208409856 14 6081 46992 31 _ _ (1075773 / 50000) (2151549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208409856 :
    ThetaLowerSegment 2208409856 2208540928 (110417193337691 / 50000) (22084757353759 / 10000) := by
  exact
    packedTile65536 2208409856 2208540928 14 6129 46993 31 _ _ (67236 / 3125) (430311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208540928 :
    ThetaLowerSegment 2208540928 2208672000 (22084757353759 / 10000) (110430325353557 / 50000) := by
  exact
    packedTile65536 2208540928 2208672000 14 6078 46995 31 _ _ (1075779 / 50000) (2151561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208672000 :
    ThetaLowerSegment 2208672000 2208803072 (110430325353557 / 50000)
      (110436814470581 / 50000) := by
  exact
    packedTile65536 2208672000 2208803072 14 6032 46996 31 _ _ (537891 / 25000) (2151567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208803072 :
    ThetaLowerSegment 2208803072 2208934144 (110436814470581 / 50000)
      (110443452064031 / 50000) := by
  exact
    packedTile65536 2208803072 2208934144 14 6170 46997 31 _ _ (215157 / 10000) (2151573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2208934144 :
    ThetaLowerSegment 2208934144 2209065216 (110443452064031 / 50000)
      (110449927232003 / 50000) := by
  exact
    packedTile65536 2208934144 2209065216 14 6019 46999 31 _ _ (268947 / 12500) (2151579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209065216 :
    ThetaLowerSegment 2209065216 2209196288 (110449927232003 / 50000)
      (110456511072923 / 50000) := by
  exact
    packedTile65536 2209065216 2209196288 14 6120 47000 31 _ _ (1075791 / 50000) (430317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209196288 :
    ThetaLowerSegment 2209196288 2209327360 (110456511072923 / 50000)
      (110463118599671 / 50000) := by
  exact
    packedTile65536 2209196288 2209327360 14 6142 47002 31 _ _ (537897 / 25000) (2151591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209327360 :
    ThetaLowerSegment 2209327360 2209458432 (110463118599671 / 50000)
      (110469713235281 / 50000) := by
  exact
    packedTile65536 2209327360 2209458432 14 6130 47003 31 _ _ (1075797 / 50000) (2151597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209458432 :
    ThetaLowerSegment 2209458432 2209589504 (110469713235281 / 50000)
      (110476230431681 / 50000) := by
  exact
    packedTile65536 2209458432 2209589504 14 6058 47004 31 _ _ (5379 / 250) (2151603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209589504 :
    ThetaLowerSegment 2209589504 2209720576 (110476230431681 / 50000) (55241335632121 / 25000) := by
  exact
    packedTile65536 2209589504 2209720576 14 5987 47006 31 _ _ (1075803 / 50000) (2151609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209720576 :
    ThetaLowerSegment 2209720576 2209851648 (55241335632121 / 25000) (27622299544811 / 12500) := by
  exact
    packedTile65536 2209720576 2209851648 14 6067 47007 31 _ _ (537903 / 25000) (430323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209851648 :
    ThetaLowerSegment 2209851648 2209982720 (27622299544811 / 12500) (22099151907667 / 10000) := by
  exact
    packedTile65536 2209851648 2209982720 14 6099 47009 31 _ _ (1075809 / 50000) (2151621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2209982720 :
    ThetaLowerSegment 2209982720 2210113792 (22099151907667 / 10000) (110502276807431 / 50000) := by
  exact
    packedTile65536 2209982720 2210113792 14 6058 47010 31 _ _ (268953 / 12500) (2151627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210113792 :
    ThetaLowerSegment 2210113792 2210244864 (110502276807431 / 50000)
      (221017848530453 / 100000) := by
  exact
    packedTile65536 2210113792 2210244864 14 6179 47011 31 _ _ (2151629 / 100000) (134477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210244864 :
    ThetaLowerSegment 2210244864 2210375936 (221017848530453 / 100000)
      (110515434036919 / 50000) := by
  exact
    packedTile65536 2210244864 2210375936 14 6051 47013 31 _ _ (430327 / 20000) (1075819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210375936 :
    ThetaLowerSegment 2210375936 2210507008 (110515434036919 / 50000)
      (221044016751989 / 100000) := by
  exact
    packedTile65536 2210375936 2210507008 14 6111 47014 31 _ _ (2151641 / 100000) (537911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210507008 :
    ThetaLowerSegment 2210507008 2210638080 (221044016751989 / 100000)
      (221056991183399 / 100000) := by
  exact
    packedTile65536 2210507008 2210638080 14 6030 47016 31 _ _ (2151647 / 100000) (43033 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210638080 :
    ThetaLowerSegment 2210638080 2210769152 (221056991183399 / 100000)
      (110535052754217 / 50000) := by
  exact
    packedTile65536 2210638080 2210769152 14 6095 47017 31 _ _ (2151653 / 100000) (268957 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210769152 :
    ThetaLowerSegment 2210769152 2210900224 (110535052754217 / 50000) (44216641392017 / 20000) := by
  exact
    packedTile65536 2210769152 2210900224 14 6089 47018 31 _ _ (2151659 / 100000) (1075831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2210900224 :
    ThetaLowerSegment 2210900224 2211031296 (44216641392017 / 20000) (44219261259321 / 20000) := by
  exact
    packedTile65536 2210900224 2211031296 14 6088 47020 31 _ _ (430333 / 20000) (537917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211031296 :
    ThetaLowerSegment 2211031296 2211162368 (44219261259321 / 20000) (110554727579043 / 50000) := by
  exact
    packedTile65536 2211031296 2211162368 14 6111 47021 31 _ _ (2151671 / 100000) (1075837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211162368 :
    ThetaLowerSegment 2211162368 2211293440 (110554727579043 / 50000)
      (221122406101949 / 100000) := by
  exact
    packedTile65536 2211162368 2211293440 14 6019 47022 31 _ _ (2151677 / 100000) (13448 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211293440 :
    ThetaLowerSegment 2211293440 2211424512 (221122406101949 / 100000)
      (221135367840341 / 100000) := by
  exact
    packedTile65536 2211293440 2211424512 14 6024 47024 31 _ _ (2151683 / 100000) (1075843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211424512 :
    ThetaLowerSegment 2211424512 2211555584 (221135367840341 / 100000)
      (22114849529493 / 10000) := by
  exact
    packedTile65536 2211424512 2211555584 14 6101 47025 31 _ _ (2151689 / 100000) (537923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211555584 :
    ThetaLowerSegment 2211555584 2211686656 (22114849529493 / 10000) (44232314229089 / 20000) := by
  exact
    packedTile65536 2211555584 2211686656 14 6077 47027 31 _ _ (430339 / 20000) (1075849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211686656 :
    ThetaLowerSegment 2211686656 2211817728 (44232314229089 / 20000) (110587357943427 / 50000) := by
  exact
    packedTile65536 2211686656 2211817728 14 6109 47028 31 _ _ (2151701 / 100000) (268963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211817728 :
    ThetaLowerSegment 2211817728 2211948800 (110587357943427 / 50000)
      (221187813327363 / 100000) := by
  exact
    packedTile65536 2211817728 2211948800 14 6087 47029 31 _ _ (2151707 / 100000) (215171 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2211948800 :
    ThetaLowerSegment 2211948800 2212079872 (221187813327363 / 100000)
      (221200798909283 / 100000) := by
  exact
    packedTile65536 2211948800 2212079872 14 6035 47031 31 _ _ (67241 / 3125) (430343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212079872 :
    ThetaLowerSegment 2212079872 2212210944 (221200798909283 / 100000)
      (221213960968289 / 100000) := by
  exact
    packedTile65536 2212079872 2212210944 14 6117 47032 31 _ _ (1075859 / 50000) (2151721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212210944 :
    ThetaLowerSegment 2212210944 2212342016 (221213960968289 / 100000)
      (221227206981233 / 100000) := by
  exact
    packedTile65536 2212210944 2212342016 14 6156 47034 31 _ _ (537931 / 25000) (2151727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212342016 :
    ThetaLowerSegment 2212342016 2212473088 (221227206981233 / 100000)
      (221240388479213 / 100000) := by
  exact
    packedTile65536 2212342016 2212473088 14 6126 47035 31 _ _ (215173 / 10000) (2151733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212473088 :
    ThetaLowerSegment 2212473088 2212604160 (221240388479213 / 100000)
      (44250701522721 / 20000) := by
  exact
    packedTile65536 2212473088 2212604160 14 6097 47036 31 _ _ (268967 / 12500) (2151739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212604160 :
    ThetaLowerSegment 2212604160 2212735232 (44250701522721 / 20000)
      (221266758040841 / 100000) := by
  exact
    packedTile65536 2212604160 2212735232 14 6158 47038 31 _ _ (1075871 / 50000) (430349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212735232 :
    ThetaLowerSegment 2212735232 2212866304 (221266758040841 / 100000)
      (44256008156249 / 20000) := by
  exact
    packedTile65536 2212735232 2212866304 14 6173 47039 31 _ _ (537937 / 25000) (2151751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212866304 :
    ThetaLowerSegment 2212866304 2212997376 (44256008156249 / 20000) (44258648358407 / 20000) := by
  exact
    packedTile65536 2212866304 2212997376 14 6135 47041 31 _ _ (1075877 / 50000) (2151757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2212997376 :
    ThetaLowerSegment 2212997376 2213128448 (44258648358407 / 20000) (44261269632439 / 20000) := by
  exact
    packedTile65536 2212997376 2213128448 14 6091 47042 31 _ _ (26897 / 1250) (2151763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213128448 :
    ThetaLowerSegment 2213128448 2213259520 (44261269632439 / 20000)
      (221319587978393 / 100000) := by
  exact
    packedTile65536 2213128448 2213259520 14 6153 47043 31 _ _ (1075883 / 50000) (2151769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213259520 :
    ThetaLowerSegment 2213259520 2213390592 (221319587978393 / 100000)
      (221332614806081 / 100000) := by
  exact
    packedTile65536 2213259520 2213390592 14 6054 47045 31 _ _ (537943 / 25000) (86071 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213390592 :
    ThetaLowerSegment 2213390592 2213521664 (221332614806081 / 100000)
      (221345770776773 / 100000) := by
  exact
    packedTile65536 2213390592 2213521664 14 6114 47046 31 _ _ (1075889 / 50000) (2151781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213521664 :
    ThetaLowerSegment 2213521664 2213652736 (221345770776773 / 100000)
      (221358715909317 / 100000) := by
  exact
    packedTile65536 2213521664 2213652736 14 6016 47048 31 _ _ (268973 / 12500) (2151787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213652736 :
    ThetaLowerSegment 2213652736 2213783808 (221358715909317 / 100000)
      (221372001054603 / 100000) := by
  exact
    packedTile65536 2213652736 2213783808 14 6174 47049 31 _ _ (2151789 / 100000) (134487 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213783808 :
    ThetaLowerSegment 2213783808 2213914880 (221372001054603 / 100000)
      (110692474202559 / 50000) := by
  exact
    packedTile65536 2213783808 2213914880 14 6017 47050 31 _ _ (430359 / 20000) (1075899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2213914880 :
    ThetaLowerSegment 2213914880 2214045952 (110692474202559 / 50000)
      (221397814023297 / 100000) := by
  exact
    packedTile65536 2213914880 2214045952 14 5979 47052 31 _ _ (2151801 / 100000) (537951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214045952 :
    ThetaLowerSegment 2214045952 2214177024 (221397814023297 / 100000)
      (221410832455647 / 100000) := by
  exact
    packedTile65536 2214045952 2214177024 14 6050 47053 31 _ _ (2151807 / 100000) (215181 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214177024 :
    ThetaLowerSegment 2214177024 2214308096 (221410832455647 / 100000)
      (44284768463409 / 20000) := by
  exact
    packedTile65536 2214177024 2214308096 14 6046 47055 31 _ _ (2151813 / 100000) (268977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214308096 :
    ThetaLowerSegment 2214308096 2214439168 (44284768463409 / 20000) (110718530470581 / 50000) := by
  exact
    packedTile65536 2214308096 2214439168 14 6143 47056 31 _ _ (2151819 / 100000) (1075911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214439168 :
    ThetaLowerSegment 2214439168 2214570240 (110718530470581 / 50000)
      (221450047205037 / 100000) := by
  exact
    packedTile65536 2214439168 2214570240 14 6035 47057 31 _ _ (86073 / 4000) (537957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214570240 :
    ThetaLowerSegment 2214570240 2214701312 (221450047205037 / 100000)
      (221463095908221 / 100000) := by
  exact
    packedTile65536 2214570240 2214701312 14 6064 47059 31 _ _ (2151831 / 100000) (1075917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214701312 :
    ThetaLowerSegment 2214701312 2214832384 (221463095908221 / 100000) (13842263209671 / 6250) := by
  exact
    packedTile65536 2214701312 2214832384 14 6095 47060 31 _ _ (2151837 / 100000) (13449 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214832384 :
    ThetaLowerSegment 2214832384 2214963456 (13842263209671 / 6250) (221489262282531 / 100000) := by
  exact
    packedTile65536 2214832384 2214963456 14 6065 47062 31 _ _ (2151843 / 100000) (1075923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2214963456 :
    ThetaLowerSegment 2214963456 2215094528 (221489262282531 / 100000)
      (55375599830169 / 25000) := by
  exact
    packedTile65536 2214963456 2215094528 14 6105 47063 31 _ _ (2151849 / 100000) (537963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215094528 :
    ThetaLowerSegment 2215094528 2215225600 (55375599830169 / 25000)
      (221515351335921 / 100000) := by
  exact
    packedTile65536 2215094528 2215225600 14 6019 47064 31 _ _ (430371 / 20000) (1075929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215225600 :
    ThetaLowerSegment 2215225600 2215356672 (221515351335921 / 100000)
      (27691035771549 / 12500) := by
  exact
    packedTile65536 2215225600 2215356672 14 6011 47066 31 _ _ (2151861 / 100000) (268983 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215356672 :
    ThetaLowerSegment 2215356672 2215487744 (27691035771549 / 12500) (55385392948269 / 25000) := by
  exact
    packedTile65536 2215356672 2215487744 14 6174 47067 31 _ _ (1075933 / 50000) (2151869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215487744 :
    ThetaLowerSegment 2215487744 2215618816 (55385392948269 / 25000) (55388647654669 / 25000) := by
  exact
    packedTile65536 2215487744 2215618816 14 6050 47068 31 _ _ (67246 / 3125) (3443 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215618816 :
    ThetaLowerSegment 2215618816 2215749888 (55388647654669 / 25000) (110783779993691 / 50000) := by
  exact
    packedTile65536 2215618816 2215749888 14 6027 47070 31 _ _ (1075939 / 50000) (2151881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215749888 :
    ThetaLowerSegment 2215749888 2215880960 (110783779993691 / 50000)
      (110790344315833 / 50000) := by
  exact
    packedTile65536 2215749888 2215880960 14 6101 47071 31 _ _ (537971 / 25000) (2151887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2215880960 :
    ThetaLowerSegment 2215880960 2216012032 (110790344315833 / 50000)
      (110796804289613 / 50000) := by
  exact
    packedTile65536 2215880960 2216012032 14 6004 47073 31 _ _ (215189 / 10000) (2151893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216012032 :
    ThetaLowerSegment 2216012032 2216143104 (110796804289613 / 50000)
      (110803454724201 / 50000) := by
  exact
    packedTile65536 2216012032 2216143104 14 6181 47074 31 _ _ (268987 / 12500) (2151899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216143104 :
    ThetaLowerSegment 2216143104 2216274176 (110803454724201 / 50000)
      (110810013721497 / 50000) := by
  exact
    packedTile65536 2216143104 2216274176 14 6096 47075 31 _ _ (1075951 / 50000) (430381 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216274176 :
    ThetaLowerSegment 2216274176 2216405248 (110810013721497 / 50000)
      (110816673876757 / 50000) := by
  exact
    packedTile65536 2216274176 2216405248 14 6190 47077 31 _ _ (537977 / 25000) (2151911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216405248 :
    ThetaLowerSegment 2216405248 2216536320 (110816673876757 / 50000)
      (110823323291017 / 50000) := by
  exact
    packedTile65536 2216405248 2216536320 14 6180 47078 31 _ _ (1075957 / 50000) (2151917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216536320 :
    ThetaLowerSegment 2216536320 2216667392 (110823323291017 / 50000)
      (110829860823977 / 50000) := by
  exact
    packedTile65536 2216536320 2216667392 14 6076 47080 31 _ _ (26899 / 1250) (2151923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216667392 :
    ThetaLowerSegment 2216667392 2216798464 (110829860823977 / 50000) (22167286130811 / 10000) := by
  exact
    packedTile65536 2216667392 2216798464 14 6106 47081 31 _ _ (1075963 / 50000) (2151929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216798464 :
    ThetaLowerSegment 2216798464 2216929536 (22167286130811 / 10000) (4433717179427 / 2000) := by
  exact
    packedTile65536 2216798464 2216929536 14 6040 47082 31 _ _ (2151931 / 100000) (1075967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2216929536 :
    ThetaLowerSegment 2216929536 2217060608 (4433717179427 / 2000) (221699030977727 / 100000) := by
  exact
    packedTile65536 2216929536 2217060608 14 6121 47084 31 _ _ (2151937 / 100000) (107597 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217060608 :
    ThetaLowerSegment 2217060608 2217191680 (221699030977727 / 100000)
      (22171220302083 / 10000) := by
  exact
    packedTile65536 2217060608 2217191680 14 6121 47085 31 _ _ (2151943 / 100000) (1075973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217191680 :
    ThetaLowerSegment 2217191680 2217322752 (22171220302083 / 10000)
      (221725237375923 / 100000) := by
  exact
    packedTile65536 2217191680 2217322752 14 6057 47087 31 _ _ (2151949 / 100000) (134497 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217322752 :
    ThetaLowerSegment 2217322752 2217339136 (221725237375923 / 100000)
      (221726907293003 / 100000) := by
  exact
    packedTile65536 2217322752 2217339136 11 776 47088 31 _ _ (430391 / 20000) (1075979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2217339136 :
    ThetaLowerSegment 2217339136 2217341184 (221726907293003 / 100000)
      (221727109576867 / 100000) := by
  exact
    packedTile65536 2217339136 2217341184 8 94 47088 31 _ _ (537989 / 25000) (2151959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2185341184_2217341184 :
    ThetaLowerSegment 2185341184 2217341184 (218527790796803 / 100000)
      (221727109576867 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2185341184 cell2185472256)
                  (ThetaLowerSegment.join cell2185603328 cell2185734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2185865472 cell2185996544)
                  (ThetaLowerSegment.join cell2186127616 cell2186258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2186389760 cell2186520832)
                  (ThetaLowerSegment.join cell2186651904 cell2186782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2186914048 cell2187045120)
                  (ThetaLowerSegment.join cell2187176192 cell2187307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2187438336 cell2187569408)
                  (ThetaLowerSegment.join cell2187700480 cell2187831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2187962624 cell2188093696)
                  (ThetaLowerSegment.join cell2188224768 cell2188355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2188486912 cell2188617984)
                  (ThetaLowerSegment.join cell2188749056 cell2188880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2189011200 cell2189142272)
                  (ThetaLowerSegment.join cell2189273344 cell2189404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2189535488 cell2189666560)
                  (ThetaLowerSegment.join cell2189797632 cell2189928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2190059776 cell2190190848)
                  (ThetaLowerSegment.join cell2190321920 cell2190452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2190584064 cell2190715136)
                  (ThetaLowerSegment.join cell2190846208 cell2190977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2191108352 cell2191239424)
                  (ThetaLowerSegment.join cell2191370496 cell2191501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2191632640 cell2191763712)
                  (ThetaLowerSegment.join cell2191894784 cell2192025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2192156928 cell2192288000)
                  (ThetaLowerSegment.join cell2192419072 cell2192550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2192681216 cell2192812288)
                  (ThetaLowerSegment.join cell2192943360 cell2193074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2193205504 cell2193336576)
                  (ThetaLowerSegment.join cell2193467648 cell2193598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2193729792 cell2193860864)
                  (ThetaLowerSegment.join cell2193991936 cell2194123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2194254080 cell2194385152)
                  (ThetaLowerSegment.join cell2194516224 cell2194647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2194778368 cell2194909440)
                  (ThetaLowerSegment.join cell2195040512 cell2195171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2195302656 cell2195433728)
                  (ThetaLowerSegment.join cell2195564800 cell2195695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2195826944 cell2195958016)
                  (ThetaLowerSegment.join cell2196089088 cell2196220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2196351232 cell2196482304)
                  (ThetaLowerSegment.join cell2196613376 cell2196744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2196875520 cell2197006592)
                  (ThetaLowerSegment.join cell2197137664 cell2197268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2197399808 cell2197530880)
                  (ThetaLowerSegment.join cell2197661952 cell2197793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2197924096 cell2198055168)
                  (ThetaLowerSegment.join cell2198186240 cell2198317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2198448384 cell2198579456)
                  (ThetaLowerSegment.join cell2198710528 cell2198841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2198972672 cell2199103744)
                  (ThetaLowerSegment.join cell2199234816 cell2199365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2199496960 cell2199628032)
                  (ThetaLowerSegment.join cell2199759104 cell2199890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2200021248 cell2200152320)
                  (ThetaLowerSegment.join cell2200283392 cell2200414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2200545536 cell2200676608)
                  (ThetaLowerSegment.join cell2200807680 cell2200938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2201069824 cell2201200896)
                  (ThetaLowerSegment.join cell2201331968 cell2201463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2201594112 cell2201725184)
                  (ThetaLowerSegment.join cell2201856256 cell2201987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2202118400 cell2202249472)
                  (ThetaLowerSegment.join cell2202380544 cell2202511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2202642688 cell2202773760)
                  (ThetaLowerSegment.join cell2202904832 cell2203035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2203166976 cell2203298048)
                  (ThetaLowerSegment.join cell2203429120 cell2203560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2203691264 cell2203822336)
                  (ThetaLowerSegment.join cell2203953408 cell2204084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2204215552 cell2204346624)
                  (ThetaLowerSegment.join cell2204477696 cell2204608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2204739840 cell2204870912)
                  (ThetaLowerSegment.join cell2205001984 cell2205133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2205264128 cell2205395200)
                  (ThetaLowerSegment.join cell2205526272 cell2205657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2205788416 cell2205919488)
                  (ThetaLowerSegment.join cell2206050560 cell2206181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2206312704 cell2206443776)
                  (ThetaLowerSegment.join cell2206574848 cell2206705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2206836992 cell2206968064)
                  (ThetaLowerSegment.join cell2207099136 cell2207230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2207361280 cell2207492352)
                  (ThetaLowerSegment.join cell2207623424 cell2207754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2207885568 cell2208016640)
                  (ThetaLowerSegment.join cell2208147712 cell2208278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2208409856 cell2208540928)
                  (ThetaLowerSegment.join cell2208672000 cell2208803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2208934144 cell2209065216)
                  (ThetaLowerSegment.join cell2209196288 cell2209327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2209458432 cell2209589504)
                  (ThetaLowerSegment.join cell2209720576 cell2209851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2209982720 cell2210113792)
                  (ThetaLowerSegment.join cell2210244864 cell2210375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2210507008 cell2210638080)
                  (ThetaLowerSegment.join cell2210769152 cell2210900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2211031296 cell2211162368)
                  (ThetaLowerSegment.join cell2211293440 cell2211424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2211555584 cell2211686656)
                  (ThetaLowerSegment.join cell2211817728 cell2211948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2212079872 cell2212210944)
                  (ThetaLowerSegment.join cell2212342016 cell2212473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2212604160 cell2212735232)
                  (ThetaLowerSegment.join cell2212866304 cell2212997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2213128448 cell2213259520)
                  (ThetaLowerSegment.join cell2213390592 cell2213521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2213652736 cell2213783808)
                  (ThetaLowerSegment.join cell2213914880 cell2214045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2214177024 cell2214308096)
                  (ThetaLowerSegment.join cell2214439168 cell2214570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2214701312 cell2214832384)
                  (ThetaLowerSegment.join cell2214963456 cell2215094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2215225600 cell2215356672)
                  (ThetaLowerSegment.join cell2215487744 cell2215618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2215749888 cell2215880960)
                  (ThetaLowerSegment.join cell2216012032 cell2216143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2216274176 cell2216405248)
                  (ThetaLowerSegment.join cell2216536320 cell2216667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2216798464 cell2216929536)
                (ThetaLowerSegment.join cell2217060608 cell2217191680))
              (ThetaLowerSegment.join cell2217322752 cell2217339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
