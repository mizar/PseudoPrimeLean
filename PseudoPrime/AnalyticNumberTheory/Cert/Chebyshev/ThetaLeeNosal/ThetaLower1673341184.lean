/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1673341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1641341184 :
    ThetaLowerSegment 1641341184 1641472256 (41032649277723 / 25000) (20517955035333 / 12500) := by
  exact
    packedTile65536 1641341184 1641472256 14 6147 40513 31 _ _ (530469 / 25000) (2121879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641472256 :
    ThetaLowerSegment 1641472256 1641603328 (20517955035333 / 12500) (41039170875903 / 25000) := by
  exact
    packedTile65536 1641472256 1641603328 14 6147 40515 31 _ _ (530471 / 25000) (2121887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641603328 :
    ThetaLowerSegment 1641603328 1641734400 (41039170875903 / 25000) (20521237065637 / 12500) := by
  exact
    packedTile65536 1641603328 1641734400 14 6227 40516 31 _ _ (530473 / 25000) (424379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641734400 :
    ThetaLowerSegment 1641734400 1641865472 (20521237065637 / 12500) (41045731778249 / 25000) := by
  exact
    packedTile65536 1641734400 1641865472 14 6141 40518 31 _ _ (21219 / 1000) (2121903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641865472 :
    ThetaLowerSegment 1641865472 1641996544 (41045731778249 / 25000) (41049037710913 / 25000) := by
  exact
    packedTile65536 1641865472 1641996544 14 6232 40519 31 _ _ (530477 / 25000) (2121911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641996544 :
    ThetaLowerSegment 1641996544 1642127616 (41049037710913 / 25000) (41052307583469 / 25000) := by
  exact
    packedTile65536 1641996544 1642127616 14 6164 40521 31 _ _ (530479 / 25000) (2121919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642127616 :
    ThetaLowerSegment 1642127616 1642258688 (41052307583469 / 25000) (41055560492961 / 25000) := by
  exact
    packedTile65536 1642127616 1642258688 14 6132 40523 31 _ _ (530481 / 25000) (2121927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642258688 :
    ThetaLowerSegment 1642258688 1642389760 (41055560492961 / 25000) (41058846304663 / 25000) := by
  exact
    packedTile65536 1642258688 1642389760 14 6194 40524 31 _ _ (530483 / 25000) (424387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642389760 :
    ThetaLowerSegment 1642389760 1642520832 (41058846304663 / 25000) (5132766184541 / 3125) := by
  exact
    packedTile65536 1642389760 1642520832 14 6189 40526 31 _ _ (106097 / 5000) (2121943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642520832 :
    ThetaLowerSegment 1642520832 1642651904 (5132766184541 / 3125) (20532715083221 / 12500) := by
  exact
    packedTile65536 1642520832 1642651904 14 6222 40528 31 _ _ (530487 / 25000) (2121951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642651904 :
    ThetaLowerSegment 1642651904 1642782976 (20532715083221 / 12500) (5133590297647 / 3125) := by
  exact
    packedTile65536 1642651904 1642782976 14 6206 40529 31 _ _ (530489 / 25000) (2121959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642782976 :
    ThetaLowerSegment 1642782976 1642914048 (5133590297647 / 3125) (41071985431317 / 25000) := by
  exact
    packedTile65536 1642782976 1642914048 14 6151 40531 31 _ _ (530491 / 25000) (2121967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642914048 :
    ThetaLowerSegment 1642914048 1643045120 (41071985431317 / 25000) (4107522196911 / 2500) := by
  exact
    packedTile65536 1642914048 1643045120 14 6101 40532 31 _ _ (530493 / 25000) (84879 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643045120 :
    ThetaLowerSegment 1643045120 1643176192 (4107522196911 / 2500) (1643138680281 / 1000) := by
  exact
    packedTile65536 1643045120 1643176192 14 6117 40534 31 _ _ (106099 / 5000) (2121983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643176192 :
    ThetaLowerSegment 1643176192 1643307264 (1643138680281 / 1000) (20540878309461 / 12500) := by
  exact
    packedTile65536 1643176192 1643307264 14 6201 40536 31 _ _ (530497 / 25000) (2121991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643307264 :
    ThetaLowerSegment 1643307264 1643438336 (20540878309461 / 12500) (2054251808187 / 1250) := by
  exact
    packedTile65536 1643307264 1643438336 14 6182 40537 31 _ _ (530499 / 25000) (2121999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643438336 :
    ThetaLowerSegment 1643438336 1643569408 (2054251808187 / 1250) (5136037740987 / 3125) := by
  exact
    packedTile65536 1643438336 1643569408 14 6156 40539 31 _ _ (530501 / 25000) (2122007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643569408 :
    ThetaLowerSegment 1643569408 1643700480 (5136037740987 / 3125) (41091558685813 / 25000) := by
  exact
    packedTile65536 1643569408 1643700480 14 6139 40540 31 _ _ (530503 / 25000) (424403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643700480 :
    ThetaLowerSegment 1643700480 1643831552 (41091558685813 / 25000) (41094858426913 / 25000) := by
  exact
    packedTile65536 1643700480 1643831552 14 6220 40542 31 _ _ (106101 / 5000) (2122023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643831552 :
    ThetaLowerSegment 1643831552 1643962624 (41094858426913 / 25000) (20549074580917 / 12500) := by
  exact
    packedTile65536 1643831552 1643962624 14 6203 40544 31 _ _ (530507 / 25000) (2122031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1643962624 :
    ThetaLowerSegment 1643962624 1644093696 (20549074580917 / 12500) (41101375187063 / 25000) := by
  exact
    packedTile65536 1643962624 1644093696 14 6081 40545 31 _ _ (530509 / 25000) (2122039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644093696 :
    ThetaLowerSegment 1644093696 1644224768 (41101375187063 / 25000) (41104639951757 / 25000) := by
  exact
    packedTile65536 1644093696 1644224768 14 6154 40547 31 _ _ (530511 / 25000) (2122047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644224768 :
    ThetaLowerSegment 1644224768 1644355840 (41104639951757 / 25000) (10276977906357 / 6250) := by
  exact
    packedTile65536 1644224768 1644355840 14 6167 40549 31 _ _ (530513 / 25000) (424411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644355840 :
    ThetaLowerSegment 1644355840 1644486912 (10276977906357 / 6250) (20555583963249 / 12500) := by
  exact
    packedTile65536 1644355840 1644486912 14 6138 40550 31 _ _ (106103 / 5000) (2122063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644486912 :
    ThetaLowerSegment 1644486912 1644617984 (20555583963249 / 12500) (20557223260779 / 12500) := by
  exact
    packedTile65536 1644486912 1644617984 14 6180 40552 31 _ _ (530517 / 25000) (2122071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644617984 :
    ThetaLowerSegment 1644617984 1644749056 (20557223260779 / 12500) (41117745819219 / 25000) := by
  exact
    packedTile65536 1644617984 1644749056 14 6219 40553 31 _ _ (530519 / 25000) (2122079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644749056 :
    ThetaLowerSegment 1644749056 1644880128 (41117745819219 / 25000) (41120949105017 / 25000) := by
  exact
    packedTile65536 1644749056 1644880128 14 6038 40555 31 _ _ (530521 / 25000) (2122087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644880128 :
    ThetaLowerSegment 1644880128 1645011200 (41120949105017 / 25000) (2056208760769 / 1250) := by
  exact
    packedTile65536 1644880128 1645011200 14 6081 40557 31 _ _ (530523 / 25000) (424419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645011200 :
    ThetaLowerSegment 1645011200 1645142272 (2056208760769 / 1250) (4112746128723 / 2500) := by
  exact
    packedTile65536 1645011200 1645142272 14 6194 40558 31 _ _ (21221 / 1000) (2122103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645142272 :
    ThetaLowerSegment 1645142272 1645273344 (4112746128723 / 2500) (20565383765747 / 12500) := by
  exact
    packedTile65536 1645142272 1645273344 14 6232 40560 31 _ _ (530527 / 25000) (2122111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645273344 :
    ThetaLowerSegment 1645273344 1645404416 (20565383765747 / 12500) (41134038242779 / 25000) := by
  exact
    packedTile65536 1645273344 1645404416 14 6165 40561 31 _ _ (530529 / 25000) (2122119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645404416 :
    ThetaLowerSegment 1645404416 1645535488 (41134038242779 / 25000) (41137299947367 / 25000) := by
  exact
    packedTile65536 1645404416 1645535488 14 6148 40563 31 _ _ (530531 / 25000) (2122127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645535488 :
    ThetaLowerSegment 1645535488 1645666560 (41137299947367 / 25000) (41140598801561 / 25000) := by
  exact
    packedTile65536 1645535488 1645666560 14 6218 40565 31 _ _ (530533 / 25000) (424427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645666560 :
    ThetaLowerSegment 1645666560 1645797632 (41140598801561 / 25000) (41143897668191 / 25000) := by
  exact
    packedTile65536 1645666560 1645797632 14 6218 40566 31 _ _ (106107 / 5000) (2122143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645797632 :
    ThetaLowerSegment 1645797632 1645928704 (41143897668191 / 25000) (4114715887913 / 2500) := by
  exact
    packedTile65536 1645797632 1645928704 14 6147 40568 31 _ _ (530537 / 25000) (2122151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1645928704 :
    ThetaLowerSegment 1645928704 1646059776 (4114715887913 / 2500) (8230093357959 / 5000) := by
  exact
    packedTile65536 1645928704 1646059776 14 6235 40570 31 _ _ (530539 / 25000) (2122159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646059776 :
    ThetaLowerSegment 1646059776 1646190848 (8230093357959 / 5000) (41153707334223 / 25000) := by
  exact
    packedTile65536 1646059776 1646190848 14 6108 40571 31 _ _ (530541 / 25000) (2122167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646190848 :
    ThetaLowerSegment 1646190848 1646321920 (41153707334223 / 25000) (32925594388379 / 20000) := by
  exact
    packedTile65536 1646190848 1646321920 14 6193 40573 31 _ _ (2122171 / 100000) (1061087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646321920 :
    ThetaLowerSegment 1646321920 1646452992 (32925594388379 / 20000)
      (164641036075819 / 100000) := by
  exact
    packedTile65536 1646321920 1646452992 14 6156 40574 31 _ _ (2122179 / 100000) (1061091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646452992 :
    ThetaLowerSegment 1646452992 1646584064 (164641036075819 / 100000)
      (32930820900673 / 20000) := by
  exact
    packedTile65536 1646452992 1646584064 14 6158 40576 31 _ _ (2122187 / 100000) (212219 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646584064 :
    ThetaLowerSegment 1646584064 1646715136 (32930820900673 / 20000) (32933460911253 / 20000) := by
  exact
    packedTile65536 1646584064 1646715136 14 6220 40578 31 _ _ (424439 / 20000) (1061099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646715136 :
    ThetaLowerSegment 1646715136 1646846208 (32933460911253 / 20000)
      (164680211794911 / 100000) := by
  exact
    packedTile65536 1646715136 1646846208 14 6082 40579 31 _ _ (2122203 / 100000) (1061103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646846208 :
    ThetaLowerSegment 1646846208 1646977280 (164680211794911 / 100000)
      (164693348281001 / 100000) := by
  exact
    packedTile65536 1646846208 1646977280 14 6190 40581 31 _ _ (2122211 / 100000) (1061107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1646977280 :
    ThetaLowerSegment 1646977280 1647108352 (164693348281001 / 100000) (5147079175864 / 3125) := by
  exact
    packedTile65536 1646977280 1647108352 14 6213 40582 31 _ _ (2122219 / 100000) (1061111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647108352 :
    ThetaLowerSegment 1647108352 1647239424 (5147079175864 / 3125) (164719685068367 / 100000) := by
  exact
    packedTile65536 1647108352 1647239424 14 6197 40584 31 _ _ (2122227 / 100000) (212223 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647239424 :
    ThetaLowerSegment 1647239424 1647370496 (164719685068367 / 100000)
      (164732690124447 / 100000) := by
  exact
    packedTile65536 1647239424 1647370496 14 6128 40586 31 _ _ (424447 / 20000) (1061119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647370496 :
    ThetaLowerSegment 1647370496 1647501568 (164732690124447 / 100000) (5148309011052 / 3125) := by
  exact
    packedTile65536 1647370496 1647501568 14 6219 40587 31 _ _ (2122243 / 100000) (1061123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647501568 :
    ThetaLowerSegment 1647501568 1647632640 (5148309011052 / 3125) (20594868055227 / 12500) := by
  exact
    packedTile65536 1647501568 1647632640 14 6152 40589 31 _ _ (2122251 / 100000) (1061127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647632640 :
    ThetaLowerSegment 1647632640 1647763712 (20594868055227 / 12500)
      (164772159748609 / 100000) := by
  exact
    packedTile65536 1647632640 1647763712 14 6227 40591 31 _ _ (2122259 / 100000) (1061131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647763712 :
    ThetaLowerSegment 1647763712 1647894784 (164772159748609 / 100000)
      (41196334226103 / 25000) := by
  exact
    packedTile65536 1647763712 1647894784 14 6209 40592 31 _ _ (2122267 / 100000) (212227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1647894784 :
    ThetaLowerSegment 1647894784 1648025856 (41196334226103 / 25000) (41199594040503 / 25000) := by
  exact
    packedTile65536 1647894784 1648025856 14 6144 40594 31 _ _ (84891 / 4000) (1061139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648025856 :
    ThetaLowerSegment 1648025856 1648156928 (41199594040503 / 25000) (20601415261039 / 12500) := by
  exact
    packedTile65536 1648025856 1648156928 14 6100 40595 31 _ _ (2122283 / 100000) (1061143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648156928 :
    ThetaLowerSegment 1648156928 1648288000 (20601415261039 / 12500) (8241222741251 / 5000) := by
  exact
    packedTile65536 1648156928 1648288000 14 6188 40597 31 _ _ (2122291 / 100000) (1061147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648288000 :
    ThetaLowerSegment 1648288000 1648419072 (8241222741251 / 5000) (164837657647099 / 100000) := by
  exact
    packedTile65536 1648288000 1648419072 14 6221 40599 31 _ _ (2122299 / 100000) (1061151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648419072 :
    ThetaLowerSegment 1648419072 1648550144 (164837657647099 / 100000)
      (82425370834877 / 50000) := by
  exact
    packedTile65536 1648419072 1648550144 14 6165 40600 31 _ _ (2122307 / 100000) (212231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648550144 :
    ThetaLowerSegment 1648550144 1648681216 (82425370834877 / 50000)
      (164863936102109 / 100000) := by
  exact
    packedTile65536 1648550144 1648681216 14 6217 40602 31 _ _ (424463 / 20000) (1061159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648681216 :
    ThetaLowerSegment 1648681216 1648812288 (164863936102109 / 100000)
      (164876890761701 / 100000) := by
  exact
    packedTile65536 1648681216 1648812288 14 6104 40603 31 _ _ (2122323 / 100000) (1061163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648812288 :
    ThetaLowerSegment 1648812288 1648943360 (164876890761701 / 100000)
      (82444989588489 / 50000) := by
  exact
    packedTile65536 1648812288 1648943360 14 6167 40605 31 _ _ (2122331 / 100000) (1061167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648943360 :
    ThetaLowerSegment 1648943360 1649074432 (82444989588489 / 50000)
      (164903105843693 / 100000) := by
  exact
    packedTile65536 1648943360 1649074432 14 6185 40607 31 _ _ (2122339 / 100000) (1061171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649074432 :
    ThetaLowerSegment 1649074432 1649205504 (164903105843693 / 100000)
      (82458160849231 / 50000) := by
  exact
    packedTile65536 1649074432 1649205504 14 6227 40608 31 _ _ (2122347 / 100000) (42447 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649205504 :
    ThetaLowerSegment 1649205504 1649336576 (82458160849231 / 50000) (8246466268071 / 5000) := by
  exact
    packedTile65536 1649205504 1649336576 14 6127 40610 31 _ _ (1061177 / 50000) (2122357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649336576 :
    ThetaLowerSegment 1649336576 1649467648 (8246466268071 / 5000) (82471196372127 / 50000) := by
  exact
    packedTile65536 1649336576 1649467648 14 6157 40612 31 _ _ (1061181 / 50000) (424473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649467648 :
    ThetaLowerSegment 1649467648 1649598720 (82471196372127 / 50000) (82477873348147 / 50000) := by
  exact
    packedTile65536 1649467648 1649598720 14 6292 40613 31 _ _ (212237 / 10000) (2122373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649598720 :
    ThetaLowerSegment 1649598720 1649729792 (82477873348147 / 50000) (5155275177754 / 3125) := by
  exact
    packedTile65536 1649598720 1649729792 14 6153 40615 31 _ _ (1061189 / 50000) (2122381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649729792 :
    ThetaLowerSegment 1649729792 1649860864 (5155275177754 / 3125) (41245453978577 / 25000) := by
  exact
    packedTile65536 1649729792 1649860864 14 6130 40616 31 _ _ (1061193 / 50000) (2122389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649860864 :
    ThetaLowerSegment 1649860864 1649991936 (41245453978577 / 25000) (5156088583722 / 3125) := by
  exact
    packedTile65536 1649860864 1649991936 14 6134 40618 31 _ _ (1061197 / 50000) (2122397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1649991936 :
    ThetaLowerSegment 1649991936 1650123008 (5156088583722 / 3125) (41252014310891 / 25000) := by
  exact
    packedTile65536 1649991936 1650123008 14 6230 40620 31 _ _ (1061201 / 50000) (424481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650123008 :
    ThetaLowerSegment 1650123008 1650254080 (41252014310891 / 25000) (41255267965421 / 25000) := by
  exact
    packedTile65536 1650123008 1650254080 14 6132 40621 31 _ _ (212241 / 10000) (2122413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650254080 :
    ThetaLowerSegment 1650254080 1650385152 (41255267965421 / 25000) (16503411836513 / 10000) := by
  exact
    packedTile65536 1650254080 1650385152 14 6147 40623 31 _ _ (1061209 / 50000) (2122421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650385152 :
    ThetaLowerSegment 1650385152 1650516224 (16503411836513 / 10000) (82523630213461 / 50000) := by
  exact
    packedTile65536 1650385152 1650516224 14 6192 40624 31 _ _ (1061213 / 50000) (2122429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650516224 :
    ThetaLowerSegment 1650516224 1650647296 (82523630213461 / 50000) (82530156698011 / 50000) := by
  exact
    packedTile65536 1650516224 1650647296 14 6150 40626 31 _ _ (1061217 / 50000) (2122437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650647296 :
    ThetaLowerSegment 1650647296 1650778368 (82530156698011 / 50000) (82536734145769 / 50000) := by
  exact
    packedTile65536 1650647296 1650778368 14 6198 40628 31 _ _ (1061221 / 50000) (424489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650778368 :
    ThetaLowerSegment 1650778368 1650909440 (82536734145769 / 50000) (41271663768347 / 25000) := by
  exact
    packedTile65536 1650778368 1650909440 14 6213 40629 31 _ _ (42449 / 2000) (2122453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650909440 :
    ThetaLowerSegment 1650909440 1651040512 (41271663768347 / 25000) (20637472013593 / 12500) := by
  exact
    packedTile65536 1650909440 1651040512 14 6182 40631 31 _ _ (1061229 / 50000) (2122461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651040512 :
    ThetaLowerSegment 1651040512 1651171584 (20637472013593 / 12500) (4127819989003 / 2500) := by
  exact
    packedTile65536 1651040512 1651171584 14 6136 40632 31 _ _ (1061233 / 50000) (2122469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651171584 :
    ThetaLowerSegment 1651171584 1651302656 (4127819989003 / 2500) (82562923203899 / 50000) := by
  exact
    packedTile65536 1651171584 1651302656 14 6147 40634 31 _ _ (1061237 / 50000) (2122477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651302656 :
    ThetaLowerSegment 1651302656 1651433728 (82562923203899 / 50000) (20642384479763 / 12500) := by
  exact
    packedTile65536 1651302656 1651433728 14 6233 40636 31 _ _ (1061241 / 50000) (424497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651433728 :
    ThetaLowerSegment 1651433728 1651564800 (20642384479763 / 12500)
      (165152067593273 / 100000) := by
  exact
    packedTile65536 1651433728 1651564800 14 6121 40637 31 _ _ (2122489 / 100000) (530623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651564800 :
    ThetaLowerSegment 1651564800 1651695872 (165152067593273 / 100000)
      (41291282890577 / 25000) := by
  exact
    packedTile65536 1651564800 1651695872 14 6155 40639 31 _ _ (2122497 / 100000) (849 / 40)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651695872 :
    ThetaLowerSegment 1651695872 1651826944 (41291282890577 / 25000) (82589083994009 / 50000) := by
  exact
    packedTile65536 1651695872 1651826944 14 6142 40641 31 _ _ (424501 / 20000) (530627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651826944 :
    ThetaLowerSegment 1651826944 1651958016 (82589083994009 / 50000)
      (165191316956053 / 100000) := by
  exact
    packedTile65536 1651826944 1651958016 14 6195 40642 31 _ _ (2122513 / 100000) (530629 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1651958016 :
    ThetaLowerSegment 1651958016 1652089088 (165191316956053 / 100000)
      (165204323764741 / 100000) := by
  exact
    packedTile65536 1651958016 1652089088 14 6128 40644 31 _ _ (2122521 / 100000) (530631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652089088 :
    ThetaLowerSegment 1652089088 1652220160 (165204323764741 / 100000)
      (41304361840387 / 25000) := by
  exact
    packedTile65536 1652089088 1652220160 14 6183 40645 31 _ _ (2122529 / 100000) (530633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652220160 :
    ThetaLowerSegment 1652220160 1652351232 (41304361840387 / 25000) (82615237746827 / 50000) := by
  exact
    packedTile65536 1652220160 1652351232 14 6138 40647 31 _ _ (2122537 / 100000) (106127 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652351232 :
    ThetaLowerSegment 1652351232 1652482304 (82615237746827 / 50000) (41310895021621 / 25000) := by
  exact
    packedTile65536 1652351232 1652482304 14 6174 40649 31 _ _ (424509 / 20000) (530637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652482304 :
    ThetaLowerSegment 1652482304 1652613376 (41310895021621 / 25000)
      (165256780243591 / 100000) := by
  exact
    packedTile65536 1652482304 1652613376 14 6219 40650 31 _ _ (2122553 / 100000) (530639 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652613376 :
    ThetaLowerSegment 1652613376 1652744448 (165256780243591 / 100000)
      (165269808523009 / 100000) := by
  exact
    packedTile65536 1652613376 1652744448 14 6138 40652 31 _ _ (2122561 / 100000) (530641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652744448 :
    ThetaLowerSegment 1652744448 1652875520 (165269808523009 / 100000)
      (165282824116117 / 100000) := by
  exact
    packedTile65536 1652744448 1652875520 14 6132 40653 31 _ _ (2122569 / 100000) (530643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1652875520 :
    ThetaLowerSegment 1652875520 1653006592 (165282824116117 / 100000)
      (20662000930233 / 12500) := by
  exact
    packedTile65536 1652875520 1653006592 14 6211 40655 31 _ _ (2122577 / 100000) (106129 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653006592 :
    ThetaLowerSegment 1653006592 1653137664 (20662000930233 / 12500)
      (165309029500839 / 100000) := by
  exact
    packedTile65536 1653006592 1653137664 14 6135 40657 31 _ _ (424517 / 20000) (530647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653137664 :
    ThetaLowerSegment 1653137664 1653268736 (165309029500839 / 100000) (3306440692563 / 2000) := by
  exact
    packedTile65536 1653137664 1653268736 14 6127 40658 31 _ _ (2122593 / 100000) (530649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653268736 :
    ThetaLowerSegment 1653268736 1653399808 (3306440692563 / 2000) (10333443569669 / 6250) := by
  exact
    packedTile65536 1653268736 1653399808 14 6154 40660 31 _ _ (2122601 / 100000) (530651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653399808 :
    ThetaLowerSegment 1653399808 1653530880 (10333443569669 / 6250) (5167132575814 / 3125) := by
  exact
    packedTile65536 1653399808 1653530880 14 6193 40662 31 _ _ (132663 / 6250) (2122611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653530880 :
    ThetaLowerSegment 1653530880 1653661952 (5167132575814 / 3125) (10335086338693 / 6250) := by
  exact
    packedTile65536 1653530880 1653661952 14 6190 40663 31 _ _ (265327 / 12500) (2122619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653661952 :
    ThetaLowerSegment 1653661952 1653793024 (10335086338693 / 6250) (2067178666761 / 1250) := by
  exact
    packedTile65536 1653661952 1653793024 14 6083 40665 31 _ _ (66332 / 3125) (2122627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653793024 :
    ThetaLowerSegment 1653793024 1653924096 (2067178666761 / 1250) (10336716915021 / 6250) := by
  exact
    packedTile65536 1653793024 1653924096 14 6208 40666 31 _ _ (265329 / 12500) (424527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1653924096 :
    ThetaLowerSegment 1653924096 1654055168 (10336716915021 / 6250) (10337532008781 / 6250) := by
  exact
    packedTile65536 1653924096 1654055168 14 6144 40668 31 _ _ (26533 / 1250) (2122643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654055168 :
    ThetaLowerSegment 1654055168 1654186240 (10337532008781 / 6250) (1033835161624 / 625) := by
  exact
    packedTile65536 1654055168 1654186240 14 6178 40670 31 _ _ (265331 / 12500) (2122651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654186240 :
    ThetaLowerSegment 1654186240 1654317312 (1033835161624 / 625) (5169583689737 / 3125) := by
  exact
    packedTile65536 1654186240 1654317312 14 6149 40671 31 _ _ (66333 / 3125) (2122659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654317312 :
    ThetaLowerSegment 1654317312 1654448384 (5169583689737 / 3125) (5169993363889 / 3125) := by
  exact
    packedTile65536 1654317312 1654448384 14 6176 40673 31 _ _ (265333 / 12500) (2122667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654448384 :
    ThetaLowerSegment 1654448384 1654579456 (5169993363889 / 3125) (10340803823831 / 6250) := by
  exact
    packedTile65536 1654448384 1654579456 14 6159 40674 31 _ _ (132667 / 6250) (84907 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654579456 :
    ThetaLowerSegment 1654579456 1654710528 (10340803823831 / 6250) (20683245029947 / 12500) := by
  exact
    packedTile65536 1654579456 1654710528 14 6171 40676 31 _ _ (53067 / 2500) (2122683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654710528 :
    ThetaLowerSegment 1654710528 1654841600 (20683245029947 / 12500) (20684858007491 / 12500) := by
  exact
    packedTile65536 1654710528 1654841600 14 6079 40678 31 _ _ (66334 / 3125) (2122691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654841600 :
    ThetaLowerSegment 1654841600 1654972672 (20684858007491 / 12500) (20686490891389 / 12500) := by
  exact
    packedTile65536 1654841600 1654972672 14 6154 40679 31 _ _ (265337 / 12500) (2122699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1654972672 :
    ThetaLowerSegment 1654972672 1655103744 (20686490891389 / 12500) (4137632875631 / 2500) := by
  exact
    packedTile65536 1654972672 1655103744 14 6307 40681 31 _ _ (132669 / 6250) (2122707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655103744 :
    ThetaLowerSegment 1655103744 1655234816 (4137632875631 / 2500) (20689807356469 / 12500) := by
  exact
    packedTile65536 1655103744 1655234816 14 6192 40682 31 _ _ (2122711 / 100000) (1061357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655234816 :
    ThetaLowerSegment 1655234816 1655365888 (20689807356469 / 12500) (6621266231831 / 4000) := by
  exact
    packedTile65536 1655234816 1655365888 14 6217 40684 31 _ _ (2122719 / 100000) (1061361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655365888 :
    ThetaLowerSegment 1655365888 1655496960 (6621266231831 / 4000) (20693065736197 / 12500) := by
  exact
    packedTile65536 1655365888 1655496960 14 6063 40686 31 _ _ (2122727 / 100000) (212273 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655496960 :
    ThetaLowerSegment 1655496960 1655628032 (20693065736197 / 12500) (41389398361559 / 25000) := by
  exact
    packedTile65536 1655496960 1655628032 14 6156 40687 31 _ _ (424547 / 20000) (1061369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655628032 :
    ThetaLowerSegment 1655628032 1655759104 (41389398361559 / 25000)
      (165570663174887 / 100000) := by
  exact
    packedTile65536 1655628032 1655759104 14 6157 40689 31 _ _ (2122743 / 100000) (1061373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655759104 :
    ThetaLowerSegment 1655759104 1655890176 (165570663174887 / 100000)
      (33116742769607 / 20000) := by
  exact
    packedTile65536 1655759104 1655890176 14 6148 40691 31 _ _ (2122751 / 100000) (1061377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655890176 :
    ThetaLowerSegment 1655890176 1656021248 (33116742769607 / 20000) (8279841094243 / 5000) := by
  exact
    packedTile65536 1655890176 1656021248 14 6175 40692 31 _ _ (2122759 / 100000) (1061381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656021248 :
    ThetaLowerSegment 1656021248 1656152320 (8279841094243 / 5000) (16560987690191 / 10000) := by
  exact
    packedTile65536 1656021248 1656152320 14 6150 40694 31 _ _ (2122767 / 100000) (212277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656152320 :
    ThetaLowerSegment 1656152320 1656283392 (16560987690191 / 10000) (33124620782587 / 20000) := by
  exact
    packedTile65536 1656152320 1656283392 14 6231 40695 31 _ _ (84911 / 4000) (1061389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656283392 :
    ThetaLowerSegment 1656283392 1656414464 (33124620782587 / 20000)
      (165636099590461 / 100000) := by
  exact
    packedTile65536 1656283392 1656414464 14 6122 40697 31 _ _ (2122783 / 100000) (1061393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656414464 :
    ThetaLowerSegment 1656414464 1656545536 (165636099590461 / 100000)
      (165649260894661 / 100000) := by
  exact
    packedTile65536 1656414464 1656545536 14 6200 40699 31 _ _ (2122791 / 100000) (1061397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656545536 :
    ThetaLowerSegment 1656545536 1656676608 (165649260894661 / 100000)
      (82831227045223 / 50000) := by
  exact
    packedTile65536 1656545536 1656676608 14 6215 40700 31 _ _ (2122799 / 100000) (1061401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656676608 :
    ThetaLowerSegment 1656676608 1656807680 (82831227045223 / 50000) (82837784392957 / 50000) := by
  exact
    packedTile65536 1656676608 1656807680 14 6178 40702 31 _ _ (1061403 / 50000) (2122809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656807680 :
    ThetaLowerSegment 1656807680 1656938752 (82837784392957 / 50000) (10355545241517 / 6250) := by
  exact
    packedTile65536 1656807680 1656938752 14 6197 40703 31 _ _ (1061407 / 50000) (2122817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1656938752 :
    ThetaLowerSegment 1656938752 1657069824 (10355545241517 / 6250) (8285093631187 / 5000) := by
  exact
    packedTile65536 1656938752 1657069824 14 6194 40705 31 _ _ (1061411 / 50000) (84913 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657069824 :
    ThetaLowerSegment 1657069824 1657200896 (8285093631187 / 5000) (16571501081861 / 10000) := by
  exact
    packedTile65536 1657069824 1657200896 14 6189 40707 31 _ _ (212283 / 10000) (2122833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657200896 :
    ThetaLowerSegment 1657200896 1657331968 (16571501081861 / 10000) (41432017098787 / 25000) := by
  exact
    packedTile65536 1657200896 1657331968 14 6151 40708 31 _ _ (1061419 / 50000) (2122841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657331968 :
    ThetaLowerSegment 1657331968 1657463040 (41432017098787 / 25000) (82870588484599 / 50000) := by
  exact
    packedTile65536 1657331968 1657463040 14 6175 40710 31 _ _ (1061423 / 50000) (2122849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657463040 :
    ThetaLowerSegment 1657463040 1657594112 (82870588484599 / 50000) (82877201174809 / 50000) := by
  exact
    packedTile65536 1657463040 1657594112 14 6230 40711 31 _ _ (1061427 / 50000) (2122857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657594112 :
    ThetaLowerSegment 1657594112 1657725184 (82877201174809 / 50000) (82883701378253 / 50000) := by
  exact
    packedTile65536 1657594112 1657725184 14 6124 40713 31 _ _ (1061431 / 50000) (424573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657725184 :
    ThetaLowerSegment 1657725184 1657856256 (82883701378253 / 50000) (5180641647108 / 3125) := by
  exact
    packedTile65536 1657725184 1657856256 14 6185 40715 31 _ _ (212287 / 10000) (2122873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657856256 :
    ThetaLowerSegment 1657856256 1657987328 (5180641647108 / 3125) (41448428944959 / 25000) := by
  exact
    packedTile65536 1657856256 1657987328 14 6210 40716 31 _ _ (1061439 / 50000) (2122881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1657987328 :
    ThetaLowerSegment 1657987328 1658118400 (41448428944959 / 25000) (8290333693799 / 5000) := by
  exact
    packedTile65536 1657987328 1658118400 14 6104 40718 31 _ _ (1061443 / 50000) (2122889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658118400 :
    ThetaLowerSegment 1658118400 1658249472 (8290333693799 / 5000) (82909911537611 / 50000) := by
  exact
    packedTile65536 1658118400 1658249472 14 6194 40720 31 _ _ (2122893 / 100000) (132681 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658249472 :
    ThetaLowerSegment 1658249472 1658380544 (82909911537611 / 50000) (41458219729093 / 25000) := by
  exact
    packedTile65536 1658249472 1658380544 14 6150 40721 31 _ _ (2122901 / 100000) (265363 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658380544 :
    ThetaLowerSegment 1658380544 1658511616 (41458219729093 / 25000) (33169245129051 / 20000) := by
  exact
    packedTile65536 1658380544 1658511616 14 6287 40723 31 _ _ (2122909 / 100000) (66341 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658511616 :
    ThetaLowerSegment 1658511616 1658642688 (33169245129051 / 20000) (41464826234223 / 25000) := by
  exact
    packedTile65536 1658511616 1658642688 14 6161 40724 31 _ _ (2122917 / 100000) (53073 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658642688 :
    ThetaLowerSegment 1658642688 1658773760 (41464826234223 / 25000)
      (165872409752917 / 100000) := by
  exact
    packedTile65536 1658642688 1658773760 14 6173 40726 31 _ _ (84917 / 4000) (132683 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658773760 :
    ThetaLowerSegment 1658773760 1658904832 (165872409752917 / 100000)
      (165885576183383 / 100000) := by
  exact
    packedTile65536 1658773760 1658904832 14 6202 40728 31 _ _ (2122933 / 100000) (265367 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1658904832 :
    ThetaLowerSegment 1658904832 1659035904 (165885576183383 / 100000)
      (82949427589669 / 50000) := by
  exact
    packedTile65536 1658904832 1659035904 14 6255 40729 31 _ _ (2122941 / 100000) (66342 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659035904 :
    ThetaLowerSegment 1659035904 1659166976 (82949427589669 / 50000)
      (165911883717351 / 100000) := by
  exact
    packedTile65536 1659035904 1659166976 14 6137 40731 31 _ _ (2122949 / 100000) (265369 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659166976 :
    ThetaLowerSegment 1659166976 1659298048 (165911883717351 / 100000)
      (82962432799703 / 50000) := by
  exact
    packedTile65536 1659166976 1659298048 14 6115 40732 31 _ _ (2122957 / 100000) (26537 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659298048 :
    ThetaLowerSegment 1659298048 1659429120 (82962432799703 / 50000) (41484484704469 / 25000) := by
  exact
    packedTile65536 1659298048 1659429120 14 6158 40734 31 _ _ (424593 / 20000) (265371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659429120 :
    ThetaLowerSegment 1659429120 1659560192 (41484484704469 / 25000) (41487736036087 / 25000) := by
  exact
    packedTile65536 1659429120 1659560192 14 6126 40736 31 _ _ (530743 / 25000) (84919 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659560192 :
    ThetaLowerSegment 1659560192 1659691264 (41487736036087 / 25000) (5186372560034 / 3125) := by
  exact
    packedTile65536 1659560192 1659691264 14 6113 40737 31 _ _ (106149 / 5000) (2122983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659691264 :
    ThetaLowerSegment 1659691264 1659822336 (5186372560034 / 3125) (41494237674611 / 25000) := by
  exact
    packedTile65536 1659691264 1659822336 14 6137 40739 31 _ _ (530747 / 25000) (2122991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659822336 :
    ThetaLowerSegment 1659822336 1659953408 (41494237674611 / 25000) (41497469936021 / 25000) := by
  exact
    packedTile65536 1659822336 1659953408 14 6090 40740 31 _ _ (530749 / 25000) (2122999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659953408 :
    ThetaLowerSegment 1659953408 1660084480 (41497469936021 / 25000) (41500755284711 / 25000) := by
  exact
    packedTile65536 1659953408 1660084480 14 6190 40742 31 _ _ (530751 / 25000) (2123007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660084480 :
    ThetaLowerSegment 1660084480 1660215552 (41500755284711 / 25000) (41504033215239 / 25000) := by
  exact
    packedTile65536 1660084480 1660215552 14 6176 40744 31 _ _ (530753 / 25000) (424603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660215552 :
    ThetaLowerSegment 1660215552 1660346624 (41504033215239 / 25000) (5188411970778 / 3125) := by
  exact
    packedTile65536 1660215552 1660346624 14 6147 40745 31 _ _ (106151 / 5000) (2123023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660346624 :
    ThetaLowerSegment 1660346624 1660477696 (5188411970778 / 3125) (41510602913091 / 25000) := by
  exact
    packedTile65536 1660346624 1660477696 14 6231 40747 31 _ _ (530757 / 25000) (2123031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660477696 :
    ThetaLowerSegment 1660477696 1660608768 (41510602913091 / 25000) (41513815066559 / 25000) := by
  exact
    packedTile65536 1660477696 1660608768 14 6052 40748 31 _ _ (530759 / 25000) (2123039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660608768 :
    ThetaLowerSegment 1660608768 1660739840 (41513815066559 / 25000) (20758568549829 / 12500) := by
  exact
    packedTile65536 1660608768 1660739840 14 6259 40750 31 _ _ (530761 / 25000) (2123047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660739840 :
    ThetaLowerSegment 1660739840 1660870912 (20758568549829 / 12500) (16608170706873 / 10000) := by
  exact
    packedTile65536 1660739840 1660870912 14 6198 40752 31 _ _ (2123051 / 100000) (1061527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1660870912 :
    ThetaLowerSegment 1660870912 1661001984 (16608170706873 / 10000) (83047452001737 / 50000) := by
  exact
    packedTile65536 1660870912 1661001984 14 6216 40753 31 _ _ (2123059 / 100000) (1061531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661001984 :
    ThetaLowerSegment 1661001984 1661133056 (83047452001737 / 50000) (41526981724113 / 25000) := by
  exact
    packedTile65536 1661001984 1661133056 14 6134 40755 31 _ _ (2123067 / 100000) (212307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661133056 :
    ThetaLowerSegment 1661133056 1661264128 (41526981724113 / 25000)
      (166121053869177 / 100000) := by
  exact
    packedTile65536 1661133056 1661264128 14 6183 40757 31 _ _ (84923 / 4000) (1061539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661264128 :
    ThetaLowerSegment 1661264128 1661395200 (166121053869177 / 100000)
      (83067052230189 / 50000) := by
  exact
    packedTile65536 1661264128 1661395200 14 6147 40758 31 _ _ (2123083 / 100000) (1061543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661395200 :
    ThetaLowerSegment 1661395200 1661526272 (83067052230189 / 50000)
      (166147121131299 / 100000) := by
  exact
    packedTile65536 1661395200 1661526272 14 6131 40760 31 _ _ (2123091 / 100000) (1061547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661526272 :
    ThetaLowerSegment 1661526272 1661657344 (166147121131299 / 100000)
      (83080117756911 / 50000) := by
  exact
    packedTile65536 1661526272 1661657344 14 6177 40761 31 _ _ (2123099 / 100000) (1061551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661657344 :
    ThetaLowerSegment 1661657344 1661788416 (83080117756911 / 50000) (83086707881039 / 50000) := by
  exact
    packedTile65536 1661657344 1661788416 14 6208 40763 31 _ _ (2123107 / 100000) (212311 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661788416 :
    ThetaLowerSegment 1661788416 1661919488 (83086707881039 / 50000) (10386652434343 / 6250) := by
  exact
    packedTile65536 1661788416 1661919488 14 6134 40765 31 _ _ (424623 / 20000) (1061559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1661919488 :
    ThetaLowerSegment 1661919488 1662050560 (10386652434343 / 6250) (20774934364821 / 12500) := by
  exact
    packedTile65536 1661919488 1662050560 14 6140 40766 31 _ _ (1061561 / 50000) (3397 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662050560 :
    ThetaLowerSegment 1662050560 1662181632 (20774934364821 / 12500) (83106360563319 / 50000) := by
  exact
    packedTile65536 1662050560 1662181632 14 6239 40768 31 _ _ (212313 / 10000) (2123133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662181632 :
    ThetaLowerSegment 1662181632 1662312704 (83106360563319 / 50000) (83112980507603 / 50000) := by
  exact
    packedTile65536 1662181632 1662312704 14 6236 40769 31 _ _ (1061569 / 50000) (2123141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662312704 :
    ThetaLowerSegment 1662312704 1662443776 (83112980507603 / 50000) (83119602599977 / 50000) := by
  exact
    packedTile65536 1662312704 1662443776 14 6238 40771 31 _ _ (1061573 / 50000) (2123149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662443776 :
    ThetaLowerSegment 1662443776 1662574848 (83119602599977 / 50000) (83126127052219 / 50000) := by
  exact
    packedTile65536 1662443776 1662574848 14 6146 40773 31 _ _ (1061577 / 50000) (2123157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662574848 :
    ThetaLowerSegment 1662574848 1662705920 (83126127052219 / 50000) (2078318809481 / 1250) := by
  exact
    packedTile65536 1662574848 1662705920 14 6241 40774 31 _ _ (1061581 / 50000) (424633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662705920 :
    ThetaLowerSegment 1662705920 1662836992 (2078318809481 / 1250) (16627852616009 / 10000) := by
  exact
    packedTile65536 1662705920 1662836992 14 6133 40776 31 _ _ (212317 / 10000) (2123173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662836992 :
    ThetaLowerSegment 1662836992 1662968064 (16627852616009 / 10000) (83145842808667 / 50000) := by
  exact
    packedTile65536 1662836992 1662968064 14 6198 40777 31 _ _ (1061589 / 50000) (2123181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1662968064 :
    ThetaLowerSegment 1662968064 1663099136 (83145842808667 / 50000)
      (166304660400869 / 100000) := by
  exact
    packedTile65536 1662968064 1663099136 14 6111 40779 31 _ _ (424637 / 20000) (530797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663099136 :
    ThetaLowerSegment 1663099136 1663230208 (166304660400869 / 100000)
      (166317853922171 / 100000) := by
  exact
    packedTile65536 1663099136 1663230208 14 6214 40781 31 _ _ (2123193 / 100000) (530799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663230208 :
    ThetaLowerSegment 1663230208 1663361280 (166317853922171 / 100000)
      (41582704016069 / 25000) := by
  exact
    packedTile65536 1663230208 1663361280 14 6105 40782 31 _ _ (2123201 / 100000) (530801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663361280 :
    ThetaLowerSegment 1663361280 1663492352 (41582704016069 / 25000) (83171979363993 / 50000) := by
  exact
    packedTile65536 1663361280 1663492352 14 6190 40784 31 _ _ (2123209 / 100000) (530803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663492352 :
    ThetaLowerSegment 1663492352 1663623424 (83171979363993 / 50000)
      (166357048360791 / 100000) := by
  exact
    packedTile65536 1663492352 1663623424 14 6165 40785 31 _ _ (2123217 / 100000) (106161 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663623424 :
    ThetaLowerSegment 1663623424 1663754496 (166357048360791 / 100000)
      (41592551496529 / 25000) := by
  exact
    packedTile65536 1663623424 1663754496 14 6197 40787 31 _ _ (84929 / 4000) (530807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663754496 :
    ThetaLowerSegment 1663754496 1663885568 (41592551496529 / 25000) (20797932931621 / 12500) := by
  exact
    packedTile65536 1663754496 1663885568 14 6244 40789 31 _ _ (2123233 / 100000) (530809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663885568 :
    ThetaLowerSegment 1663885568 1664016640 (20797932931621 / 12500)
      (166396447071683 / 100000) := by
  exact
    packedTile65536 1663885568 1664016640 14 6115 40790 31 _ _ (2123241 / 100000) (530811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664016640 :
    ThetaLowerSegment 1664016640 1664147712 (166396447071683 / 100000)
      (166409441355563 / 100000) := by
  exact
    packedTile65536 1664016640 1664147712 14 6120 40792 31 _ _ (2123249 / 100000) (530813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664147712 :
    ThetaLowerSegment 1664147712 1664278784 (166409441355563 / 100000) (6656898021803 / 4000) := by
  exact
    packedTile65536 1664147712 1664278784 14 6127 40793 31 _ _ (265407 / 12500) (2123259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664278784 :
    ThetaLowerSegment 1664278784 1664409856 (6656898021803 / 4000) (33287103846999 / 20000) := by
  exact
    packedTile65536 1664278784 1664409856 14 6155 40795 31 _ _ (66352 / 3125) (2123267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664409856 :
    ThetaLowerSegment 1664409856 1664540928 (33287103846999 / 20000)
      (166448585850883 / 100000) := by
  exact
    packedTile65536 1664409856 1664540928 14 6154 40797 31 _ _ (265409 / 12500) (84931 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664540928 :
    ThetaLowerSegment 1664540928 1664672000 (166448585850883 / 100000)
      (166461673748803 / 100000) := by
  exact
    packedTile65536 1664540928 1664672000 14 6164 40798 31 _ _ (26541 / 1250) (2123283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664672000 :
    ThetaLowerSegment 1664672000 1664803072 (166461673748803 / 100000)
      (166474695874107 / 100000) := by
  exact
    packedTile65536 1664672000 1664803072 14 6133 40800 31 _ _ (265411 / 12500) (2123291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664803072 :
    ThetaLowerSegment 1664803072 1664934144 (166474695874107 / 100000)
      (166487860309307 / 100000) := by
  exact
    packedTile65536 1664803072 1664934144 14 6200 40801 31 _ _ (66353 / 3125) (2123299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1664934144 :
    ThetaLowerSegment 1664934144 1665065216 (166487860309307 / 100000)
      (166501054520363 / 100000) := by
  exact
    packedTile65536 1664934144 1665065216 14 6214 40803 31 _ _ (265413 / 12500) (2123307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665065216 :
    ThetaLowerSegment 1665065216 1665196288 (166501054520363 / 100000)
      (166514187205083 / 100000) := by
  exact
    packedTile65536 1665065216 1665196288 14 6185 40805 31 _ _ (132707 / 6250) (424663 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665196288 :
    ThetaLowerSegment 1665196288 1665327360 (166514187205083 / 100000)
      (41631837414891 / 25000) := by
  exact
    packedTile65536 1665196288 1665327360 14 6199 40806 31 _ _ (2123319 / 100000) (1061661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665327360 :
    ThetaLowerSegment 1665327360 1665458432 (41631837414891 / 25000)
      (166540461203789 / 100000) := by
  exact
    packedTile65536 1665327360 1665458432 14 6175 40808 31 _ _ (2123327 / 100000) (212333 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665458432 :
    ThetaLowerSegment 1665458432 1665589504 (166540461203789 / 100000)
      (166553723554199 / 100000) := by
  exact
    packedTile65536 1665458432 1665589504 14 6246 40810 31 _ _ (424667 / 20000) (1061669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665589504 :
    ThetaLowerSegment 1665589504 1665720576 (166553723554199 / 100000)
      (41641727909393 / 25000) := by
  exact
    packedTile65536 1665589504 1665720576 14 6211 40811 31 _ _ (2123343 / 100000) (1061673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665720576 :
    ThetaLowerSegment 1665720576 1665851648 (41641727909393 / 25000) (33316046283679 / 20000) := by
  exact
    packedTile65536 1665720576 1665851648 14 6273 40813 31 _ _ (2123351 / 100000) (1061677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665851648 :
    ThetaLowerSegment 1665851648 1665982720 (33316046283679 / 20000)
      (166593260349219 / 100000) := by
  exact
    packedTile65536 1665851648 1665982720 14 6136 40814 31 _ _ (2123359 / 100000) (1061681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1665982720 :
    ThetaLowerSegment 1665982720 1666113792 (166593260349219 / 100000)
      (83303145726249 / 50000) := by
  exact
    packedTile65536 1665982720 1666113792 14 6137 40816 31 _ _ (2123367 / 100000) (212337 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666113792 :
    ThetaLowerSegment 1666113792 1666244864 (83303145726249 / 50000) (83309666607803 / 50000) := by
  exact
    packedTile65536 1666113792 1666244864 14 6142 40818 31 _ _ (1061687 / 50000) (2123377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666244864 :
    ThetaLowerSegment 1666244864 1666375936 (83309666607803 / 50000) (5207269217813 / 3125) := by
  exact
    packedTile65536 1666244864 1666375936 14 6255 40819 31 _ _ (1061691 / 50000) (424677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666375936 :
    ThetaLowerSegment 1666375936 1666507008 (5207269217813 / 3125) (5207673723608 / 3125) := by
  exact
    packedTile65536 1666375936 1666507008 14 6096 40821 31 _ _ (212339 / 10000) (2123393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666507008 :
    ThetaLowerSegment 1666507008 1666638080 (5207673723608 / 3125) (83329420504973 / 50000) := by
  exact
    packedTile65536 1666507008 1666638080 14 6255 40822 31 _ _ (1061699 / 50000) (2123401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666638080 :
    ThetaLowerSegment 1666638080 1666769152 (83329420504973 / 50000) (4166798507539 / 2500) := by
  exact
    packedTile65536 1666638080 1666769152 14 6169 40824 31 _ _ (1061703 / 50000) (2123409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666769152 :
    ThetaLowerSegment 1666769152 1666900224 (4166798507539 / 2500) (83342475229569 / 50000) := by
  exact
    packedTile65536 1666769152 1666900224 14 6127 40826 31 _ _ (1061707 / 50000) (2123417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1666900224 :
    ThetaLowerSegment 1666900224 1667031296 (83342475229569 / 50000) (41674483796167 / 25000) := by
  exact
    packedTile65536 1666900224 1667031296 14 6115 40827 31 _ _ (1061711 / 50000) (84937 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667031296 :
    ThetaLowerSegment 1667031296 1667162368 (41674483796167 / 25000) (41677777236097 / 25000) := by
  exact
    packedTile65536 1667031296 1667162368 14 6204 40829 31 _ _ (212343 / 10000) (2123433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667162368 :
    ThetaLowerSegment 1667162368 1667293440 (41677777236097 / 25000) (83362177472197 / 50000) := by
  exact
    packedTile65536 1667162368 1667293440 14 6238 40830 31 _ _ (2123437 / 100000) (26543 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667293440 :
    ThetaLowerSegment 1667293440 1667424512 (83362177472197 / 50000)
      (166737441735929 / 100000) := by
  exact
    packedTile65536 1667293440 1667424512 14 6163 40832 31 _ _ (424689 / 20000) (265431 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667424512 :
    ThetaLowerSegment 1667424512 1667555584 (166737441735929 / 100000)
      (166750433021383 / 100000) := by
  exact
    packedTile65536 1667424512 1667555584 14 6118 40834 31 _ _ (2123453 / 100000) (66358 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667555584 :
    ThetaLowerSegment 1667555584 1667686656 (166750433021383 / 100000) (10422716012981 / 6250) := by
  exact
    packedTile65536 1667555584 1667686656 14 6133 40835 31 _ _ (2123461 / 100000) (265433 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667686656 :
    ThetaLowerSegment 1667686656 1667817728 (10422716012981 / 6250) (166776534653267 / 100000) := by
  exact
    packedTile65536 1667686656 1667817728 14 6159 40837 31 _ _ (2123469 / 100000) (132717 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667817728 :
    ThetaLowerSegment 1667817728 1667948800 (166776534653267 / 100000)
      (166789742680207 / 100000) := by
  exact
    packedTile65536 1667817728 1667948800 14 6220 40838 31 _ _ (2123477 / 100000) (53087 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667948800 :
    ThetaLowerSegment 1667948800 1668079872 (166789742680207 / 100000)
      (166802882805387 / 100000) := by
  exact
    packedTile65536 1667948800 1668079872 14 6188 40840 31 _ _ (424697 / 20000) (66359 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668079872 :
    ThetaLowerSegment 1668079872 1668210944 (166802882805387 / 100000)
      (166815978380551 / 100000) := by
  exact
    packedTile65536 1668079872 1668210944 14 6167 40842 31 _ _ (530873 / 25000) (424699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668210944 :
    ThetaLowerSegment 1668210944 1668342016 (166815978380551 / 100000)
      (166829090993051 / 100000) := by
  exact
    packedTile65536 1668210944 1668342016 14 6175 40843 31 _ _ (4247 / 200) (2123503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668342016 :
    ThetaLowerSegment 1668342016 1668473088 (166829090993051 / 100000)
      (166842250372127 / 100000) := by
  exact
    packedTile65536 1668342016 1668473088 14 6197 40845 31 _ _ (530877 / 25000) (2123511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668473088 :
    ThetaLowerSegment 1668473088 1668604160 (166842250372127 / 100000)
      (33371048408603 / 20000) := by
  exact
    packedTile65536 1668473088 1668604160 14 6118 40846 31 _ _ (530879 / 25000) (2123519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668604160 :
    ThetaLowerSegment 1668604160 1668735232 (33371048408603 / 20000) (33373694319507 / 20000) := by
  exact
    packedTile65536 1668604160 1668735232 14 6230 40848 31 _ _ (530881 / 25000) (2123527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668735232 :
    ThetaLowerSegment 1668735232 1668866304 (33373694319507 / 20000)
      (166881333830859 / 100000) := by
  exact
    packedTile65536 1668735232 1668866304 14 6057 40850 31 _ _ (530883 / 25000) (424707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668866304 :
    ThetaLowerSegment 1668866304 1668997376 (166881333830859 / 100000)
      (166894355378139 / 100000) := by
  exact
    packedTile65536 1668866304 1668997376 14 6132 40851 31 _ _ (106177 / 5000) (2123543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1668997376 :
    ThetaLowerSegment 1668997376 1669128448 (166894355378139 / 100000) (5215860507324 / 3125) := by
  exact
    packedTile65536 1668997376 1669128448 14 6207 40853 31 _ _ (2123547 / 100000) (42471 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669128448 :
    ThetaLowerSegment 1669128448 1669259520 (5215860507324 / 3125) (166920555750073 / 100000) := by
  exact
    packedTile65536 1669128448 1669259520 14 6131 40854 31 _ _ (424711 / 20000) (1061779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669259520 :
    ThetaLowerSegment 1669259520 1669390592 (166920555750073 / 100000) (41733445856 / 25) := by
  exact
    packedTile65536 1669259520 1669390592 14 6229 40856 31 _ _ (2123563 / 100000) (1061783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669390592 :
    ThetaLowerSegment 1669390592 1669521664 (41733445856 / 25) (83473510882807 / 50000) := by
  exact
    packedTile65536 1669390592 1669521664 14 6234 40858 31 _ _ (2123571 / 100000) (1061787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669521664 :
    ThetaLowerSegment 1669521664 1669652736 (83473510882807 / 50000)
      (166960194326151 / 100000) := by
  exact
    packedTile65536 1669521664 1669652736 14 6203 40859 31 _ _ (2123579 / 100000) (1061791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669652736 :
    ThetaLowerSegment 1669652736 1669783808 (166960194326151 / 100000)
      (33394647479501 / 20000) := by
  exact
    packedTile65536 1669652736 1669783808 14 6142 40861 31 _ _ (2123587 / 100000) (212359 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669783808 :
    ThetaLowerSegment 1669783808 1669914880 (33394647479501 / 20000)
      (166986352714049 / 100000) := by
  exact
    packedTile65536 1669783808 1669914880 14 6176 40862 31 _ _ (1061797 / 50000) (2123597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1669914880 :
    ThetaLowerSegment 1669914880 1670045952 (166986352714049 / 100000)
      (166999266337811 / 100000) := by
  exact
    packedTile65536 1669914880 1670045952 14 6081 40864 31 _ _ (1061801 / 50000) (424721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670045952 :
    ThetaLowerSegment 1670045952 1670177024 (166999266337811 / 100000)
      (167012526158651 / 100000) := by
  exact
    packedTile65536 1670045952 1670177024 14 6244 40866 31 _ _ (212361 / 10000) (2123613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670177024 :
    ThetaLowerSegment 1670177024 1670308096 (167012526158651 / 100000)
      (167025531195283 / 100000) := by
  exact
    packedTile65536 1670177024 1670308096 14 6124 40867 31 _ _ (1061809 / 50000) (2123621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670308096 :
    ThetaLowerSegment 1670308096 1670439168 (167025531195283 / 100000)
      (167038619102321 / 100000) := by
  exact
    packedTile65536 1670308096 1670439168 14 6163 40869 31 _ _ (1061813 / 50000) (2123629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670439168 :
    ThetaLowerSegment 1670439168 1670570240 (167038619102321 / 100000)
      (167051794127657 / 100000) := by
  exact
    packedTile65536 1670439168 1670570240 14 6204 40871 31 _ _ (1061817 / 50000) (2123637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670570240 :
    ThetaLowerSegment 1670570240 1670701312 (167051794127657 / 100000)
      (167064816300401 / 100000) := by
  exact
    packedTile65536 1670570240 1670701312 14 6132 40872 31 _ _ (1061821 / 50000) (424729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670701312 :
    ThetaLowerSegment 1670701312 1670832384 (167064816300401 / 100000)
      (167077961687711 / 100000) := by
  exact
    packedTile65536 1670701312 1670832384 14 6190 40874 31 _ _ (2123649 / 100000) (530913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670832384 :
    ThetaLowerSegment 1670832384 1670963456 (167077961687711 / 100000)
      (167090890511527 / 100000) := by
  exact
    packedTile65536 1670832384 1670963456 14 6088 40875 31 _ _ (2123657 / 100000) (106183 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1670963456 :
    ThetaLowerSegment 1670963456 1671094528 (167090890511527 / 100000)
      (167104176159767 / 100000) := by
  exact
    packedTile65536 1670963456 1671094528 14 6256 40877 31 _ _ (424733 / 20000) (530917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671094528 :
    ThetaLowerSegment 1671094528 1671225600 (167104176159767 / 100000)
      (83558589704773 / 50000) := by
  exact
    packedTile65536 1671094528 1671225600 14 6123 40879 31 _ _ (2123673 / 100000) (530919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671225600 :
    ThetaLowerSegment 1671225600 1671356672 (83558589704773 / 50000) (83565181610597 / 50000) := by
  exact
    packedTile65536 1671225600 1671356672 14 6208 40880 31 _ _ (2123681 / 100000) (530921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671356672 :
    ThetaLowerSegment 1671356672 1671487744 (83565181610597 / 50000)
      (167143532216683 / 100000) := by
  exact
    packedTile65536 1671356672 1671487744 14 6201 40882 31 _ _ (2123689 / 100000) (530923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671487744 :
    ThetaLowerSegment 1671487744 1671618816 (167143532216683 / 100000)
      (33431338552159 / 20000) := by
  exact
    packedTile65536 1671487744 1671618816 14 6197 40883 31 _ _ (132731 / 6250) (2123699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671618816 :
    ThetaLowerSegment 1671618816 1671749888 (33431338552159 / 20000)
      (167169793890771 / 100000) := by
  exact
    packedTile65536 1671618816 1671749888 14 6169 40885 31 _ _ (265463 / 12500) (2123707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671749888 :
    ThetaLowerSegment 1671749888 1671880960 (167169793890771 / 100000)
      (167182778265939 / 100000) := by
  exact
    packedTile65536 1671749888 1671880960 14 6114 40887 31 _ _ (66366 / 3125) (424743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671880960 :
    ThetaLowerSegment 1671880960 1672012032 (167182778265939 / 100000)
      (167196110980099 / 100000) := by
  exact
    packedTile65536 1671880960 1672012032 14 6278 40888 31 _ _ (53093 / 2500) (2123723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672012032 :
    ThetaLowerSegment 1672012032 1672143104 (167196110980099 / 100000)
      (167209137927651 / 100000) := by
  exact
    packedTile65536 1672012032 1672143104 14 6134 40890 31 _ _ (132733 / 6250) (2123731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672143104 :
    ThetaLowerSegment 1672143104 1672274176 (167209137927651 / 100000)
      (167222243502507 / 100000) := by
  exact
    packedTile65536 1672143104 1672274176 14 6171 40891 31 _ _ (265467 / 12500) (2123739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672274176 :
    ThetaLowerSegment 1672274176 1672405248 (167222243502507 / 100000)
      (167235502036299 / 100000) := by
  exact
    packedTile65536 1672274176 1672405248 14 6243 40893 31 _ _ (66367 / 3125) (2123747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672405248 :
    ThetaLowerSegment 1672405248 1672536320 (167235502036299 / 100000)
      (167248669292499 / 100000) := by
  exact
    packedTile65536 1672405248 1672536320 14 6200 40895 31 _ _ (2123751 / 100000) (1061877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672536320 :
    ThetaLowerSegment 1672536320 1672667392 (167248669292499 / 100000)
      (83630834410669 / 50000) := by
  exact
    packedTile65536 1672536320 1672667392 14 6121 40896 31 _ _ (2123759 / 100000) (1061881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672667392 :
    ThetaLowerSegment 1672667392 1672798464 (83630834410669 / 50000) (20909365671869 / 12500) := by
  exact
    packedTile65536 1672667392 1672798464 14 6242 40898 31 _ _ (2123767 / 100000) (212377 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672798464 :
    ThetaLowerSegment 1672798464 1672929536 (20909365671869 / 12500)
      (167288026942927 / 100000) := by
  exact
    packedTile65536 1672798464 1672929536 14 6169 40899 31 _ _ (84951 / 4000) (1061889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1672929536 :
    ThetaLowerSegment 1672929536 1673060608 (167288026942927 / 100000)
      (83650500566637 / 50000) := by
  exact
    packedTile65536 1672929536 1673060608 14 6109 40901 31 _ _ (2123783 / 100000) (1061893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673060608 :
    ThetaLowerSegment 1673060608 1673191680 (83650500566637 / 50000) (33462808666761 / 20000) := by
  exact
    packedTile65536 1673060608 1673191680 14 6141 40903 31 _ _ (2123791 / 100000) (1061897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673191680 :
    ThetaLowerSegment 1673191680 1673322752 (33462808666761 / 20000) (6693081214343 / 4000) := by
  exact
    packedTile65536 1673191680 1673322752 14 6115 40904 31 _ _ (1061899 / 50000) (2123801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673322752 :
    ThetaLowerSegment 1673322752 1673339136 (6693081214343 / 4000) (167328682679643 / 100000) := by
  exact
    packedTile65536 1673322752 1673339136 11 778 40906 31 _ _ (1061903 / 50000) (2123809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1673339136 :
    ThetaLowerSegment 1673339136 1673341184 (167328682679643 / 100000)
      (167328895060343 / 100000) := by
  exact
    packedTile65536 1673339136 1673341184 8 100 40906 31 _ _ (2123807 / 100000) (212381 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1641341184_1673341184 :
    ThetaLowerSegment 1641341184 1673341184 (41032649277723 / 25000)
      (167328895060343 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1641341184 cell1641472256)
                  (ThetaLowerSegment.join cell1641603328 cell1641734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1641865472 cell1641996544)
                  (ThetaLowerSegment.join cell1642127616 cell1642258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1642389760 cell1642520832)
                  (ThetaLowerSegment.join cell1642651904 cell1642782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1642914048 cell1643045120)
                  (ThetaLowerSegment.join cell1643176192 cell1643307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1643438336 cell1643569408)
                  (ThetaLowerSegment.join cell1643700480 cell1643831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1643962624 cell1644093696)
                  (ThetaLowerSegment.join cell1644224768 cell1644355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1644486912 cell1644617984)
                  (ThetaLowerSegment.join cell1644749056 cell1644880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1645011200 cell1645142272)
                  (ThetaLowerSegment.join cell1645273344 cell1645404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1645535488 cell1645666560)
                  (ThetaLowerSegment.join cell1645797632 cell1645928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1646059776 cell1646190848)
                  (ThetaLowerSegment.join cell1646321920 cell1646452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1646584064 cell1646715136)
                  (ThetaLowerSegment.join cell1646846208 cell1646977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1647108352 cell1647239424)
                  (ThetaLowerSegment.join cell1647370496 cell1647501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1647632640 cell1647763712)
                  (ThetaLowerSegment.join cell1647894784 cell1648025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1648156928 cell1648288000)
                  (ThetaLowerSegment.join cell1648419072 cell1648550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1648681216 cell1648812288)
                  (ThetaLowerSegment.join cell1648943360 cell1649074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1649205504 cell1649336576)
                  (ThetaLowerSegment.join cell1649467648 cell1649598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1649729792 cell1649860864)
                  (ThetaLowerSegment.join cell1649991936 cell1650123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1650254080 cell1650385152)
                  (ThetaLowerSegment.join cell1650516224 cell1650647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1650778368 cell1650909440)
                  (ThetaLowerSegment.join cell1651040512 cell1651171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1651302656 cell1651433728)
                  (ThetaLowerSegment.join cell1651564800 cell1651695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1651826944 cell1651958016)
                  (ThetaLowerSegment.join cell1652089088 cell1652220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1652351232 cell1652482304)
                  (ThetaLowerSegment.join cell1652613376 cell1652744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1652875520 cell1653006592)
                  (ThetaLowerSegment.join cell1653137664 cell1653268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1653399808 cell1653530880)
                  (ThetaLowerSegment.join cell1653661952 cell1653793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1653924096 cell1654055168)
                  (ThetaLowerSegment.join cell1654186240 cell1654317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1654448384 cell1654579456)
                  (ThetaLowerSegment.join cell1654710528 cell1654841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1654972672 cell1655103744)
                  (ThetaLowerSegment.join cell1655234816 cell1655365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1655496960 cell1655628032)
                  (ThetaLowerSegment.join cell1655759104 cell1655890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1656021248 cell1656152320)
                  (ThetaLowerSegment.join cell1656283392 cell1656414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1656545536 cell1656676608)
                  (ThetaLowerSegment.join cell1656807680 cell1656938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1657069824 cell1657200896)
                  (ThetaLowerSegment.join cell1657331968 cell1657463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1657594112 cell1657725184)
                  (ThetaLowerSegment.join cell1657856256 cell1657987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1658118400 cell1658249472)
                  (ThetaLowerSegment.join cell1658380544 cell1658511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1658642688 cell1658773760)
                  (ThetaLowerSegment.join cell1658904832 cell1659035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1659166976 cell1659298048)
                  (ThetaLowerSegment.join cell1659429120 cell1659560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1659691264 cell1659822336)
                  (ThetaLowerSegment.join cell1659953408 cell1660084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1660215552 cell1660346624)
                  (ThetaLowerSegment.join cell1660477696 cell1660608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1660739840 cell1660870912)
                  (ThetaLowerSegment.join cell1661001984 cell1661133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1661264128 cell1661395200)
                  (ThetaLowerSegment.join cell1661526272 cell1661657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1661788416 cell1661919488)
                  (ThetaLowerSegment.join cell1662050560 cell1662181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1662312704 cell1662443776)
                  (ThetaLowerSegment.join cell1662574848 cell1662705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1662836992 cell1662968064)
                  (ThetaLowerSegment.join cell1663099136 cell1663230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1663361280 cell1663492352)
                  (ThetaLowerSegment.join cell1663623424 cell1663754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1663885568 cell1664016640)
                  (ThetaLowerSegment.join cell1664147712 cell1664278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1664409856 cell1664540928)
                  (ThetaLowerSegment.join cell1664672000 cell1664803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1664934144 cell1665065216)
                  (ThetaLowerSegment.join cell1665196288 cell1665327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1665458432 cell1665589504)
                  (ThetaLowerSegment.join cell1665720576 cell1665851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1665982720 cell1666113792)
                  (ThetaLowerSegment.join cell1666244864 cell1666375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1666507008 cell1666638080)
                  (ThetaLowerSegment.join cell1666769152 cell1666900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1667031296 cell1667162368)
                  (ThetaLowerSegment.join cell1667293440 cell1667424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1667555584 cell1667686656)
                  (ThetaLowerSegment.join cell1667817728 cell1667948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1668079872 cell1668210944)
                  (ThetaLowerSegment.join cell1668342016 cell1668473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1668604160 cell1668735232)
                  (ThetaLowerSegment.join cell1668866304 cell1668997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1669128448 cell1669259520)
                  (ThetaLowerSegment.join cell1669390592 cell1669521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1669652736 cell1669783808)
                  (ThetaLowerSegment.join cell1669914880 cell1670045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1670177024 cell1670308096)
                  (ThetaLowerSegment.join cell1670439168 cell1670570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1670701312 cell1670832384)
                  (ThetaLowerSegment.join cell1670963456 cell1671094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1671225600 cell1671356672)
                  (ThetaLowerSegment.join cell1671487744 cell1671618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1671749888 cell1671880960)
                  (ThetaLowerSegment.join cell1672012032 cell1672143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1672274176 cell1672405248)
                  (ThetaLowerSegment.join cell1672536320 cell1672667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1672798464 cell1672929536)
                (ThetaLowerSegment.join cell1673060608 cell1673191680))
              (ThetaLowerSegment.join cell1673322752 cell1673339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
