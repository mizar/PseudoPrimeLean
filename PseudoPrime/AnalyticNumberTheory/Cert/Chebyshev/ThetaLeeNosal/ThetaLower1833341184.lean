/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1833341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1801341184 :
    ThetaLowerSegment 1801341184 1801472256 (180130263237107 / 100000)
      (180143519164267 / 100000) := by
  exact
    packedTile65536 1801341184 1801472256 14 6220 42442 31 _ _ (1065589 / 50000) (2131181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801472256 :
    ThetaLowerSegment 1801472256 1801603328 (180143519164267 / 100000)
      (36031339257461 / 20000) := by
  exact
    packedTile65536 1801472256 1801603328 14 6183 42443 31 _ _ (1065593 / 50000) (2131189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801603328 :
    ThetaLowerSegment 1801603328 1801734400 (36031339257461 / 20000)
      (180169709351763 / 100000) := by
  exact
    packedTile65536 1801603328 1801734400 14 6106 42445 31 _ _ (2131193 / 100000) (532799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801734400 :
    ThetaLowerSegment 1801734400 1801865472 (180169709351763 / 100000)
      (180182816231763 / 100000) := by
  exact
    packedTile65536 1801734400 1801865472 14 6150 42446 31 _ _ (2664 / 125) (2131203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801865472 :
    ThetaLowerSegment 1801865472 1801996544 (180182816231763 / 100000)
      (36039182925997 / 20000) := by
  exact
    packedTile65536 1801865472 1801996544 14 6146 42448 31 _ _ (2131207 / 100000) (213121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1801996544 :
    ThetaLowerSegment 1801996544 1802127616 (36039182925997 / 20000) (7208363933039 / 4000) := by
  exact
    packedTile65536 1801996544 1802127616 14 6186 42449 31 _ _ (426243 / 20000) (1065609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802127616 :
    ThetaLowerSegment 1802127616 1802258688 (7208363933039 / 4000) (180222083861621 / 100000) := by
  exact
    packedTile65536 1802127616 1802258688 14 6093 42451 31 _ _ (1065611 / 50000) (85249 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802258688 :
    ThetaLowerSegment 1802258688 1802389760 (180222083861621 / 100000)
      (36047010904263 / 20000) := by
  exact
    packedTile65536 1802258688 1802389760 14 6086 42453 31 _ _ (2131229 / 100000) (66601 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802389760 :
    ThetaLowerSegment 1802389760 1802520832 (36047010904263 / 20000)
      (180248327859123 / 100000) := by
  exact
    packedTile65536 1802389760 1802520832 14 6228 42454 31 _ _ (532809 / 25000) (2131239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802520832 :
    ThetaLowerSegment 1802520832 1802651904 (180248327859123 / 100000)
      (36052305330643 / 20000) := by
  exact
    packedTile65536 1802520832 1802651904 14 6193 42456 31 _ _ (532811 / 25000) (2131247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802651904 :
    ThetaLowerSegment 1802651904 1802782976 (36052305330643 / 20000) (45068624894513 / 25000) := by
  exact
    packedTile65536 1802651904 1802782976 14 6087 42457 31 _ _ (2131251 / 100000) (1065627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802782976 :
    ThetaLowerSegment 1802782976 1802914048 (45068624894513 / 25000) (45071900638059 / 25000) := by
  exact
    packedTile65536 1802782976 1802914048 14 6148 42459 31 _ _ (1065629 / 50000) (2131261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1802914048 :
    ThetaLowerSegment 1802914048 1803045120 (45071900638059 / 25000) (3606013301631 / 2000) := by
  exact
    packedTile65536 1802914048 1803045120 14 6129 42460 31 _ _ (1065633 / 50000) (2131269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803045120 :
    ThetaLowerSegment 1803045120 1803176192 (3606013301631 / 2000) (180313770279227 / 100000) := by
  exact
    packedTile65536 1803045120 1803176192 14 6149 42462 31 _ _ (2131273 / 100000) (532819 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803176192 :
    ThetaLowerSegment 1803176192 1803307264 (180313770279227 / 100000)
      (180326928801947 / 100000) := by
  exact
    packedTile65536 1803176192 1803307264 14 6174 42463 31 _ _ (26641 / 1250) (2131283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803307264 :
    ThetaLowerSegment 1803307264 1803438336 (180326928801947 / 100000)
      (22542493071457 / 12500) := by
  exact
    packedTile65536 1803307264 1803438336 14 6107 42465 31 _ _ (2131287 / 100000) (213129 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803438336 :
    ThetaLowerSegment 1803438336 1803569408 (22542493071457 / 12500) (45088249155559 / 25000) := by
  exact
    packedTile65536 1803438336 1803569408 14 6124 42466 31 _ _ (426259 / 20000) (1065649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803569408 :
    ThetaLowerSegment 1803569408 1803700480 (45088249155559 / 25000) (45091542017149 / 25000) := by
  exact
    packedTile65536 1803569408 1803700480 14 6180 42468 31 _ _ (1065651 / 50000) (426261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803700480 :
    ThetaLowerSegment 1803700480 1803831552 (45091542017149 / 25000) (90189603708529 / 50000) := by
  exact
    packedTile65536 1803700480 1803831552 14 6118 42469 31 _ _ (2131309 / 100000) (133207 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803831552 :
    ThetaLowerSegment 1803831552 1803962624 (90189603708529 / 50000) (90196187343653 / 50000) := by
  exact
    packedTile65536 1803831552 1803962624 14 6178 42471 31 _ _ (532829 / 25000) (2131319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1803962624 :
    ThetaLowerSegment 1803962624 1804093696 (90196187343653 / 50000) (90202756084221 / 50000) := by
  exact
    packedTile65536 1803962624 1804093696 14 6164 42473 31 _ _ (532831 / 25000) (2131327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804093696 :
    ThetaLowerSegment 1804093696 1804224768 (90202756084221 / 50000) (45104667751509 / 25000) := by
  exact
    packedTile65536 1804093696 1804224768 14 6174 42474 31 _ _ (2131331 / 100000) (1065667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804224768 :
    ThetaLowerSegment 1804224768 1804355840 (45104667751509 / 25000) (9021592986279 / 5000) := by
  exact
    packedTile65536 1804224768 1804355840 14 6188 42476 31 _ _ (1065669 / 50000) (2131341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804355840 :
    ThetaLowerSegment 1804355840 1804486912 (9021592986279 / 5000) (7217792817381 / 4000) := by
  exact
    packedTile65536 1804355840 1804486912 14 6081 42477 31 _ _ (426269 / 20000) (532837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804486912 :
    ThetaLowerSegment 1804486912 1804617984 (7217792817381 / 4000) (180458064662067 / 100000) := by
  exact
    packedTile65536 1804486912 1804617984 14 6214 42479 31 _ _ (2131353 / 100000) (532839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804617984 :
    ThetaLowerSegment 1804617984 1804749056 (180458064662067 / 100000)
      (180471040381747 / 100000) := by
  exact
    packedTile65536 1804617984 1804749056 14 6088 42480 31 _ _ (13321 / 625) (2131363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804749056 :
    ThetaLowerSegment 1804749056 1804880128 (180471040381747 / 100000)
      (45121029079573 / 25000) := by
  exact
    packedTile65536 1804749056 1804880128 14 6135 42482 31 _ _ (2131367 / 100000) (213137 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804880128 :
    ThetaLowerSegment 1804880128 1805011200 (45121029079573 / 25000) (45124307134323 / 25000) := by
  exact
    packedTile65536 1804880128 1805011200 14 6152 42483 31 _ _ (17051 / 800) (1065689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805011200 :
    ThetaLowerSegment 1805011200 1805142272 (45124307134323 / 25000) (90255130969111 / 50000) := by
  exact
    packedTile65536 1805011200 1805142272 14 6115 42485 31 _ _ (1065691 / 50000) (426277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805142272 :
    ThetaLowerSegment 1805142272 1805273344 (90255130969111 / 50000) (45130799867363 / 25000) := by
  exact
    packedTile65536 1805142272 1805273344 14 6070 42486 31 _ _ (2131389 / 100000) (66606 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805273344 :
    ThetaLowerSegment 1805273344 1805404416 (45130799867363 / 25000) (22567026988103 / 12500) := by
  exact
    packedTile65536 1805273344 1805404416 14 6107 42488 31 _ _ (532849 / 25000) (2131399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805404416 :
    ThetaLowerSegment 1805404416 1805535488 (22567026988103 / 12500) (4513735978381 / 2500) := by
  exact
    packedTile65536 1805404416 1805535488 14 6204 42490 31 _ _ (532851 / 25000) (2131407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805535488 :
    ThetaLowerSegment 1805535488 1805666560 (4513735978381 / 2500) (180562523867369 / 100000) := by
  exact
    packedTile65536 1805535488 1805666560 14 6139 42491 31 _ _ (2131411 / 100000) (1065707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805666560 :
    ThetaLowerSegment 1805666560 1805797632 (180562523867369 / 100000)
      (180575664059339 / 100000) := by
  exact
    packedTile65536 1805666560 1805797632 14 6165 42493 31 _ _ (1065709 / 50000) (2131421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805797632 :
    ThetaLowerSegment 1805797632 1805928704 (180575664059339 / 100000)
      (180588891682889 / 100000) := by
  exact
    packedTile65536 1805797632 1805928704 14 6206 42494 31 _ _ (85257 / 4000) (532857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1805928704 :
    ThetaLowerSegment 1805928704 1806059776 (180588891682889 / 100000)
      (180602059675963 / 100000) := by
  exact
    packedTile65536 1805928704 1806059776 14 6178 42496 31 _ _ (2131433 / 100000) (532859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806059776 :
    ThetaLowerSegment 1806059776 1806190848 (180602059675963 / 100000)
      (180615089168683 / 100000) := by
  exact
    packedTile65536 1806059776 1806190848 14 6113 42497 31 _ _ (26643 / 1250) (2131443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806190848 :
    ThetaLowerSegment 1806190848 1806321920 (180615089168683 / 100000)
      (90314127558401 / 50000) := by
  exact
    packedTile65536 1806190848 1806321920 14 6177 42499 31 _ _ (2131447 / 100000) (42629 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806321920 :
    ThetaLowerSegment 1806321920 1806452992 (90314127558401 / 50000) (90320645544733 / 50000) := by
  exact
    packedTile65536 1806321920 1806452992 14 6116 42500 31 _ _ (1065727 / 50000) (2131457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806452992 :
    ThetaLowerSegment 1806452992 1806584064 (90320645544733 / 50000) (18065440384369 / 10000) := by
  exact
    packedTile65536 1806452992 1806584064 14 6152 42502 31 _ _ (1065731 / 50000) (426293 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806584064 :
    ThetaLowerSegment 1806584064 1806715136 (18065440384369 / 10000) (22583443310193 / 12500) := by
  exact
    packedTile65536 1806584064 1806715136 14 6166 42503 31 _ _ (2131469 / 100000) (133217 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806715136 :
    ThetaLowerSegment 1806715136 1806846208 (22583443310193 / 12500) (22585069626381 / 12500) := by
  exact
    packedTile65536 1806715136 1806846208 14 6104 42505 31 _ _ (532869 / 25000) (2131479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806846208 :
    ThetaLowerSegment 1806846208 1806977280 (22585069626381 / 12500) (36138711385173 / 20000) := by
  exact
    packedTile65536 1806846208 1806977280 14 6099 42507 31 _ _ (2131483 / 100000) (1065743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1806977280 :
    ThetaLowerSegment 1806977280 1807108352 (36138711385173 / 20000) (90353350915431 / 50000) := by
  exact
    packedTile65536 1806977280 1807108352 14 6167 42508 31 _ _ (2131491 / 100000) (1065747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807108352 :
    ThetaLowerSegment 1807108352 1807239424 (90353350915431 / 50000) (18071990859247 / 10000) := by
  exact
    packedTile65536 1807108352 1807239424 14 6196 42510 31 _ _ (1065749 / 50000) (2131501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807239424 :
    ThetaLowerSegment 1807239424 1807370496 (18071990859247 / 10000) (36146564676253 / 20000) := by
  exact
    packedTile65536 1807239424 1807370496 14 6059 42511 31 _ _ (426301 / 20000) (532877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807370496 :
    ThetaLowerSegment 1807370496 1807501568 (36146564676253 / 20000)
      (180746083517417 / 100000) := by
  exact
    packedTile65536 1807370496 1807501568 14 6221 42513 31 _ _ (266439 / 12500) (426303 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807501568 :
    ThetaLowerSegment 1807501568 1807632640 (180746083517417 / 100000)
      (180759243521897 / 100000) := by
  exact
    packedTile65536 1807501568 1807632640 14 6174 42514 31 _ _ (13322 / 625) (2131523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807632640 :
    ThetaLowerSegment 1807632640 1807763712 (180759243521897 / 100000)
      (90386245481101 / 50000) := by
  exact
    packedTile65536 1807632640 1807763712 14 6215 42516 31 _ _ (2131527 / 100000) (213153 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807763712 :
    ThetaLowerSegment 1807763712 1807894784 (90386245481101 / 50000) (90392729607529 / 50000) := by
  exact
    packedTile65536 1807763712 1807894784 14 6084 42517 31 _ _ (1065767 / 50000) (2131537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1807894784 :
    ThetaLowerSegment 1807894784 1808025856 (90392729607529 / 50000)
      (180798450957453 / 100000) := by
  exact
    packedTile65536 1807894784 1808025856 14 6095 42519 31 _ _ (2131541 / 100000) (266443 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808025856 :
    ThetaLowerSegment 1808025856 1808156928 (180798450957453 / 100000)
      (18081165164041 / 10000) := by
  exact
    packedTile65536 1808025856 1808156928 14 6193 42520 31 _ _ (2131549 / 100000) (66611 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808156928 :
    ThetaLowerSegment 1808156928 1808288000 (18081165164041 / 10000) (90412378223349 / 50000) := by
  exact
    packedTile65536 1808156928 1808288000 14 6148 42522 31 _ _ (532889 / 25000) (2131559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808288000 :
    ThetaLowerSegment 1808288000 1808419072 (90412378223349 / 50000) (36167576948643 / 20000) := by
  exact
    packedTile65536 1808288000 1808419072 14 6159 42523 31 _ _ (2131563 / 100000) (1065783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808419072 :
    ThetaLowerSegment 1808419072 1808550144 (36167576948643 / 20000) (36170203469197 / 20000) := by
  exact
    packedTile65536 1808419072 1808550144 14 6161 42525 31 _ _ (213157 / 10000) (2131573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808550144 :
    ThetaLowerSegment 1808550144 1808681216 (36170203469197 / 20000)
      (180864045550721 / 100000) := by
  exact
    packedTile65536 1808550144 1808681216 14 6112 42527 31 _ _ (1065789 / 50000) (2131581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808681216 :
    ThetaLowerSegment 1808681216 1808812288 (180864045550721 / 100000)
      (45219325469459 / 25000) := by
  exact
    packedTile65536 1808681216 1808812288 14 6219 42528 31 _ _ (426317 / 20000) (532897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808812288 :
    ThetaLowerSegment 1808812288 1808943360 (45219325469459 / 25000) (361781001391 / 200) := by
  exact
    packedTile65536 1808812288 1808943360 14 6192 42530 31 _ _ (266449 / 12500) (426319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808943360 :
    ThetaLowerSegment 1808943360 1809074432 (361781001391 / 200) (180903394737851 / 100000) := by
  exact
    packedTile65536 1808943360 1809074432 14 6049 42531 31 _ _ (2131599 / 100000) (1065801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809074432 :
    ThetaLowerSegment 1809074432 1809205504 (180903394737851 / 100000)
      (45229143615983 / 25000) := by
  exact
    packedTile65536 1809074432 1809205504 14 6183 42533 31 _ _ (2131607 / 100000) (213161 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809205504 :
    ThetaLowerSegment 1809205504 1809336576 (45229143615983 / 25000) (452324806577 / 250) := by
  exact
    packedTile65536 1809205504 1809336576 14 6262 42534 31 _ _ (1065807 / 50000) (2131617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809336576 :
    ThetaLowerSegment 1809336576 1809467648 (452324806577 / 250) (90471477680797 / 50000) := by
  exact
    packedTile65536 1809336576 1809467648 14 6114 42536 31 _ _ (2131621 / 100000) (266453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809467648 :
    ThetaLowerSegment 1809467648 1809598720 (90471477680797 / 50000) (90478086793411 / 50000) := by
  exact
    packedTile65536 1809467648 1809598720 14 6201 42537 31 _ _ (532907 / 25000) (2131631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809598720 :
    ThetaLowerSegment 1809598720 1809729792 (90478086793411 / 50000) (18096925756859 / 10000) := by
  exact
    packedTile65536 1809598720 1809729792 14 6138 42539 31 _ _ (532909 / 25000) (2131639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809729792 :
    ThetaLowerSegment 1809729792 1809860864 (18096925756859 / 10000)
      (180982198773243 / 100000) := by
  exact
    packedTile65536 1809729792 1809860864 14 6071 42540 31 _ _ (2131643 / 100000) (1065823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809860864 :
    ThetaLowerSegment 1809860864 1809991936 (180982198773243 / 100000)
      (180995331868893 / 100000) := by
  exact
    packedTile65536 1809860864 1809991936 14 6161 42542 31 _ _ (42633 / 2000) (2131653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1809991936 :
    ThetaLowerSegment 1809991936 1810123008 (180995331868893 / 100000)
      (90504300716859 / 50000) := by
  exact
    packedTile65536 1809991936 1810123008 14 6225 42544 31 _ _ (2131657 / 100000) (106583 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810123008 :
    ThetaLowerSegment 1810123008 1810254080 (90504300716859 / 50000) (90510763925139 / 50000) := by
  exact
    packedTile65536 1810123008 1810254080 14 6064 42545 31 _ _ (426333 / 20000) (532917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810254080 :
    ThetaLowerSegment 1810254080 1810385152 (90510763925139 / 50000) (90517324145719 / 50000) := by
  exact
    packedTile65536 1810254080 1810385152 14 6155 42547 31 _ _ (266459 / 12500) (85267 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810385152 :
    ThetaLowerSegment 1810385152 1810516224 (90517324145719 / 50000) (90523932350619 / 50000) := by
  exact
    packedTile65536 1810385152 1810516224 14 6200 42548 31 _ _ (2131679 / 100000) (1065841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810516224 :
    ThetaLowerSegment 1810516224 1810647296 (90523932350619 / 50000) (45265260163101 / 25000) := by
  exact
    packedTile65536 1810516224 1810647296 14 6181 42550 31 _ _ (1065843 / 50000) (2131689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810647296 :
    ThetaLowerSegment 1810647296 1810778368 (45265260163101 / 25000) (45268536576779 / 25000) := by
  exact
    packedTile65536 1810647296 1810778368 14 6148 42551 31 _ _ (1065847 / 50000) (2131697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810778368 :
    ThetaLowerSegment 1810778368 1810909440 (45268536576779 / 25000) (90543521549083 / 50000) := by
  exact
    packedTile65536 1810778368 1810909440 14 6050 42553 31 _ _ (2131701 / 100000) (266463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1810909440 :
    ThetaLowerSegment 1810909440 1811040512 (90543521549083 / 50000) (3622000845071 / 2000) := by
  exact
    packedTile65536 1810909440 1811040512 14 6098 42554 31 _ _ (532927 / 25000) (2131711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811040512 :
    ThetaLowerSegment 1811040512 1811171584 (3622000845071 / 2000) (7244520549573 / 4000) := by
  exact
    packedTile65536 1811040512 1811171584 14 6085 42556 31 _ _ (426343 / 20000) (1065859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811171584 :
    ThetaLowerSegment 1811171584 1811302656 (7244520549573 / 4000) (181126111039293 / 100000) := by
  exact
    packedTile65536 1811171584 1811302656 14 6144 42557 31 _ _ (1065861 / 50000) (85269 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811302656 :
    ThetaLowerSegment 1811302656 1811433728 (181126111039293 / 100000)
      (181139308579723 / 100000) := by
  exact
    packedTile65536 1811302656 1811433728 14 6191 42559 31 _ _ (213173 / 10000) (2131733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811433728 :
    ThetaLowerSegment 1811433728 1811564800 (181139308579723 / 100000)
      (36230499100961 / 20000) := by
  exact
    packedTile65536 1811433728 1811564800 14 6186 42560 31 _ _ (2131737 / 100000) (106587 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811564800 :
    ThetaLowerSegment 1811564800 1811695872 (36230499100961 / 20000) (36233108355617 / 20000) := by
  exact
    packedTile65536 1811564800 1811695872 14 6120 42562 31 _ _ (66617 / 3125) (2131747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811695872 :
    ThetaLowerSegment 1811695872 1811826944 (36233108355617 / 20000)
      (181178455925643 / 100000) := by
  exact
    packedTile65536 1811695872 1811826944 14 6058 42564 31 _ _ (2131751 / 100000) (1065877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811826944 :
    ThetaLowerSegment 1811826944 1811958016 (181178455925643 / 100000)
      (181191651513853 / 100000) := by
  exact
    packedTile65536 1811826944 1811958016 14 6190 42565 31 _ _ (2131759 / 100000) (1065881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1811958016 :
    ThetaLowerSegment 1811958016 1812089088 (181191651513853 / 100000)
      (181204896176011 / 100000) := by
  exact
    packedTile65536 1811958016 1812089088 14 6213 42567 31 _ _ (1065883 / 50000) (2131769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812089088 :
    ThetaLowerSegment 1812089088 1812220160 (181204896176011 / 100000)
      (90608936139131 / 50000) := by
  exact
    packedTile65536 1812089088 1812220160 14 6087 42568 31 _ _ (2131773 / 100000) (66618 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812220160 :
    ThetaLowerSegment 1812220160 1812351232 (90608936139131 / 50000) (90615496692081 / 50000) := by
  exact
    packedTile65536 1812220160 1812351232 14 6155 42570 31 _ _ (106589 / 5000) (2131783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812351232 :
    ThetaLowerSegment 1812351232 1812482304 (90615496692081 / 50000) (18124420194261 / 10000) := by
  exact
    packedTile65536 1812351232 1812482304 14 6196 42571 31 _ _ (532947 / 25000) (2131791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812482304 :
    ThetaLowerSegment 1812482304 1812613376 (18124420194261 / 10000) (36251443310217 / 20000) := by
  exact
    packedTile65536 1812482304 1812613376 14 6105 42573 31 _ _ (426359 / 20000) (1065899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812613376 :
    ThetaLowerSegment 1812613376 1812744448 (36251443310217 / 20000)
      (181270397482851 / 100000) := by
  exact
    packedTile65536 1812613376 1812744448 14 6183 42574 31 _ _ (1065901 / 50000) (426361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812744448 :
    ThetaLowerSegment 1812744448 1812875520 (181270397482851 / 100000)
      (45320908471233 / 25000) := by
  exact
    packedTile65536 1812744448 1812875520 14 6209 42576 31 _ _ (2131809 / 100000) (532953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812875520 :
    ThetaLowerSegment 1812875520 1813006592 (45320908471233 / 25000)
      (181296887391221 / 100000) := by
  exact
    packedTile65536 1812875520 1813006592 14 6217 42577 31 _ _ (2131817 / 100000) (106591 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813006592 :
    ThetaLowerSegment 1813006592 1813137664 (181296887391221 / 100000)
      (181309878726677 / 100000) := by
  exact
    packedTile65536 1813006592 1813137664 14 6094 42579 31 _ _ (133239 / 6250) (2131827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813137664 :
    ThetaLowerSegment 1813137664 1813268736 (181309878726677 / 100000)
      (90661431854649 / 50000) := by
  exact
    packedTile65536 1813137664 1813268736 14 6091 42580 31 _ _ (2131831 / 100000) (1065917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813268736 :
    ThetaLowerSegment 1813268736 1813399808 (90661431854649 / 50000) (11333499872701 / 6250) := by
  exact
    packedTile65536 1813268736 1813399808 14 6161 42582 31 _ _ (1065919 / 50000) (2131841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813399808 :
    ThetaLowerSegment 1813399808 1813530880 (11333499872701 / 6250) (45337267609189 / 25000) := by
  exact
    packedTile65536 1813399808 1813530880 14 6132 42584 31 _ _ (426369 / 20000) (266481 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813530880 :
    ThetaLowerSegment 1813530880 1813661952 (45337267609189 / 25000) (90681052292999 / 50000) := by
  exact
    packedTile65536 1813530880 1813661952 14 6114 42585 31 _ _ (2131853 / 100000) (133241 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813661952 :
    ThetaLowerSegment 1813661952 1813793024 (90681052292999 / 50000) (90687570454949 / 50000) := by
  exact
    packedTile65536 1813661952 1813793024 14 6115 42587 31 _ _ (106593 / 5000) (2131863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813793024 :
    ThetaLowerSegment 1813793024 1813924096 (90687570454949 / 50000) (45347054445519 / 25000) := by
  exact
    packedTile65536 1813793024 1813924096 14 6134 42588 31 _ _ (2131867 / 100000) (213187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1813924096 :
    ThetaLowerSegment 1813924096 1814055168 (45347054445519 / 25000) (45350326872109 / 25000) := by
  exact
    packedTile65536 1813924096 1814055168 14 6140 42590 31 _ _ (1065937 / 50000) (2131877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814055168 :
    ThetaLowerSegment 1814055168 1814186240 (45350326872109 / 25000) (4535358971751 / 2500) := by
  exact
    packedTile65536 1814055168 1814186240 14 6122 42591 31 _ _ (1065941 / 50000) (426377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814186240 :
    ThetaLowerSegment 1814186240 1814317312 (4535358971751 / 2500) (4535687282657 / 2500) := by
  exact
    packedTile65536 1814186240 1814317312 14 6160 42593 31 _ _ (2131889 / 100000) (532973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814317312 :
    ThetaLowerSegment 1814317312 1814448384 (4535687282657 / 2500) (5670017428027 / 3125) := by
  exact
    packedTile65536 1814317312 1814448384 14 6129 42594 31 _ _ (266487 / 12500) (2131899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814448384 :
    ThetaLowerSegment 1814448384 1814579456 (5670017428027 / 3125) (36290762347563 / 20000) := by
  exact
    packedTile65536 1814448384 1814579456 14 6217 42596 31 _ _ (2131903 / 100000) (1065953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814579456 :
    ThetaLowerSegment 1814579456 1814710528 (36290762347563 / 20000) (36293398667469 / 20000) := by
  exact
    packedTile65536 1814579456 1814710528 14 6183 42597 31 _ _ (213191 / 10000) (2131913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814710528 :
    ThetaLowerSegment 1814710528 1814841600 (36293398667469 / 20000) (36295984684003 / 20000) := by
  exact
    packedTile65536 1814710528 1814841600 14 6065 42599 31 _ _ (1065959 / 50000) (2131921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814841600 :
    ThetaLowerSegment 1814841600 1814972672 (36295984684003 / 20000) (36298598424053 / 20000) := by
  exact
    packedTile65536 1814841600 1814972672 14 6130 42600 31 _ _ (85277 / 4000) (266491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1814972672 :
    ThetaLowerSegment 1814972672 1815103744 (36298598424053 / 20000)
      (181506105633997 / 100000) := by
  exact
    packedTile65536 1814972672 1815103744 14 6151 42602 31 _ _ (532983 / 25000) (426387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815103744 :
    ThetaLowerSegment 1815103744 1815234816 (181506105633997 / 100000) (11344946136069 / 6250) := by
  exact
    packedTile65536 1815103744 1815234816 14 6113 42604 31 _ _ (2131939 / 100000) (1065971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815234816 :
    ThetaLowerSegment 1815234816 1815365888 (11344946136069 / 6250) (181532264574783 / 100000) := by
  exact
    packedTile65536 1815234816 1815365888 14 6157 42605 31 _ _ (2131947 / 100000) (42639 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815365888 :
    ThetaLowerSegment 1815365888 1815496960 (181532264574783 / 100000)
      (181545512536939 / 100000) := by
  exact
    packedTile65536 1815365888 1815496960 14 6214 42607 31 _ _ (1065977 / 50000) (2131957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815496960 :
    ThetaLowerSegment 1815496960 1815628032 (181545512536939 / 100000)
      (90779325906291 / 50000) := by
  exact
    packedTile65536 1815496960 1815628032 14 6163 42608 31 _ _ (2131961 / 100000) (532991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815628032 :
    ThetaLowerSegment 1815628032 1815759104 (90779325906291 / 50000) (90785879575923 / 50000) := by
  exact
    packedTile65536 1815628032 1815759104 14 6148 42610 31 _ _ (66624 / 3125) (2131971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815759104 :
    ThetaLowerSegment 1815759104 1815890176 (90785879575923 / 50000) (90792403419423 / 50000) := by
  exact
    packedTile65536 1815759104 1815890176 14 6120 42611 31 _ _ (85279 / 4000) (1065989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1815890176 :
    ThetaLowerSegment 1815890176 1816021248 (90792403419423 / 50000) (90798965663097 / 50000) := by
  exact
    packedTile65536 1815890176 1816021248 14 6156 42613 31 _ _ (2131983 / 100000) (1065993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816021248 :
    ThetaLowerSegment 1816021248 1816152320 (90798965663097 / 50000) (90805585492047 / 50000) := by
  exact
    packedTile65536 1816021248 1816152320 14 6210 42614 31 _ _ (213199 / 10000) (2131993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816152320 :
    ThetaLowerSegment 1816152320 1816283392 (90805585492047 / 50000) (90812100874879 / 50000) := by
  exact
    packedTile65536 1816152320 1816283392 14 6112 42616 31 _ _ (2131997 / 100000) (533 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816283392 :
    ThetaLowerSegment 1816283392 1816414464 (90812100874879 / 50000) (90818613081097 / 50000) := by
  exact
    packedTile65536 1816283392 1816414464 14 6109 42617 31 _ _ (533001 / 25000) (2132007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816414464 :
    ThetaLowerSegment 1816414464 1816545536 (90818613081097 / 50000) (90825191404123 / 50000) := by
  exact
    packedTile65536 1816414464 1816545536 14 6171 42619 31 _ _ (533003 / 25000) (426403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816545536 :
    ThetaLowerSegment 1816545536 1816676608 (90825191404123 / 50000) (36332707899499 / 20000) := by
  exact
    packedTile65536 1816545536 1816676608 14 6171 42620 31 _ _ (2132019 / 100000) (1066011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816676608 :
    ThetaLowerSegment 1816676608 1816807680 (36332707899499 / 20000)
      (181676519271783 / 100000) := by
  exact
    packedTile65536 1816676608 1816807680 14 6088 42622 31 _ _ (1066013 / 50000) (2132029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816807680 :
    ThetaLowerSegment 1816807680 1816938752 (181676519271783 / 100000)
      (90844863608109 / 50000) := by
  exact
    packedTile65536 1816807680 1816938752 14 6195 42624 31 _ _ (2132033 / 100000) (533009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816938752 :
    ThetaLowerSegment 1816938752 1817069824 (90844863608109 / 50000) (90851358867969 / 50000) := by
  exact
    packedTile65536 1816938752 1817069824 14 6093 42625 31 _ _ (53301 / 2500) (2132043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817069824 :
    ThetaLowerSegment 1817069824 1817200896 (90851358867969 / 50000) (90857875472681 / 50000) := by
  exact
    packedTile65536 1817069824 1817200896 14 6113 42627 31 _ _ (133253 / 6250) (2132051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817200896 :
    ThetaLowerSegment 1817200896 1817331968 (90857875472681 / 50000)
      (181728835366897 / 100000) := by
  exact
    packedTile65536 1817200896 1817331968 14 6137 42628 31 _ _ (426411 / 20000) (1066029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817331968 :
    ThetaLowerSegment 1817331968 1817463040 (181728835366897 / 100000)
      (181741896378709 / 100000) := by
  exact
    packedTile65536 1817331968 1817463040 14 6126 42630 31 _ _ (1066031 / 50000) (426413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817463040 :
    ThetaLowerSegment 1817463040 1817594112 (181741896378709 / 100000)
      (181755072565129 / 100000) := by
  exact
    packedTile65536 1817463040 1817594112 14 6180 42631 31 _ _ (2132069 / 100000) (266509 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817594112 :
    ThetaLowerSegment 1817594112 1817725184 (181755072565129 / 100000)
      (181768297832557 / 100000) := by
  exact
    packedTile65536 1817594112 1817725184 14 6203 42633 31 _ _ (533019 / 25000) (2132079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817725184 :
    ThetaLowerSegment 1817725184 1817856256 (181768297832557 / 100000)
      (181781344054553 / 100000) := by
  exact
    packedTile65536 1817725184 1817856256 14 6119 42634 31 _ _ (533021 / 25000) (2132087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817856256 :
    ThetaLowerSegment 1817856256 1817987328 (181781344054553 / 100000)
      (90897229273147 / 50000) := by
  exact
    packedTile65536 1817856256 1817987328 14 6151 42636 31 _ _ (2132091 / 100000) (1066047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1817987328 :
    ThetaLowerSegment 1817987328 1818118400 (90897229273147 / 50000) (11362969852909 / 6250) := by
  exact
    packedTile65536 1817987328 1818118400 14 6125 42637 31 _ _ (1066049 / 50000) (2132101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818118400 :
    ThetaLowerSegment 1818118400 1818249472 (11362969852909 / 6250) (45455122343341 / 25000) := by
  exact
    packedTile65536 1818118400 1818249472 14 6084 42639 31 _ _ (426421 / 20000) (533027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818249472 :
    ThetaLowerSegment 1818249472 1818380544 (45455122343341 / 25000) (18183358481141 / 10000) := by
  exact
    packedTile65536 1818249472 1818380544 14 6142 42640 31 _ _ (2132113 / 100000) (533029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818380544 :
    ThetaLowerSegment 1818380544 1818511616 (18183358481141 / 10000) (18184664404641 / 10000) := by
  exact
    packedTile65536 1818380544 1818511616 14 6125 42642 31 _ _ (53303 / 2500) (2132123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818511616 :
    ThetaLowerSegment 1818511616 1818642688 (18184664404641 / 10000) (90929884710111 / 50000) := by
  exact
    packedTile65536 1818511616 1818642688 14 6156 42644 31 _ _ (2132127 / 100000) (213213 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818642688 :
    ThetaLowerSegment 1818642688 1818773760 (90929884710111 / 50000) (22734097729253 / 12500) := by
  exact
    packedTile65536 1818642688 1818773760 14 6103 42645 31 _ _ (1066067 / 50000) (2132137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818773760 :
    ThetaLowerSegment 1818773760 1818904832 (22734097729253 / 12500) (22735726684977 / 12500) := by
  exact
    packedTile65536 1818773760 1818904832 14 6112 42647 31 _ _ (2132141 / 100000) (133259 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1818904832 :
    ThetaLowerSegment 1818904832 1819035904 (22735726684977 / 12500)
      (181898975235593 / 100000) := by
  exact
    packedTile65536 1818904832 1819035904 14 6173 42648 31 _ _ (2132149 / 100000) (266519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819035904 :
    ThetaLowerSegment 1819035904 1819166976 (181898975235593 / 100000)
      (36382397130301 / 20000) := by
  exact
    packedTile65536 1819035904 1819166976 14 6102 42650 31 _ _ (533039 / 25000) (2132159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819166976 :
    ThetaLowerSegment 1819166976 1819298048 (36382397130301 / 20000) (4548126128747 / 2500) := by
  exact
    packedTile65536 1819166976 1819298048 14 6125 42651 31 _ _ (2132163 / 100000) (1066083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819298048 :
    ThetaLowerSegment 1819298048 1819429120 (4548126128747 / 2500) (227422606877 / 125) := by
  exact
    packedTile65536 1819298048 1819429120 14 6116 42653 31 _ _ (213217 / 10000) (2132173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819429120 :
    ThetaLowerSegment 1819429120 1819560192 (227422606877 / 125) (90975603459429 / 50000) := by
  exact
    packedTile65536 1819429120 1819560192 14 6154 42654 31 _ _ (2132177 / 100000) (106609 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819560192 :
    ThetaLowerSegment 1819560192 1819691264 (90975603459429 / 50000) (90982217497299 / 50000) := by
  exact
    packedTile65536 1819560192 1819691264 14 6204 42656 31 _ _ (426437 / 20000) (533047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819691264 :
    ThetaLowerSegment 1819691264 1819822336 (90982217497299 / 50000) (90988783582563 / 50000) := by
  exact
    packedTile65536 1819691264 1819822336 14 6159 42657 31 _ _ (66631 / 3125) (426439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819822336 :
    ThetaLowerSegment 1819822336 1819953408 (90988783582563 / 50000) (90995427514647 / 50000) := by
  exact
    packedTile65536 1819822336 1819953408 14 6232 42659 31 _ _ (2132199 / 100000) (1066101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1819953408 :
    ThetaLowerSegment 1819953408 1820084480 (90995427514647 / 50000) (91001956329419 / 50000) := by
  exact
    packedTile65536 1819953408 1820084480 14 6124 42660 31 _ _ (1066103 / 50000) (2132209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820084480 :
    ThetaLowerSegment 1820084480 1820215552 (91001956329419 / 50000)
      (182017006578871 / 100000) := by
  exact
    packedTile65536 1820084480 1820215552 14 6141 42662 31 _ _ (2132213 / 100000) (266527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820215552 :
    ThetaLowerSegment 1820215552 1820346624 (182017006578871 / 100000) (9101499483627 / 5000) := by
  exact
    packedTile65536 1820215552 1820346624 14 6089 42663 31 _ _ (2132221 / 100000) (66632 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820346624 :
    ThetaLowerSegment 1820346624 1820477696 (9101499483627 / 5000) (5688847697789 / 3125) := by
  exact
    packedTile65536 1820346624 1820477696 14 6161 42665 31 _ _ (533057 / 25000) (2132231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820477696 :
    ThetaLowerSegment 1820477696 1820608768 (5688847697789 / 3125) (182056075392403 / 100000) := by
  exact
    packedTile65536 1820477696 1820608768 14 6073 42667 31 _ _ (426447 / 20000) (1066119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820608768 :
    ThetaLowerSegment 1820608768 1820739840 (182056075392403 / 100000)
      (36413838162589 / 20000) := by
  exact
    packedTile65536 1820608768 1820739840 14 6151 42668 31 _ _ (1066121 / 50000) (426449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820739840 :
    ThetaLowerSegment 1820739840 1820870912 (36413838162589 / 20000) (91041108361043 / 50000) := by
  exact
    packedTile65536 1820739840 1820870912 14 6109 42670 31 _ _ (2132249 / 100000) (533063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820870912 :
    ThetaLowerSegment 1820870912 1821001984 (91041108361043 / 50000) (22761923725729 / 12500) := by
  exact
    packedTile65536 1820870912 1821001984 14 6178 42671 31 _ _ (2132257 / 100000) (106613 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821001984 :
    ThetaLowerSegment 1821001984 1821133056 (22761923725729 / 12500) (22763564502877 / 12500) := by
  exact
    packedTile65536 1821001984 1821133056 14 6156 42673 31 _ _ (266533 / 12500) (2132267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821133056 :
    ThetaLowerSegment 1821133056 1821264128 (22763564502877 / 12500) (36424287090601 / 20000) := by
  exact
    packedTile65536 1821133056 1821264128 14 6059 42674 31 _ _ (2132271 / 100000) (1066137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821264128 :
    ThetaLowerSegment 1821264128 1821395200 (36424287090601 / 20000)
      (182134653444327 / 100000) := by
  exact
    packedTile65536 1821264128 1821395200 14 6199 42676 31 _ _ (1066139 / 50000) (2132281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821395200 :
    ThetaLowerSegment 1821395200 1821526272 (182134653444327 / 100000)
      (182147929050737 / 100000) := by
  exact
    packedTile65536 1821395200 1821526272 14 6226 42677 31 _ _ (426457 / 20000) (66634 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821526272 :
    ThetaLowerSegment 1821526272 1821657344 (182147929050737 / 100000)
      (182161085298547 / 100000) := by
  exact
    packedTile65536 1821526272 1821657344 14 6170 42679 31 _ _ (2132293 / 100000) (266537 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821657344 :
    ThetaLowerSegment 1821657344 1821788416 (182161085298547 / 100000)
      (182174329013847 / 100000) := by
  exact
    packedTile65536 1821657344 1821788416 14 6211 42680 31 _ _ (21323 / 1000) (2132303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821788416 :
    ThetaLowerSegment 1821788416 1821919488 (182174329013847 / 100000)
      (182187186825057 / 100000) := by
  exact
    packedTile65536 1821788416 1821919488 14 6030 42682 31 _ _ (2132307 / 100000) (213231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1821919488 :
    ThetaLowerSegment 1821919488 1822050560 (182187186825057 / 100000)
      (182200345334751 / 100000) := by
  exact
    packedTile65536 1821919488 1822050560 14 6171 42683 31 _ _ (1066157 / 50000) (2132317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822050560 :
    ThetaLowerSegment 1822050560 1822181632 (182200345334751 / 100000)
      (22776678923591 / 12500) := by
  exact
    packedTile65536 1822050560 1822181632 14 6137 42685 31 _ _ (2132321 / 100000) (533081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822181632 :
    ThetaLowerSegment 1822181632 1822312704 (22776678923591 / 12500) (22778316552263 / 12500) := by
  exact
    packedTile65536 1822181632 1822312704 14 6144 42687 31 _ _ (2132329 / 100000) (533083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822312704 :
    ThetaLowerSegment 1822312704 1822443776 (22778316552263 / 12500) (22779944857341 / 12500) := by
  exact
    packedTile65536 1822312704 1822443776 14 6109 42688 31 _ _ (133271 / 6250) (2132339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822443776 :
    ThetaLowerSegment 1822443776 1822574848 (22779944857341 / 12500) (22781578232079 / 12500) := by
  exact
    packedTile65536 1822443776 1822574848 14 6128 42690 31 _ _ (2132343 / 100000) (1066173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822574848 :
    ThetaLowerSegment 1822574848 1822705920 (22781578232079 / 12500) (91132832588441 / 50000) := by
  exact
    packedTile65536 1822574848 1822705920 14 6115 42691 31 _ _ (42647 / 2000) (2132353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822705920 :
    ThetaLowerSegment 1822705920 1822836992 (91132832588441 / 50000)
      (182278772775361 / 100000) := by
  exact
    packedTile65536 1822705920 1822836992 14 6147 42693 31 _ _ (2132357 / 100000) (53309 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822836992 :
    ThetaLowerSegment 1822836992 1822968064 (182278772775361 / 100000)
      (182291778063397 / 100000) := by
  exact
    packedTile65536 1822836992 1822968064 14 6099 42694 31 _ _ (533091 / 25000) (2132367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1822968064 :
    ThetaLowerSegment 1822968064 1823099136 (182291778063397 / 100000)
      (182304713031949 / 100000) := by
  exact
    packedTile65536 1822968064 1823099136 14 6066 42696 31 _ _ (533093 / 25000) (17059 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823099136 :
    ThetaLowerSegment 1823099136 1823230208 (182304713031949 / 100000)
      (182317869810379 / 100000) := by
  exact
    packedTile65536 1823099136 1823230208 14 6170 42697 31 _ _ (2132379 / 100000) (1066191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823230208 :
    ThetaLowerSegment 1823230208 1823361280 (182317869810379 / 100000)
      (182330962660419 / 100000) := by
  exact
    packedTile65536 1823230208 1823361280 14 6140 42699 31 _ _ (1066193 / 50000) (2132389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823361280 :
    ThetaLowerSegment 1823361280 1823492352 (182330962660419 / 100000)
      (182344012905579 / 100000) := by
  exact
    packedTile65536 1823361280 1823492352 14 6120 42700 31 _ _ (2132393 / 100000) (533099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823492352 :
    ThetaLowerSegment 1823492352 1823623424 (182344012905579 / 100000)
      (182357240182779 / 100000) := by
  exact
    packedTile65536 1823492352 1823623424 14 6203 42702 31 _ _ (5331 / 250) (2132403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823623424 :
    ThetaLowerSegment 1823623424 1823754496 (182357240182779 / 100000)
      (182370439788299 / 100000) := by
  exact
    packedTile65536 1823623424 1823754496 14 6190 42703 31 _ _ (266551 / 12500) (2132411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823754496 :
    ThetaLowerSegment 1823754496 1823885568 (182370439788299 / 100000)
      (91191788798557 / 50000) := by
  exact
    packedTile65536 1823754496 1823885568 14 6161 42705 31 _ _ (426483 / 20000) (1066209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1823885568 :
    ThetaLowerSegment 1823885568 1824016640 (91191788798557 / 50000) (91198399306757 / 50000) := by
  exact
    packedTile65536 1823885568 1824016640 14 6200 42706 31 _ _ (1066211 / 50000) (85297 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824016640 :
    ThetaLowerSegment 1824016640 1824147712 (91198399306757 / 50000) (91204937334071 / 50000) := by
  exact
    packedTile65536 1824016640 1824147712 14 6132 42708 31 _ _ (2132429 / 100000) (133277 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824147712 :
    ThetaLowerSegment 1824147712 1824278784 (91204937334071 / 50000) (91211553216761 / 50000) := by
  exact
    packedTile65536 1824147712 1824278784 14 6205 42710 31 _ _ (533109 / 25000) (2132439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824278784 :
    ThetaLowerSegment 1824278784 1824409856 (91211553216761 / 50000) (91218141402499 / 50000) := by
  exact
    packedTile65536 1824278784 1824409856 14 6179 42711 31 _ _ (533111 / 25000) (2132447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824409856 :
    ThetaLowerSegment 1824409856 1824540928 (91218141402499 / 50000) (22806178937233 / 12500) := by
  exact
    packedTile65536 1824409856 1824540928 14 6166 42713 31 _ _ (2132451 / 100000) (1066227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824540928 :
    ThetaLowerSegment 1824540928 1824672000 (22806178937233 / 12500) (91231278388427 / 50000) := by
  exact
    packedTile65536 1824540928 1824672000 14 6155 42714 31 _ _ (1066229 / 50000) (2132461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824672000 :
    ThetaLowerSegment 1824672000 1824803072 (91231278388427 / 50000)
      (182475566945819 / 100000) := by
  exact
    packedTile65536 1824672000 1824803072 14 6101 42716 31 _ _ (426493 / 20000) (533117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824803072 :
    ThetaLowerSegment 1824803072 1824934144 (182475566945819 / 100000)
      (36497733344263 / 20000) := by
  exact
    packedTile65536 1824803072 1824934144 14 6143 42717 31 _ _ (266559 / 12500) (85299 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824934144 :
    ThetaLowerSegment 1824934144 1825065216 (36497733344263 / 20000) (36500369088307 / 20000) := by
  exact
    packedTile65536 1824934144 1825065216 14 6180 42719 31 _ _ (2132479 / 100000) (1066241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825065216 :
    ThetaLowerSegment 1825065216 1825196288 (36500369088307 / 20000) (91257406547491 / 50000) := by
  exact
    packedTile65536 1825065216 1825196288 14 6081 42720 31 _ _ (2132487 / 100000) (213249 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825196288 :
    ThetaLowerSegment 1825196288 1825327360 (91257406547491 / 50000) (91264038603831 / 50000) := by
  exact
    packedTile65536 1825196288 1825327360 14 6220 42722 31 _ _ (1066247 / 50000) (2132497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825327360 :
    ThetaLowerSegment 1825327360 1825458432 (91264038603831 / 50000)
      (182541168631301 / 100000) := by
  exact
    packedTile65536 1825327360 1825458432 14 6139 42723 31 _ _ (2132501 / 100000) (266563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825458432 :
    ThetaLowerSegment 1825458432 1825589504 (182541168631301 / 100000)
      (36510862255621 / 20000) := by
  exact
    packedTile65536 1825458432 1825589504 14 6163 42725 31 _ _ (533127 / 25000) (2132511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825589504 :
    ThetaLowerSegment 1825589504 1825720576 (36510862255621 / 20000) (730269645271 / 400) := by
  exact
    packedTile65536 1825589504 1825720576 14 6143 42726 31 _ _ (426503 / 20000) (1066259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825720576 :
    ThetaLowerSegment 1825720576 1825851648 (730269645271 / 400) (45645074005429 / 25000) := by
  exact
    packedTile65536 1825720576 1825851648 14 6042 42728 31 _ _ (2132523 / 100000) (1066263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825851648 :
    ThetaLowerSegment 1825851648 1825982720 (45645074005429 / 25000) (45648364499219 / 25000) := by
  exact
    packedTile65536 1825851648 1825982720 14 6172 42729 31 _ _ (213253 / 10000) (2132533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1825982720 :
    ThetaLowerSegment 1825982720 1826113792 (45648364499219 / 25000) (45651627280829 / 25000) := by
  exact
    packedTile65536 1825982720 1826113792 14 6120 42731 31 _ _ (2132537 / 100000) (106627 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826113792 :
    ThetaLowerSegment 1826113792 1826244864 (45651627280829 / 25000) (45654880476701 / 25000) := by
  exact
    packedTile65536 1826113792 1826244864 14 6102 42733 31 _ _ (66642 / 3125) (2132547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826244864 :
    ThetaLowerSegment 1826244864 1826375936 (45654880476701 / 25000) (91316263101401 / 50000) := by
  exact
    packedTile65536 1826244864 1826375936 14 6098 42734 31 _ _ (2132551 / 100000) (1066277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826375936 :
    ThetaLowerSegment 1826375936 1826507008 (91316263101401 / 50000) (22830711310417 / 12500) := by
  exact
    packedTile65536 1826375936 1826507008 14 6173 42736 31 _ _ (1066279 / 50000) (2132561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826507008 :
    ThetaLowerSegment 1826507008 1826638080 (22830711310417 / 12500) (11416167629713 / 6250) := by
  exact
    packedTile65536 1826507008 1826638080 14 6092 42737 31 _ _ (1066283 / 50000) (2132569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826638080 :
    ThetaLowerSegment 1826638080 1826769152 (11416167629713 / 6250) (182671940281749 / 100000) := by
  exact
    packedTile65536 1826638080 1826769152 14 6217 42739 31 _ _ (2132573 / 100000) (66643 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826769152 :
    ThetaLowerSegment 1826769152 1826900224 (182671940281749 / 100000)
      (182685241183209 / 100000) := by
  exact
    packedTile65536 1826769152 1826900224 14 6237 42740 31 _ _ (106629 / 5000) (2132583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1826900224 :
    ThetaLowerSegment 1826900224 1827031296 (182685241183209 / 100000)
      (36539661935269 / 20000) := by
  exact
    packedTile65536 1826900224 1827031296 14 6128 42742 31 _ _ (2132587 / 100000) (213259 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827031296 :
    ThetaLowerSegment 1827031296 1827162368 (36539661935269 / 20000)
      (182711410201287 / 100000) := by
  exact
    packedTile65536 1827031296 1827162368 14 6143 42743 31 _ _ (1066297 / 50000) (2132597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827162368 :
    ThetaLowerSegment 1827162368 1827293440 (182711410201287 / 100000)
      (182724547023447 / 100000) := by
  exact
    packedTile65536 1827162368 1827293440 14 6160 42745 31 _ _ (2132601 / 100000) (533151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827293440 :
    ThetaLowerSegment 1827293440 1827424512 (182724547023447 / 100000)
      (182737679629669 / 100000) := by
  exact
    packedTile65536 1827293440 1827424512 14 6158 42746 31 _ _ (2132609 / 100000) (533153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827424512 :
    ThetaLowerSegment 1827424512 1827555584 (182737679629669 / 100000)
      (36550136011361 / 20000) := by
  exact
    packedTile65536 1827424512 1827555584 14 6096 42748 31 _ _ (266577 / 12500) (2132619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827555584 :
    ThetaLowerSegment 1827555584 1827686656 (36550136011361 / 20000) (91381847727487 / 50000) := by
  exact
    packedTile65536 1827555584 1827686656 14 6103 42749 31 _ _ (2132623 / 100000) (1066313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827686656 :
    ThetaLowerSegment 1827686656 1827817728 (91381847727487 / 50000) (5711775147862 / 3125) := by
  exact
    packedTile65536 1827686656 1827817728 14 6147 42751 31 _ _ (213263 / 10000) (2132633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827817728 :
    ThetaLowerSegment 1827817728 1827948800 (5711775147862 / 3125) (45697487576513 / 25000) := by
  exact
    packedTile65536 1827817728 1827948800 14 6164 42752 31 _ _ (2132637 / 100000) (13329 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1827948800 :
    ThetaLowerSegment 1827948800 1828079872 (45697487576513 / 25000)
      (182803170572407 / 100000) := by
  exact
    packedTile65536 1827948800 1828079872 14 6199 42754 31 _ _ (426529 / 20000) (266581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828079872 :
    ThetaLowerSegment 1828079872 1828210944 (182803170572407 / 100000)
      (182816418606631 / 100000) := by
  exact
    packedTile65536 1828079872 1828210944 14 6212 42756 31 _ _ (533163 / 25000) (426531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828210944 :
    ThetaLowerSegment 1828210944 1828342016 (182816418606631 / 100000) (5713424884581 / 3125) := by
  exact
    packedTile65536 1828210944 1828342016 14 6179 42757 31 _ _ (2132659 / 100000) (1066331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828342016 :
    ThetaLowerSegment 1828342016 1828473088 (5713424884581 / 3125) (91421312381593 / 50000) := by
  exact
    packedTile65536 1828342016 1828473088 14 6109 42759 31 _ _ (1066333 / 50000) (2132669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828473088 :
    ThetaLowerSegment 1828473088 1828604160 (91421312381593 / 50000) (36571149420031 / 20000) := by
  exact
    packedTile65536 1828473088 1828604160 14 6153 42760 31 _ _ (2132673 / 100000) (533169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828604160 :
    ThetaLowerSegment 1828604160 1828735232 (36571149420031 / 20000) (36573747877343 / 20000) := by
  exact
    packedTile65536 1828604160 1828735232 14 6092 42762 31 _ _ (53317 / 2500) (2132683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828735232 :
    ThetaLowerSegment 1828735232 1828866304 (36573747877343 / 20000) (7315275922867 / 4000) := by
  exact
    packedTile65536 1828735232 1828866304 14 6170 42763 31 _ _ (133293 / 6250) (2132691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828866304 :
    ThetaLowerSegment 1828866304 1828997376 (7315275922867 / 4000) (914475124047 / 500) := by
  exact
    packedTile65536 1828866304 1828997376 14 6155 42765 31 _ _ (426539 / 20000) (1066349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1828997376 :
    ThetaLowerSegment 1828997376 1829128448 (914475124047 / 500) (91454084325913 / 50000) := by
  exact
    packedTile65536 1828997376 1829128448 14 6163 42766 31 _ _ (1066351 / 50000) (426541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829128448 :
    ThetaLowerSegment 1829128448 1829259520 (91454084325913 / 50000) (45730314804917 / 25000) := by
  exact
    packedTile65536 1829128448 1829259520 14 6138 42768 31 _ _ (2132709 / 100000) (266589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829259520 :
    ThetaLowerSegment 1829259520 1829390592 (45730314804917 / 25000) (22866787597251 / 12500) := by
  exact
    packedTile65536 1829259520 1829390592 14 6115 42769 31 _ _ (533179 / 25000) (2132719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829390592 :
    ThetaLowerSegment 1829390592 1829521664 (22866787597251 / 12500) (45736887313321 / 25000) := by
  exact
    packedTile65536 1829390592 1829521664 14 6212 42771 31 _ _ (2132723 / 100000) (1066363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829521664 :
    ThetaLowerSegment 1829521664 1829652736 (45736887313321 / 25000) (45740167453599 / 25000) := by
  exact
    packedTile65536 1829521664 1829652736 14 6152 42772 31 _ _ (2132731 / 100000) (1066367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829652736 :
    ThetaLowerSegment 1829652736 1829783808 (45740167453599 / 25000) (45743447604643 / 25000) := by
  exact
    packedTile65536 1829652736 1829783808 14 6152 42774 31 _ _ (1066369 / 50000) (2132741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829783808 :
    ThetaLowerSegment 1829783808 1829914880 (45743447604643 / 25000)
      (182986712720527 / 100000) := by
  exact
    packedTile65536 1829783808 1829914880 14 6059 42775 31 _ _ (426549 / 20000) (533187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829914880 :
    ThetaLowerSegment 1829914880 1830045952 (182986712720527 / 100000)
      (182999707578463 / 100000) := by
  exact
    packedTile65536 1829914880 1830045952 14 6093 42777 31 _ _ (133297 / 6250) (426551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830045952 :
    ThetaLowerSegment 1830045952 1830177024 (182999707578463 / 100000)
      (91506368301597 / 50000) := by
  exact
    packedTile65536 1830045952 1830177024 14 6109 42779 31 _ _ (2132759 / 100000) (1066381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830177024 :
    ThetaLowerSegment 1830177024 1830308096 (91506368301597 / 50000) (9151292762343 / 5000) := by
  exact
    packedTile65536 1830177024 1830308096 14 6151 42780 31 _ _ (1066383 / 50000) (2132769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830308096 :
    ThetaLowerSegment 1830308096 1830439168 (9151292762343 / 5000) (9151951789509 / 5000) := by
  exact
    packedTile65536 1830308096 1830439168 14 6180 42782 31 _ _ (1066387 / 50000) (2132777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830439168 :
    ThetaLowerSegment 1830439168 1830570240 (9151951789509 / 5000) (183052209978417 / 100000) := by
  exact
    packedTile65536 1830439168 1830570240 14 6177 42783 31 _ _ (2132781 / 100000) (133299 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830570240 :
    ThetaLowerSegment 1830570240 1830701312 (183052209978417 / 100000)
      (183065207188489 / 100000) := by
  exact
    packedTile65536 1830570240 1830701312 14 6094 42785 31 _ _ (533197 / 25000) (2132791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830701312 :
    ThetaLowerSegment 1830701312 1830832384 (183065207188489 / 100000)
      (183078319612149 / 100000) := by
  exact
    packedTile65536 1830701312 1830832384 14 6148 42786 31 _ _ (426559 / 20000) (1066399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830832384 :
    ThetaLowerSegment 1830832384 1830963456 (183078319612149 / 100000) (7323656430033 / 4000) := by
  exact
    packedTile65536 1830832384 1830963456 14 6138 42788 31 _ _ (1066401 / 50000) (426561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1830963456 :
    ThetaLowerSegment 1830963456 1831094528 (7323656430033 / 4000) (45776143078791 / 25000) := by
  exact
    packedTile65536 1830963456 1831094528 14 6171 42789 31 _ _ (2132809 / 100000) (533203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831094528 :
    ThetaLowerSegment 1831094528 1831225600 (45776143078791 / 25000) (45779422283391 / 25000) := by
  exact
    packedTile65536 1831094528 1831225600 14 6150 42791 31 _ _ (133301 / 6250) (2132819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831225600 :
    ThetaLowerSegment 1831225600 1831356672 (45779422283391 / 25000) (9156532728533 / 5000) := by
  exact
    packedTile65536 1831225600 1831356672 14 6079 42792 31 _ _ (266603 / 12500) (2132827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831356672 :
    ThetaLowerSegment 1831356672 1831487744 (9156532728533 / 5000) (183143829067747 / 100000) := by
  exact
    packedTile65536 1831356672 1831487744 14 6177 42794 31 _ _ (2132831 / 100000) (1066417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831487744 :
    ThetaLowerSegment 1831487744 1831618816 (183143829067747 / 100000)
      (183156843645223 / 100000) := by
  exact
    packedTile65536 1831487744 1831618816 14 6102 42795 31 _ _ (1066419 / 50000) (2132841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831618816 :
    ThetaLowerSegment 1831618816 1831749888 (183156843645223 / 100000)
      (22896253345021 / 12500) := by
  exact
    packedTile65536 1831618816 1831749888 14 6181 42797 31 _ _ (426569 / 20000) (133303 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831749888 :
    ThetaLowerSegment 1831749888 1831880960 (22896253345021 / 12500) (45795795014613 / 25000) := by
  exact
    packedTile65536 1831749888 1831880960 14 6167 42798 31 _ _ (533213 / 25000) (426571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1831880960 :
    ThetaLowerSegment 1831880960 1832012032 (45795795014613 / 25000) (45799100946063 / 25000) := by
  exact
    packedTile65536 1831880960 1832012032 14 6200 42800 31 _ _ (2132859 / 100000) (1066431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832012032 :
    ThetaLowerSegment 1832012032 1832143104 (45799100946063 / 25000)
      (183209407874351 / 100000) := by
  exact
    packedTile65536 1832012032 1832143104 14 6097 42802 31 _ _ (2132867 / 100000) (213287 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832143104 :
    ThetaLowerSegment 1832143104 1832274176 (183209407874351 / 100000)
      (36644490506347 / 20000) := by
  exact
    packedTile65536 1832143104 1832274176 14 6116 42803 31 _ _ (1066437 / 50000) (2132877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832274176 :
    ThetaLowerSegment 1832274176 1832405248 (36644490506347 / 20000)
      (183235450308549 / 100000) := by
  exact
    packedTile65536 1832274176 1832405248 14 6094 42805 31 _ _ (2132881 / 100000) (533221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832405248 :
    ThetaLowerSegment 1832405248 1832536320 (183235450308549 / 100000)
      (36649733563097 / 20000) := by
  exact
    packedTile65536 1832405248 1832536320 14 6197 42806 31 _ _ (266611 / 12500) (2132891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832536320 :
    ThetaLowerSegment 1832536320 1832667392 (36649733563097 / 20000) (9163082750657 / 5000) := by
  exact
    packedTile65536 1832536320 1832667392 14 6089 42808 31 _ _ (426579 / 20000) (1066449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832667392 :
    ThetaLowerSegment 1832667392 1832798464 (9163082750657 / 5000) (91637314728003 / 50000) := by
  exact
    packedTile65536 1832667392 1832798464 14 6083 42809 31 _ _ (1066451 / 50000) (426581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832798464 :
    ThetaLowerSegment 1832798464 1832929536 (91637314728003 / 50000) (22910965156431 / 12500) := by
  exact
    packedTile65536 1832798464 1832929536 14 6138 42811 31 _ _ (2132909 / 100000) (133307 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1832929536 :
    ThetaLowerSegment 1832929536 1833060608 (22910965156431 / 12500)
      (183300751241401 / 100000) := by
  exact
    packedTile65536 1832929536 1833060608 14 6109 42812 31 _ _ (2132917 / 100000) (53323 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833060608 :
    ThetaLowerSegment 1833060608 1833191680 (183300751241401 / 100000)
      (183313962572657 / 100000) := by
  exact
    packedTile65536 1833060608 1833191680 14 6194 42814 31 _ _ (533231 / 25000) (2132927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833191680 :
    ThetaLowerSegment 1833191680 1833322752 (183313962572657 / 100000)
      (183327212340029 / 100000) := by
  exact
    packedTile65536 1833191680 1833322752 14 6212 42815 31 _ _ (2132931 / 100000) (1066467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833322752 :
    ThetaLowerSegment 1833322752 1833339136 (183327212340029 / 100000)
      (183328867499917 / 100000) := by
  exact
    packedTile65536 1833322752 1833339136 11 776 42817 31 _ _ (1066469 / 50000) (2132941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833339136 :
    ThetaLowerSegment 1833339136 1833341184 (183328867499917 / 100000)
      (36665812746061 / 20000) := by
  exact
    packedTile65536 1833339136 1833341184 8 92 42817 31 _ _ (2132939 / 100000) (1066471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1801341184_1833341184 :
    ThetaLowerSegment 1801341184 1833341184 (180130263237107 / 100000)
      (36665812746061 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1801341184 cell1801472256)
                  (ThetaLowerSegment.join cell1801603328 cell1801734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1801865472 cell1801996544)
                  (ThetaLowerSegment.join cell1802127616 cell1802258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1802389760 cell1802520832)
                  (ThetaLowerSegment.join cell1802651904 cell1802782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1802914048 cell1803045120)
                  (ThetaLowerSegment.join cell1803176192 cell1803307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1803438336 cell1803569408)
                  (ThetaLowerSegment.join cell1803700480 cell1803831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1803962624 cell1804093696)
                  (ThetaLowerSegment.join cell1804224768 cell1804355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1804486912 cell1804617984)
                  (ThetaLowerSegment.join cell1804749056 cell1804880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1805011200 cell1805142272)
                  (ThetaLowerSegment.join cell1805273344 cell1805404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1805535488 cell1805666560)
                  (ThetaLowerSegment.join cell1805797632 cell1805928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1806059776 cell1806190848)
                  (ThetaLowerSegment.join cell1806321920 cell1806452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1806584064 cell1806715136)
                  (ThetaLowerSegment.join cell1806846208 cell1806977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1807108352 cell1807239424)
                  (ThetaLowerSegment.join cell1807370496 cell1807501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1807632640 cell1807763712)
                  (ThetaLowerSegment.join cell1807894784 cell1808025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1808156928 cell1808288000)
                  (ThetaLowerSegment.join cell1808419072 cell1808550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1808681216 cell1808812288)
                  (ThetaLowerSegment.join cell1808943360 cell1809074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1809205504 cell1809336576)
                  (ThetaLowerSegment.join cell1809467648 cell1809598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1809729792 cell1809860864)
                  (ThetaLowerSegment.join cell1809991936 cell1810123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1810254080 cell1810385152)
                  (ThetaLowerSegment.join cell1810516224 cell1810647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1810778368 cell1810909440)
                  (ThetaLowerSegment.join cell1811040512 cell1811171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1811302656 cell1811433728)
                  (ThetaLowerSegment.join cell1811564800 cell1811695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1811826944 cell1811958016)
                  (ThetaLowerSegment.join cell1812089088 cell1812220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1812351232 cell1812482304)
                  (ThetaLowerSegment.join cell1812613376 cell1812744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1812875520 cell1813006592)
                  (ThetaLowerSegment.join cell1813137664 cell1813268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1813399808 cell1813530880)
                  (ThetaLowerSegment.join cell1813661952 cell1813793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1813924096 cell1814055168)
                  (ThetaLowerSegment.join cell1814186240 cell1814317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1814448384 cell1814579456)
                  (ThetaLowerSegment.join cell1814710528 cell1814841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1814972672 cell1815103744)
                  (ThetaLowerSegment.join cell1815234816 cell1815365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1815496960 cell1815628032)
                  (ThetaLowerSegment.join cell1815759104 cell1815890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1816021248 cell1816152320)
                  (ThetaLowerSegment.join cell1816283392 cell1816414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1816545536 cell1816676608)
                  (ThetaLowerSegment.join cell1816807680 cell1816938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1817069824 cell1817200896)
                  (ThetaLowerSegment.join cell1817331968 cell1817463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1817594112 cell1817725184)
                  (ThetaLowerSegment.join cell1817856256 cell1817987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1818118400 cell1818249472)
                  (ThetaLowerSegment.join cell1818380544 cell1818511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1818642688 cell1818773760)
                  (ThetaLowerSegment.join cell1818904832 cell1819035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1819166976 cell1819298048)
                  (ThetaLowerSegment.join cell1819429120 cell1819560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1819691264 cell1819822336)
                  (ThetaLowerSegment.join cell1819953408 cell1820084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1820215552 cell1820346624)
                  (ThetaLowerSegment.join cell1820477696 cell1820608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1820739840 cell1820870912)
                  (ThetaLowerSegment.join cell1821001984 cell1821133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1821264128 cell1821395200)
                  (ThetaLowerSegment.join cell1821526272 cell1821657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1821788416 cell1821919488)
                  (ThetaLowerSegment.join cell1822050560 cell1822181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1822312704 cell1822443776)
                  (ThetaLowerSegment.join cell1822574848 cell1822705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1822836992 cell1822968064)
                  (ThetaLowerSegment.join cell1823099136 cell1823230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1823361280 cell1823492352)
                  (ThetaLowerSegment.join cell1823623424 cell1823754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1823885568 cell1824016640)
                  (ThetaLowerSegment.join cell1824147712 cell1824278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1824409856 cell1824540928)
                  (ThetaLowerSegment.join cell1824672000 cell1824803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1824934144 cell1825065216)
                  (ThetaLowerSegment.join cell1825196288 cell1825327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1825458432 cell1825589504)
                  (ThetaLowerSegment.join cell1825720576 cell1825851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1825982720 cell1826113792)
                  (ThetaLowerSegment.join cell1826244864 cell1826375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1826507008 cell1826638080)
                  (ThetaLowerSegment.join cell1826769152 cell1826900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1827031296 cell1827162368)
                  (ThetaLowerSegment.join cell1827293440 cell1827424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1827555584 cell1827686656)
                  (ThetaLowerSegment.join cell1827817728 cell1827948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1828079872 cell1828210944)
                  (ThetaLowerSegment.join cell1828342016 cell1828473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1828604160 cell1828735232)
                  (ThetaLowerSegment.join cell1828866304 cell1828997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1829128448 cell1829259520)
                  (ThetaLowerSegment.join cell1829390592 cell1829521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1829652736 cell1829783808)
                  (ThetaLowerSegment.join cell1829914880 cell1830045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1830177024 cell1830308096)
                  (ThetaLowerSegment.join cell1830439168 cell1830570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1830701312 cell1830832384)
                  (ThetaLowerSegment.join cell1830963456 cell1831094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1831225600 cell1831356672)
                  (ThetaLowerSegment.join cell1831487744 cell1831618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1831749888 cell1831880960)
                  (ThetaLowerSegment.join cell1832012032 cell1832143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1832274176 cell1832405248)
                  (ThetaLowerSegment.join cell1832536320 cell1832667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1832798464 cell1832929536)
                (ThetaLowerSegment.join cell1833060608 cell1833191680))
              (ThetaLowerSegment.join cell1833322752 cell1833339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
